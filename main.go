package main

import (
	"crypto/aes"
	"crypto/cipher"
	"crypto/ecdh"
	"crypto/hmac"
	"crypto/md5"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"time"

	"github.com/mappu/miqt/qt6"
	"github.com/mappu/miqt/qt6/webengine"
)

// Borrows Firefox for Android's public OAuth client id, unlike Firefox
// Desktop's client which only works inside browser chrome.
//
// This client's registered redirect_uri used to be a real hosted page at
// lockbox.firefox.com that kept the auth code visible in the address bar.
// Mozilla discontinued the Lockwise app in Dec 2021 and that page now 301s
// straight to a marketing page, dropping the ?code=/&state= query string in
// the process - and since the redirect_uri is baked into this client id's
// registration, we can't just point it somewhere we control.
//
// So doLogin() opens the auth page in an embedded, off-the-record
// QWebEngineView (Qt6 WebEngine, via the miqt bindings) with a URL request
// interceptor watching for redirectHost. When that request is about to go
// out, we block it before it ever hits the network, read the code/state off
// its URL, and quit the Qt event loop - no fake TLS cert, no browser
// warning, no external browser process at all.
const (
	clientID       = "e7ce535d93522896"
	scope          = "https://identity.mozilla.com/apps/oldsync"
	authURL        = "https://accounts.firefox.com/authorization"
	tokenURL       = "https://oauth.accounts.firefox.com/v1/token"
	tokenServerURL = "https://token.services.mozilla.com/1.0/sync/1.5"
	redirectHost   = "lockbox.firefox.com"
)

type credentials struct {
	RefreshToken string `json:"refresh_token"`
	KeyID        string `json:"key_id"`
	SyncKey      string `json:"sync_key_b64"` // base64url of the 64-byte oldsync scoped key
}

func credentialsPath() string {
	home, _ := os.UserHomeDir()
	return filepath.Join(home, ".config", "mozsync", "credentials.json")
}

func main() {
	usage := "usage: mozsync <login|dump|chrome-import <path>|falkon-import <path>>"
	if len(os.Args) < 2 {
		fmt.Fprintln(os.Stderr, usage)
		os.Exit(1)
	}
	var err error
	switch os.Args[1] {
	case "login":
		err = doLogin()
	case "dump":
		err = doDump()
	case "chrome-import":
		if len(os.Args) < 3 {
			fmt.Fprintln(os.Stderr, usage)
			os.Exit(1)
		}
		err = doChromeImport(os.Args[2])
	case "falkon-import":
		if len(os.Args) < 3 {
			fmt.Fprintln(os.Stderr, usage)
			os.Exit(1)
		}
		err = doFalkonImport(os.Args[2])
	default:
		fmt.Fprintln(os.Stderr, usage)
		os.Exit(1)
	}
	if err != nil {
		fmt.Fprintln(os.Stderr, "error:", err)
		os.Exit(1)
	}
}

// ---------- login (one-time browser-based OAuth setup) ----------

func doLogin() error {
	verifier := randB64URL(32)
	challenge := b64url(sha256sum([]byte(verifier)))
	state := randB64URL(16)

	priv, err := ecdh.P256().GenerateKey(rand.Reader)
	if err != nil {
		return err
	}
	pub := priv.PublicKey().Bytes() // uncompressed point: 0x04 || X(32) || Y(32)
	x, y := pub[1:33], pub[33:65]
	jwk := map[string]string{"crv": "P-256", "kty": "EC", "x": b64url(x), "y": b64url(y)}
	jwkJSON, err := json.Marshal(jwk)
	if err != nil {
		return err
	}

	q := url.Values{}
	q.Set("client_id", clientID)
	q.Set("scope", scope)
	q.Set("state", state)
	q.Set("access_type", "offline")
	q.Set("code_challenge_method", "S256")
	q.Set("code_challenge", challenge)
	q.Set("keys_jwk", b64url(jwkJSON))
	q.Set("response_type", "code")
	fullAuthURL := authURL + "?" + q.Encode()

	code, gotState, err := runLoginWindow(fullAuthURL)
	if err != nil {
		return err
	}
	if code == "" {
		return fmt.Errorf("login window closed before signing in")
	}
	if gotState != state {
		return fmt.Errorf("state mismatch (got %q, want %q) - aborting", gotState, state)
	}

	var tokenResp struct {
		AccessToken  string `json:"access_token"`
		RefreshToken string `json:"refresh_token"`
		KeysJWE      string `json:"keys_jwe"`
	}
	err = postJSON(tokenURL, map[string]string{
		"client_id":     clientID,
		"grant_type":    "authorization_code",
		"code":          code,
		"code_verifier": verifier,
	}, &tokenResp)
	if err != nil {
		return fmt.Errorf("token exchange failed: %w", err)
	}
	if tokenResp.KeysJWE == "" {
		return fmt.Errorf("no keys_jwe in token response")
	}

	kid, kBytes, err := decryptKeysJWE(tokenResp.KeysJWE, priv)
	if err != nil {
		return fmt.Errorf("decrypting keys_jwe: %w", err)
	}

	creds := credentials{RefreshToken: tokenResp.RefreshToken, KeyID: kid, SyncKey: b64url(kBytes)}
	if err := saveCredentials(creds); err != nil {
		return err
	}
	fmt.Println()
	fmt.Println("Saved credentials to", credentialsPath())
	fmt.Println("This file grants ongoing access to your Mozilla account's sync data - keep it private (mode 0600).")
	fmt.Println("Run `mozsync dump` to fetch your bookmarks.")
	return nil
}

// ---------- embedded login window ----------
//
// runLoginWindow opens fullAuthURL in an off-the-record QWebEngineView and
// watches every outgoing request with a QWebEngineUrlRequestInterceptor.
// When one targets redirectHost, we block it (so it never actually hits
// Mozilla's broken redirect endpoint) and read code/state straight off its
// URL. Interception runs on Chromium's IO thread, not the Qt GUI thread, so
// the interceptor callback only ever touches a mutex-guarded plain Go value
// - a QTimer polling on the GUI thread is what actually calls
// QCoreApplication_Quit() once a result shows up.
func runLoginWindow(fullAuthURL string) (code, state string, err error) {
	app := qt6.NewQApplication(os.Args)
	defer app.Delete()

	var (
		mu     sync.Mutex
		result *struct{ code, state string }
	)

	profile := webengine.NewQWebEngineProfile() // no name -> off-the-record, nothing persisted
	interceptor := webengine.NewQWebEngineUrlRequestInterceptor()
	interceptor.OnInterceptRequest(func(info *webengine.QWebEngineUrlRequestInfo) {
		u := info.RequestUrl()
		if u.Host() != redirectHost {
			return
		}
		info.Block(true)
		vals, _ := url.ParseQuery(u.Query())
		mu.Lock()
		if result == nil {
			result = &struct{ code, state string }{vals.Get("code"), vals.Get("state")}
		}
		mu.Unlock()
	})
	profile.SetUrlRequestInterceptor(interceptor)

	view := webengine.NewQWebEngineView3(profile)
	view.SetWindowTitle("Sign in to your Mozilla Account")
	view.Resize(900, 700)
	view.Load(qt6.NewQUrl3(fullAuthURL))
	view.Show()

	const timeout = 5 * time.Minute
	deadline := time.Now().Add(timeout)
	poll := qt6.NewQTimer()
	poll.OnTimeout(func() {
		mu.Lock()
		r := result
		mu.Unlock()
		if r != nil || time.Now().After(deadline) {
			qt6.QCoreApplication_Quit()
		}
	})
	poll.Start(150)

	qt6.QCoreApplication_Exec() // blocks until Quit(); also returns if the user closes the window

	mu.Lock()
	defer mu.Unlock()
	if result == nil {
		return "", "", nil // window closed / timed out without a captured redirect
	}
	return result.code, result.state, nil
}

func saveCredentials(c credentials) error {
	path := credentialsPath()
	if err := os.MkdirAll(filepath.Dir(path), 0o700); err != nil {
		return err
	}
	data, err := json.MarshalIndent(c, "", "  ")
	if err != nil {
		return err
	}
	return os.WriteFile(path, data, 0o600)
}

func loadCredentials() (credentials, error) {
	var c credentials
	data, err := os.ReadFile(credentialsPath())
	if err != nil {
		return c, err
	}
	err = json.Unmarshal(data, &c)
	return c, err
}

// ---------- JWE (ECDH-ES + A256GCM), per RFC 7518 4.6 ----------

func decryptKeysJWE(jwe string, priv *ecdh.PrivateKey) (kid string, key []byte, err error) {
	parts := strings.Split(jwe, ".")
	if len(parts) != 5 {
		return "", nil, fmt.Errorf("malformed JWE: expected 5 segments, got %d", len(parts))
	}
	headerB64, ivB64, ctB64, tagB64 := parts[0], parts[2], parts[3], parts[4]

	headerRaw, err := base64.RawURLEncoding.DecodeString(headerB64)
	if err != nil {
		return "", nil, err
	}
	var header struct {
		Enc string `json:"enc"`
		Alg string `json:"alg"`
		EPK struct {
			X string `json:"x"`
			Y string `json:"y"`
		} `json:"epk"`
	}
	if err := json.Unmarshal(headerRaw, &header); err != nil {
		return "", nil, err
	}
	if header.Alg != "ECDH-ES" || header.Enc != "A256GCM" {
		return "", nil, fmt.Errorf("unexpected JWE alg/enc: %s/%s", header.Alg, header.Enc)
	}

	epkX, err := base64.RawURLEncoding.DecodeString(header.EPK.X)
	if err != nil {
		return "", nil, err
	}
	epkY, err := base64.RawURLEncoding.DecodeString(header.EPK.Y)
	if err != nil {
		return "", nil, err
	}
	epkBytes := append([]byte{0x04}, append(epkX, epkY...)...)
	serverPub, err := ecdh.P256().NewPublicKey(epkBytes)
	if err != nil {
		return "", nil, err
	}
	shared, err := priv.ECDH(serverPub)
	if err != nil {
		return "", nil, err
	}

	cek := concatKDF(shared, header.Enc, 32) // A256GCM -> 256-bit CEK

	iv, err := base64.RawURLEncoding.DecodeString(ivB64)
	if err != nil {
		return "", nil, err
	}
	ciphertext, err := base64.RawURLEncoding.DecodeString(ctB64)
	if err != nil {
		return "", nil, err
	}
	tag, err := base64.RawURLEncoding.DecodeString(tagB64)
	if err != nil {
		return "", nil, err
	}

	block, err := aes.NewCipher(cek)
	if err != nil {
		return "", nil, err
	}
	gcm, err := cipher.NewGCM(block)
	if err != nil {
		return "", nil, err
	}
	aad := []byte(headerB64) // JWE AAD is the raw base64url header segment itself
	plaintext, err := gcm.Open(nil, iv, append(ciphertext, tag...), aad)
	if err != nil {
		return "", nil, fmt.Errorf("GCM open failed: %w", err)
	}

	var scoped map[string]struct {
		K   string `json:"k"`
		Kid string `json:"kid"`
	}
	if err := json.Unmarshal(plaintext, &scoped); err != nil {
		return "", nil, err
	}
	sk, ok := scoped[scope]
	if !ok {
		return "", nil, fmt.Errorf("no scoped key for %s in keys_jwe payload", scope)
	}
	kBytes, err := base64.RawURLEncoding.DecodeString(sk.K)
	if err != nil {
		return "", nil, err
	}
	return sk.Kid, kBytes, nil
}

// concatKDF is the single-round NIST SP 800-56A Concat KDF used by JWE ECDH-ES
// direct agreement, with empty PartyUInfo/PartyVInfo (no apu/apv exchanged here).
func concatKDF(z []byte, algID string, keyLenBytes int) []byte {
	algIDBytes := []byte(algID)
	otherInfo := appendUint32(nil, uint32(len(algIDBytes)))
	otherInfo = append(otherInfo, algIDBytes...)
	otherInfo = appendUint32(otherInfo, 0) // PartyUInfo length (empty)
	otherInfo = appendUint32(otherInfo, 0) // PartyVInfo length (empty)
	otherInfo = appendUint32(otherInfo, uint32(keyLenBytes*8))

	h := sha256.New()
	h.Write(appendUint32(nil, 1)) // round counter; one round covers 256 bits
	h.Write(z)
	h.Write(otherInfo)
	sum := h.Sum(nil)
	return sum[:keyLenBytes]
}

func appendUint32(b []byte, v uint32) []byte {
	return append(b, byte(v>>24), byte(v>>16), byte(v>>8), byte(v))
}

// ---------- Sync 1.5 storage records ----------

type syncKeyBundle struct {
	EncKey  []byte
	HMACKey []byte
}

func decryptBSOPayload(payloadJSON string, bundle syncKeyBundle) ([]byte, error) {
	var payload struct {
		Ciphertext string `json:"ciphertext"`
		IV         string `json:"IV"`
		HMAC       string `json:"hmac"`
	}
	if err := json.Unmarshal([]byte(payloadJSON), &payload); err != nil {
		return nil, err
	}
	mac := hmac.New(sha256.New, bundle.HMACKey)
	mac.Write([]byte(payload.Ciphertext)) // HMAC covers the base64 ciphertext string itself
	if hex.EncodeToString(mac.Sum(nil)) != payload.HMAC {
		return nil, fmt.Errorf("HMAC verification failed")
	}
	iv, err := base64.StdEncoding.DecodeString(payload.IV)
	if err != nil {
		return nil, err
	}
	ct, err := base64.StdEncoding.DecodeString(payload.Ciphertext)
	if err != nil {
		return nil, err
	}
	if len(ct)%aes.BlockSize != 0 {
		return nil, fmt.Errorf("ciphertext not a multiple of block size")
	}
	block, err := aes.NewCipher(bundle.EncKey)
	if err != nil {
		return nil, err
	}
	out := make([]byte, len(ct))
	cipher.NewCBCDecrypter(block, iv).CryptBlocks(out, ct)
	return pkcs7Unpad(out)
}

func pkcs7Unpad(b []byte) ([]byte, error) {
	if len(b) == 0 {
		return nil, fmt.Errorf("empty plaintext")
	}
	pad := int(b[len(b)-1])
	if pad == 0 || pad > len(b) {
		return nil, fmt.Errorf("invalid padding")
	}
	return b[:len(b)-pad], nil
}

func doDump() error {
	creds, err := loadCredentials()
	if err != nil {
		return fmt.Errorf("no credentials found, run `mozsync login` first: %w", err)
	}
	masterKey, err := base64.RawURLEncoding.DecodeString(creds.SyncKey)
	if err != nil || len(masterKey) != 64 {
		return fmt.Errorf("stored sync key is invalid, re-run `mozsync login`")
	}
	masterBundle := syncKeyBundle{EncKey: masterKey[:32], HMACKey: masterKey[32:64]}

	accessToken, err := refreshAccessToken(creds.RefreshToken)
	if err != nil {
		return fmt.Errorf("refreshing access token: %w", err)
	}
	hawkID, hawkKey, apiEndpoint, err := getStorageCredentials(accessToken, creds.KeyID)
	if err != nil {
		return fmt.Errorf("fetching storage credentials: %w", err)
	}

	keysPayload, err := storageGET(apiEndpoint, "/storage/crypto/keys", hawkID, hawkKey)
	if err != nil {
		return fmt.Errorf("fetching crypto/keys: %w", err)
	}
	var keysBSO struct {
		Payload string `json:"payload"`
	}
	if err := json.Unmarshal(keysPayload, &keysBSO); err != nil {
		return err
	}
	plain, err := decryptBSOPayload(keysBSO.Payload, masterBundle)
	if err != nil {
		return fmt.Errorf("decrypting crypto/keys: %w", err)
	}
	var keysRecord struct {
		Default     []string            `json:"default"`
		Collections map[string][]string `json:"collections"`
	}
	if err := json.Unmarshal(plain, &keysRecord); err != nil {
		return err
	}
	bundleFor := func(collection string) (syncKeyBundle, error) {
		pair := keysRecord.Default
		if override, ok := keysRecord.Collections[collection]; ok {
			pair = override
		}
		if len(pair) != 2 {
			return syncKeyBundle{}, fmt.Errorf("no usable key bundle for collection %s", collection)
		}
		enc, err := base64.StdEncoding.DecodeString(pair[0])
		if err != nil {
			return syncKeyBundle{}, err
		}
		h, err := base64.StdEncoding.DecodeString(pair[1])
		if err != nil {
			return syncKeyBundle{}, err
		}
		return syncKeyBundle{EncKey: enc, HMACKey: h}, nil
	}
	bmBundle, err := bundleFor("bookmarks")
	if err != nil {
		return err
	}

	bmRaw, err := storageGET(apiEndpoint, "/storage/bookmarks?full=true", hawkID, hawkKey)
	if err != nil {
		return fmt.Errorf("fetching bookmarks: %w", err)
	}
	var bsos []struct {
		ID      string `json:"id"`
		Payload string `json:"payload"`
	}
	if err := json.Unmarshal(bmRaw, &bsos); err != nil {
		return err
	}

	var records []json.RawMessage
	for _, bso := range bsos {
		plain, err := decryptBSOPayload(bso.Payload, bmBundle)
		if err != nil {
			fmt.Fprintf(os.Stderr, "warning: skipping record %s: %v\n", bso.ID, err)
			continue
		}
		records = append(records, json.RawMessage(plain))
	}

	out, err := json.MarshalIndent(records, "", "  ")
	if err != nil {
		return err
	}
	fmt.Println(string(out))
	return nil
}

// ---------- chrome-import: merge a `mozsync dump` into a Chromium profile's Bookmarks file ----------
//
// Reads the flat dump array (Firefox Places Sync records) from stdin, and for
// each of Firefox's special roots that has children (toolbar, menu, unfiled,
// mobile), builds one labeled wrapper folder holding the full imported
// subtree and appends it into the corresponding Chromium root - bookmark_bar
// for toolbar, other for menu/unfiled, synced for mobile. Existing bookmarks
// are never touched or removed, only appended to, and the previous file is
// always backed up first. The Chromium file is read/written as a generic
// map[string]interface{} rather than a fixed struct so fields Chromium itself
// relies on (like a bookmark's meta_info) survive the round-trip untouched.

type ffRecord struct {
	ID        string   `json:"id"`
	Type      string   `json:"type"`
	Title     string   `json:"title"`
	BmkURI    string   `json:"bmkUri"`
	DateAdded int64    `json:"dateAdded"`
	Children  []string `json:"children"`
	Deleted   bool     `json:"deleted"`
}

func doChromeImport(path string) error {
	dumpBytes, err := io.ReadAll(os.Stdin)
	if err != nil {
		return fmt.Errorf("reading dump from stdin: %w", err)
	}
	var records []ffRecord
	if err := json.Unmarshal(dumpBytes, &records); err != nil {
		return fmt.Errorf("parsing dump JSON: %w", err)
	}
	byID := make(map[string]ffRecord, len(records))
	for _, r := range records {
		if !r.Deleted {
			byID[r.ID] = r
		}
	}

	if chromiumRunning() {
		fmt.Fprintln(os.Stderr, "warning: Chromium appears to be running - it may overwrite this import on its")
		fmt.Fprintln(os.Stderr, "         next save. Fully quit Chromium and re-run this if the import doesn't stick.")
	}

	existing, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("reading %s: %w", path, err)
	}
	var cf map[string]interface{}
	if err := json.Unmarshal(existing, &cf); err != nil {
		return fmt.Errorf("parsing existing Chromium bookmarks file: %w", err)
	}
	roots, ok := cf["roots"].(map[string]interface{})
	if !ok {
		return fmt.Errorf("existing Chromium bookmarks file has no \"roots\" object")
	}
	bar, ok1 := roots["bookmark_bar"].(map[string]interface{})
	other, ok2 := roots["other"].(map[string]interface{})
	synced, ok3 := roots["synced"].(map[string]interface{})
	if !ok1 || !ok2 || !ok3 {
		return fmt.Errorf("existing Chromium bookmarks file is missing an expected root")
	}

	backupPath := path + ".mozsync-bak"
	if err := os.WriteFile(backupPath, existing, 0o600); err != nil {
		return fmt.Errorf("backing up existing bookmarks file: %w", err)
	}

	nextID := maxChromeID(roots) + 1

	// Merge directly into each root's top level, matching existing items by
	// (name, type): an existing bookmark's url is overwritten, an existing
	// folder is recursed into and merged, and only genuinely new items are
	// appended. No wrapper folder, and re-running this is idempotent instead
	// of piling up a fresh dated folder each time.
	mergeRoot := func(target map[string]interface{}, ffRootID string) {
		root, ok := byID[ffRootID]
		if !ok {
			return
		}
		existingKids, _ := target["children"].([]interface{})
		target["children"] = mergeChromeChildren(existingKids, byID, root.Children, &nextID)
	}
	mergeRoot(bar, "toolbar")
	mergeRoot(other, "menu")
	mergeRoot(other, "unfiled")
	mergeRoot(synced, "mobile")

	cf["checksum"] = computeChromeChecksum(bar, other, synced)

	out, err := json.MarshalIndent(cf, "", "   ")
	if err != nil {
		return err
	}
	tmpPath := path + ".mozsync-tmp"
	if err := os.WriteFile(tmpPath, out, 0o600); err != nil {
		return err
	}
	if err := os.Rename(tmpPath, path); err != nil {
		return err
	}

	fmt.Println("Imported into", path)
	fmt.Println("Backup of the previous file saved to", backupPath)
	fmt.Println("Fully quit and relaunch Chromium to see the merged bookmarks.")
	return nil
}

// mergeChromeChildren upserts each Firefox child (by title+type match) into
// an existing Chromium children array: url nodes get their url overwritten,
// folder nodes are recursed into, and anything with no match is appended as
// a freshly built subtree.
func mergeChromeChildren(existing []interface{}, byID map[string]ffRecord, ffChildIDs []string, nextID *int) []interface{} {
	for _, childID := range ffChildIDs {
		r, ok := byID[childID]
		if !ok {
			continue
		}
		switch r.Type {
		case "bookmark":
			if r.BmkURI == "" {
				continue
			}
			existing = upsertChromeURL(existing, r, nextID)
		case "folder":
			existing = upsertChromeFolder(existing, r, byID, nextID)
		}
	}
	return existing
}

func upsertChromeURL(existing []interface{}, r ffRecord, nextID *int) []interface{} {
	for _, e := range existing {
		m, ok := e.(map[string]interface{})
		if !ok {
			continue
		}
		name, _ := m["name"].(string)
		t, _ := m["type"].(string)
		if name == r.Title && t == "url" {
			m["url"] = r.BmkURI
			return existing
		}
	}
	n := map[string]interface{}{
		"id": strconv.Itoa(*nextID), "guid": newGUID(), "name": r.Title, "type": "url",
		"url": r.BmkURI, "date_added": chromeTimestamp(r.DateAdded), "date_last_used": "0", "date_modified": "0",
	}
	(*nextID)++
	return append(existing, n)
}

func upsertChromeFolder(existing []interface{}, r ffRecord, byID map[string]ffRecord, nextID *int) []interface{} {
	for _, e := range existing {
		m, ok := e.(map[string]interface{})
		if !ok {
			continue
		}
		name, _ := m["name"].(string)
		t, _ := m["type"].(string)
		if name == r.Title && t == "folder" {
			kids, _ := m["children"].([]interface{})
			m["children"] = mergeChromeChildren(kids, byID, r.Children, nextID)
			return existing
		}
	}
	if n := buildChromeNode(byID, r.ID, nextID); n != nil {
		existing = append(existing, n)
	}
	return existing
}

func buildChromeNode(byID map[string]ffRecord, id string, nextID *int) map[string]interface{} {
	r, ok := byID[id]
	if !ok {
		return nil
	}
	switch r.Type {
	case "bookmark":
		if r.BmkURI == "" {
			return nil
		}
		n := map[string]interface{}{
			"id": strconv.Itoa(*nextID), "guid": newGUID(), "name": r.Title, "type": "url",
			"url": r.BmkURI, "date_added": chromeTimestamp(r.DateAdded), "date_last_used": "0", "date_modified": "0",
		}
		(*nextID)++
		return n
	case "folder":
		myID := strconv.Itoa(*nextID)
		(*nextID)++
		var kids []interface{}
		for _, childID := range r.Children {
			if child := buildChromeNode(byID, childID, nextID); child != nil {
				kids = append(kids, child)
			}
		}
		n := map[string]interface{}{
			"id": myID, "guid": newGUID(), "name": r.Title, "type": "folder",
			"date_added": chromeTimestamp(r.DateAdded), "date_last_used": "0", "date_modified": "0",
		}
		if kids != nil {
			n["children"] = kids
		}
		return n
	default:
		return nil // skip queries, separators, livemarks, etc.
	}
}

func maxChromeID(roots map[string]interface{}) int {
	max := 0
	var walk func(n interface{})
	walk = func(n interface{}) {
		m, ok := n.(map[string]interface{})
		if !ok {
			return
		}
		if idStr, ok := m["id"].(string); ok {
			if v, err := strconv.Atoi(idStr); err == nil && v > max {
				max = v
			}
		}
		if kids, ok := m["children"].([]interface{}); ok {
			for _, k := range kids {
				walk(k)
			}
		}
	}
	for _, v := range roots {
		walk(v)
	}
	return max
}

// computeChromeChecksum reproduces Chromium's BookmarkCodec checksum: an MD5
// over (id, name[, url if a url node]) for every node, visited pre-order,
// across bookmark_bar/other/synced in that order. Best-effort - if a given
// Chromium version's algorithm has drifted, worst case is a one-time "your
// bookmarks were changed outside Chrome" notice on next launch; the data
// itself is unaffected either way.
func computeChromeChecksum(roots ...map[string]interface{}) string {
	h := md5.New()
	var walk func(n map[string]interface{})
	walk = func(n map[string]interface{}) {
		if n == nil {
			return
		}
		if idStr, ok := n["id"].(string); ok {
			io.WriteString(h, idStr)
		}
		if name, ok := n["name"].(string); ok {
			io.WriteString(h, name)
		}
		if t, _ := n["type"].(string); t == "url" {
			if u, ok := n["url"].(string); ok {
				io.WriteString(h, u)
			}
		}
		if kids, ok := n["children"].([]interface{}); ok {
			for _, k := range kids {
				if km, ok := k.(map[string]interface{}); ok {
					walk(km)
				}
			}
		}
	}
	for _, r := range roots {
		walk(r)
	}
	return hex.EncodeToString(h.Sum(nil))
}

// chromeEpochDeltaMicros is the offset between the Unix epoch (1970-01-01)
// and the Windows/WebKit epoch (1601-01-01) that Chromium's bookmark
// timestamps are measured from, in microseconds.
const chromeEpochDeltaMicros = 11644473600000000

func chromeTimestamp(unixMs int64) string {
	return strconv.FormatInt(unixMs*1000+chromeEpochDeltaMicros, 10)
}

func newGUID() string {
	b := make([]byte, 16)
	_, _ = rand.Read(b)
	b[6] = (b[6] & 0x0f) | 0x40
	b[8] = (b[8] & 0x3f) | 0x80
	return fmt.Sprintf("%x-%x-%x-%x-%x", b[0:4], b[4:6], b[6:8], b[8:10], b[10:16])
}

func chromiumRunning() bool {
	out, err := exec.Command("pgrep", "-f", "org.chromium.Chromium").Output()
	return err == nil && len(strings.TrimSpace(string(out))) > 0
}

// ---------- falkon-import: merge a `mozsync dump` into Falkon's bookmarks.json ----------
//
// Falkon (unlike Chromium) stores bookmarks as plain JSON with no ids,
// checksum, or timestamp bookkeeping - just nested folders under three roots:
// bookmark_bar, bookmark_menu, other. Same safe-append/backup approach as
// chrome-import: existing bookmarks are never touched, only appended to.

func doFalkonImport(path string) error {
	dumpBytes, err := io.ReadAll(os.Stdin)
	if err != nil {
		return fmt.Errorf("reading dump from stdin: %w", err)
	}
	var records []ffRecord
	if err := json.Unmarshal(dumpBytes, &records); err != nil {
		return fmt.Errorf("parsing dump JSON: %w", err)
	}
	byID := make(map[string]ffRecord, len(records))
	for _, r := range records {
		if !r.Deleted {
			byID[r.ID] = r
		}
	}

	if falkonRunning() {
		fmt.Fprintln(os.Stderr, "warning: Falkon appears to be running - it may overwrite this import on its")
		fmt.Fprintln(os.Stderr, "         next save. Fully quit Falkon and re-run this if the import doesn't stick.")
	}

	existing, err := os.ReadFile(path)
	if err != nil {
		return fmt.Errorf("reading %s: %w", path, err)
	}
	var bf map[string]interface{}
	if err := json.Unmarshal(existing, &bf); err != nil {
		return fmt.Errorf("parsing existing Falkon bookmarks file: %w", err)
	}
	roots, ok := bf["roots"].(map[string]interface{})
	if !ok {
		return fmt.Errorf("existing Falkon bookmarks file has no \"roots\" object")
	}
	bar, ok1 := roots["bookmark_bar"].(map[string]interface{})
	menu, ok2 := roots["bookmark_menu"].(map[string]interface{})
	other, ok3 := roots["other"].(map[string]interface{})
	if !ok1 || !ok2 || !ok3 {
		return fmt.Errorf("existing Falkon bookmarks file is missing an expected root")
	}

	backupPath := path + ".mozsync-bak"
	if err := os.WriteFile(backupPath, existing, 0o600); err != nil {
		return fmt.Errorf("backing up existing bookmarks file: %w", err)
	}

	// Merge directly into each root's top level, matching existing items by
	// (name, type): an existing bookmark's url is overwritten, an existing
	// folder is recursed into and merged, and only genuinely new items are
	// appended. No wrapper folder, and re-running this is idempotent instead
	// of piling up a fresh dated folder each time.
	mergeRoot := func(target map[string]interface{}, ffRootID string) {
		root, ok := byID[ffRootID]
		if !ok {
			return
		}
		existingKids, _ := target["children"].([]interface{})
		target["children"] = mergeFalkonChildren(existingKids, byID, root.Children)
	}
	mergeRoot(bar, "toolbar")
	mergeRoot(menu, "menu")
	mergeRoot(other, "unfiled")
	mergeRoot(other, "mobile")

	out, err := json.MarshalIndent(bf, "", " ")
	if err != nil {
		return err
	}
	tmpPath := path + ".mozsync-tmp"
	if err := os.WriteFile(tmpPath, out, 0o600); err != nil {
		return err
	}
	if err := os.Rename(tmpPath, path); err != nil {
		return err
	}

	fmt.Println("Imported into", path)
	fmt.Println("Backup of the previous file saved to", backupPath)
	fmt.Println("Fully quit and relaunch Falkon to see the merged bookmarks.")
	return nil
}

// mergeFalkonChildren upserts each Firefox child (by title+type match) into
// an existing Falkon children array: url nodes get their url overwritten,
// folder nodes are recursed into, and anything with no match is appended as
// a freshly built subtree.
func mergeFalkonChildren(existing []interface{}, byID map[string]ffRecord, ffChildIDs []string) []interface{} {
	for _, childID := range ffChildIDs {
		r, ok := byID[childID]
		if !ok {
			continue
		}
		switch r.Type {
		case "bookmark":
			if r.BmkURI == "" {
				continue
			}
			existing = upsertFalkonURL(existing, r)
		case "folder":
			existing = upsertFalkonFolder(existing, r, byID)
		}
	}
	return existing
}

func upsertFalkonURL(existing []interface{}, r ffRecord) []interface{} {
	for _, e := range existing {
		m, ok := e.(map[string]interface{})
		if !ok {
			continue
		}
		name, _ := m["name"].(string)
		t, _ := m["type"].(string)
		if name == r.Title && t == "url" {
			m["url"] = r.BmkURI
			return existing
		}
	}
	n := map[string]interface{}{
		"description": "", "keyword": "", "name": r.Title, "type": "url", "url": r.BmkURI, "visit_count": 0,
	}
	return append(existing, n)
}

func upsertFalkonFolder(existing []interface{}, r ffRecord, byID map[string]ffRecord) []interface{} {
	for _, e := range existing {
		m, ok := e.(map[string]interface{})
		if !ok {
			continue
		}
		name, _ := m["name"].(string)
		t, _ := m["type"].(string)
		if name == r.Title && t == "folder" {
			kids, _ := m["children"].([]interface{})
			m["children"] = mergeFalkonChildren(kids, byID, r.Children)
			return existing
		}
	}
	if n := buildFalkonNode(byID, r.ID); n != nil {
		existing = append(existing, n)
	}
	return existing
}

func buildFalkonNode(byID map[string]ffRecord, id string) map[string]interface{} {
	r, ok := byID[id]
	if !ok {
		return nil
	}
	switch r.Type {
	case "bookmark":
		if r.BmkURI == "" {
			return nil
		}
		return map[string]interface{}{
			"description": "", "keyword": "", "name": r.Title, "type": "url",
			"url": r.BmkURI, "visit_count": 0,
		}
	case "folder":
		var kids []interface{}
		for _, childID := range r.Children {
			if child := buildFalkonNode(byID, childID); child != nil {
				kids = append(kids, child)
			}
		}
		if kids == nil {
			kids = []interface{}{}
		}
		return map[string]interface{}{
			"children": kids, "description": "", "expanded": true, "expanded_sidebar": true,
			"name": r.Title, "type": "folder",
		}
	default:
		return nil // skip queries, separators, livemarks, etc.
	}
}

func falkonRunning() bool {
	out, err := exec.Command("pgrep", "-f", "org.kde.falkon").Output()
	return err == nil && len(strings.TrimSpace(string(out))) > 0
}

func refreshAccessToken(refreshToken string) (string, error) {
	var resp struct {
		AccessToken string `json:"access_token"`
	}
	err := postJSON(tokenURL, map[string]string{
		"client_id":     clientID,
		"grant_type":    "refresh_token",
		"refresh_token": refreshToken,
		"scope":         scope,
	}, &resp)
	if err != nil {
		return "", err
	}
	if resp.AccessToken == "" {
		return "", fmt.Errorf("empty access token in refresh response")
	}
	return resp.AccessToken, nil
}

func getStorageCredentials(accessToken, keyID string) (id, key, apiEndpoint string, err error) {
	req, err := http.NewRequest("GET", tokenServerURL, nil)
	if err != nil {
		return "", "", "", err
	}
	req.Header.Set("Authorization", "Bearer "+accessToken)
	req.Header.Set("X-KeyID", keyID)
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return "", "", "", err
	}
	defer resp.Body.Close()
	body, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != 200 {
		return "", "", "", fmt.Errorf("tokenserver returned %d: %s", resp.StatusCode, body)
	}
	var ts struct {
		ID          string `json:"id"`
		Key         string `json:"key"`
		APIEndpoint string `json:"api_endpoint"`
	}
	if err := json.Unmarshal(body, &ts); err != nil {
		return "", "", "", err
	}
	return ts.ID, ts.Key, ts.APIEndpoint, nil
}

func storageGET(apiEndpoint, path, hawkID, hawkKey string) ([]byte, error) {
	fullURL := apiEndpoint + path
	req, err := http.NewRequest("GET", fullURL, nil)
	if err != nil {
		return nil, err
	}
	req.Header.Set("Authorization", hawkHeader("GET", fullURL, hawkID, hawkKey))
	resp, err := http.DefaultClient.Do(req)
	if err != nil {
		return nil, err
	}
	defer resp.Body.Close()
	body, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != 200 {
		return nil, fmt.Errorf("storage server returned %d: %s", resp.StatusCode, body)
	}
	return body, nil
}

// ---------- Hawk request signing ----------

func hawkHeader(method, rawURL, id, key string) string {
	u, _ := url.Parse(rawURL)
	ts := time.Now().Unix()
	nonce := randB64URL(6)
	resource := u.Path
	if u.RawQuery != "" {
		resource += "?" + u.RawQuery
	}
	port := u.Port()
	if port == "" {
		port = "443"
	}
	normalized := fmt.Sprintf("hawk.1.header\n%d\n%s\n%s\n%s\n%s\n%s\n\n\n",
		ts, nonce, method, resource, u.Hostname(), port)
	mac := hmac.New(sha256.New, []byte(key))
	mac.Write([]byte(normalized))
	macB64 := base64.StdEncoding.EncodeToString(mac.Sum(nil))
	return fmt.Sprintf(`Hawk id="%s", ts="%d", nonce="%s", mac="%s"`, id, ts, nonce, macB64)
}

// ---------- small helpers ----------

func postJSON(u string, body interface{}, out interface{}) error {
	data, err := json.Marshal(body)
	if err != nil {
		return err
	}
	resp, err := http.Post(u, "application/json", strings.NewReader(string(data)))
	if err != nil {
		return err
	}
	defer resp.Body.Close()
	respBody, _ := io.ReadAll(resp.Body)
	if resp.StatusCode != 200 {
		return fmt.Errorf("HTTP %d: %s", resp.StatusCode, respBody)
	}
	return json.Unmarshal(respBody, out)
}

func randB64URL(n int) string {
	b := make([]byte, n)
	_, _ = rand.Read(b)
	return b64url(b)
}

func b64url(b []byte) string {
	return base64.RawURLEncoding.EncodeToString(b)
}

func sha256sum(b []byte) []byte {
	s := sha256.Sum256(b)
	return s[:]
}

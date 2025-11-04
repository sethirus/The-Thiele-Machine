# Threat Model for Thiele Receipt System

**Version:** 1.0  
**Date:** 2025-11-04  
**Status:** Production

---

## Executive Summary

The Thiele Receipt System provides cryptographic integrity and authenticity guarantees for software artifacts. This document defines the threat model, security boundaries, and guarantees provided by the system.

---

## 1. Assets

### 1.1 Primary Assets

1. **Software Artifacts**
   - Binary executables
   - Source code files
   - Configuration files
   - Documentation

2. **Receipts (TRS-1.0 Format)**
   - File metadata (paths, sizes, hashes)
   - Global digest (integrity hash)
   - Optional Ed25519 signatures
   - Optional metadata (version, author, etc.)

3. **Cryptographic Keys**
   - Ed25519 private signing keys (32 bytes)
   - Ed25519 public verification keys (32 bytes)

4. **User Trust**
   - Confidence in software integrity
   - Confidence in software provenance

### 1.2 Secondary Assets

1. **Web Interface**
   - Browser-based receipt generator
   - Browser-based receipt verifier
   - Badge and QR code generators

2. **CLI Tools**
   - `create_receipt.py` - Receipt generator
   - `verify_trs10.py` - Receipt verifier

---

## 2. Adversaries & Threat Actors

### 2.1 Threat Actor Profiles

#### **T1: Malicious Software Distributor**
- **Goal:** Distribute tampered/malicious software as legitimate
- **Capabilities:** Can modify artifacts, create fake receipts
- **Cannot:** Obtain legitimate private signing keys

#### **T2: Man-in-the-Middle Attacker**
- **Goal:** Intercept and modify artifacts or receipts in transit
- **Capabilities:** Network interception, DNS poisoning
- **Cannot:** Break cryptographic hashes or signatures

#### **T3: Compromised Build Server**
- **Goal:** Inject malicious code during build process
- **Capabilities:** Full control of build environment
- **Cannot:** Access signing keys if properly isolated

#### **T4: Key Compromise Attacker**
- **Goal:** Sign malicious artifacts with stolen keys
- **Capabilities:** Obtained private signing key
- **Cannot:** Retroactively forge old signatures (no forward secrecy in Ed25519)

#### **T5: Supply Chain Attacker**
- **Goal:** Compromise dependencies or tools
- **Capabilities:** Insert malicious code in dependencies
- **Cannot:** Modify receipts without detection

### 2.2 Out of Scope Threats

- **Physical security** of devices storing keys
- **Social engineering** to obtain keys
- **Regulatory compliance** (GDPR, export controls, etc.)
- **Availability attacks** (DoS on verification services)
- **Side-channel attacks** on cryptographic operations

---

## 3. Security Guarantees

### 3.1 Integrity Guarantees

✅ **GUARANTEED:**

1. **Tamper Detection:** Any modification to artifact files is detected during verification
2. **Receipt Integrity:** Receipts cannot be modified without detection (via global digest)
3. **Collision Resistance:** Computationally infeasible to find two artifacts with same hash

⚠️ **NOT GUARANTEED:**

1. **Integrity of receipt itself without signature:** Receipts without signatures can be replaced entirely
2. **Time-of-check to time-of-use:** Artifact could be modified after verification

### 3.2 Authenticity Guarantees

✅ **GUARANTEED (with Ed25519 signatures):**

1. **Origin Verification:** Receipts signed by known key prove origin
2. **Non-Repudiation:** Signer cannot deny creating signed receipt
3. **Signature Validity:** Invalid signatures are detected

⚠️ **NOT GUARANTEED:**

1. **Key Ownership:** Public key alone doesn't prove identity without PKI
2. **Key Freshness:** No built-in key rotation or expiry
3. **Replay Protection:** Old signed receipts remain valid indefinitely

### 3.3 Confidentiality Guarantees

❌ **NOT PROVIDED:**

1. **Content Confidentiality:** All artifacts and receipts are assumed public
2. **Metadata Privacy:** All metadata in receipts is public
3. **Key Privacy:** Public keys are meant to be distributed

---

## 4. Attack Scenarios & Mitigations

### 4.1 Artifact Tampering

**Attack:** Adversary (T1) modifies artifact after receipt creation

**Threat Vector:**
1. User downloads legitimate artifact + receipt
2. Adversary intercepts and modifies artifact
3. User verifies with receipt

**Mitigation:**
- ✅ Verification fails immediately (hash mismatch)
- ✅ Global digest prevents selective modification of multiple files

**Status:** ✅ **MITIGATED**

### 4.2 Receipt Forgery (Unsigned)

**Attack:** Adversary (T1) creates fake receipt for malicious artifact

**Threat Vector:**
1. Adversary creates malicious artifact
2. Adversary generates valid receipt for it
3. User downloads both and verifies successfully

**Mitigation:**
- ⚠️ **Partial:** Receipt is technically valid for the malicious artifact
- ✅ **Full with signatures:** Signature verification prevents this if user checks signature

**Status:** ⚠️ **REQUIRES SIGNATURES** for full mitigation

**Recommendation:** **Always use signatures for production releases**

### 4.3 Signature Stripping

**Attack:** Adversary (T1) removes signature from receipt

**Threat Vector:**
1. User downloads signed receipt
2. Adversary strips signature field
3. User verifies without checking signature

**Mitigation:**
- ⚠️ Verifier should warn when signature is absent
- ⚠️ Users must check for `sig_scheme: ed25519`

**Status:** ⚠️ **USER RESPONSIBILITY**

**Recommendation:** Verifiers should prominently display signature status

### 4.4 Key Compromise

**Attack:** Adversary (T4) steals private signing key

**Threat Vector:**
1. Attacker obtains private key (phishing, malware, etc.)
2. Attacker signs malicious artifacts
3. Signatures verify successfully

**Mitigation:**
- ⚠️ No technical mitigation (trust chain is broken)
- ✅ **Operational:** Key rotation, revocation lists (future work)
- ✅ **Operational:** HSM or secure key storage

**Status:** ⚠️ **OPERATIONAL CONTROLS REQUIRED**

**Recommendation:**
- Use hardware security modules (HSMs) for production keys
- Implement key rotation policy
- Maintain revocation list (future enhancement)

### 4.5 Malicious Web Verifier

**Attack:** Adversary (T2) hosts fake web verifier to steal artifacts

**Threat Vector:**
1. User visits fake verifier website
2. User uploads artifact + receipt
3. Adversary captures sensitive artifacts

**Mitigation:**
- ✅ Official verifier is 100% client-side (no uploads)
- ✅ Content Security Policy (CSP) prevents injection
- ✅ Subresource Integrity (SRI) for external scripts
- ✅ Clear UI stating "Nothing uploaded to server"

**Status:** ✅ **MITIGATED**

### 4.6 Supply Chain Attack on Dependencies

**Attack:** Adversary (T5) compromises TweetNaCl.js or QRCode.js libraries

**Threat Vector:**
1. Attacker compromises CDN or library
2. Malicious code injected into verifier
3. Keys or artifacts stolen when user verifies

**Mitigation:**
- ✅ Subresource Integrity (SRI) checks on all external scripts
- ✅ CSP restricts script sources
- ⚠️ Offline verification mode (future enhancement)

**Status:** ✅ **MITIGATED** (with SRI)

### 4.7 Time-of-Check / Time-of-Use (TOCTOU)

**Attack:** Artifact modified after verification but before use

**Threat Vector:**
1. User verifies artifact (passes)
2. Artifact modified before execution
3. User executes tampered artifact

**Mitigation:**
- ⚠️ No built-in protection
- ✅ **Best Practice:** Verify immediately before use
- ✅ **Best Practice:** Immutable artifact storage

**Status:** ⚠️ **USER RESPONSIBILITY**

---

## 5. Signature Scheme Details

### 5.1 What Is Signed

**Signed Data:** The `global_digest` string (UTF-8 encoded)

**Algorithm:** Ed25519 (RFC 8032)

**Signature Format:**
```json
{
  "sig_scheme": "ed25519",
  "signature": "<128-char hex>",
  "public_key": "<64-char hex>"
}
```

**Verification Process:**
1. Extract `global_digest` from receipt
2. Encode as UTF-8 bytes
3. Verify Ed25519 signature using `public_key`
4. If valid, signature confirms receipt authenticity

### 5.2 Key Management

**Key Generation:**
```bash
# Generate Ed25519 key pair
python3 -c "from nacl.signing import SigningKey; sk = SigningKey.generate(); open('private.key', 'wb').write(bytes(sk)); open('public.key', 'wb').write(bytes(sk.verify_key))"
```

**Key Storage:**
- Private keys: Secure storage (HSM, encrypted filesystem, secrets manager)
- Public keys: Distributed with releases, documented in README

**Key Rotation:**
- Not currently automated
- Manual process: Generate new key, sign with both old and new, announce transition

---

## 6. Browser Security

### 6.1 Content Security Policy (CSP)

All web pages include strict CSP headers:

```html
<meta http-equiv="Content-Security-Policy" content="
  default-src 'none';
  script-src 'self' https://cdn.jsdelivr.net;
  style-src 'self' 'unsafe-inline';
  img-src 'self' https://img.shields.io data:;
  font-src 'self';
  connect-src 'none';
  form-action 'none';
  base-uri 'self';
  frame-ancestors 'none';">
```

**Protections:**
- ✅ No inline scripts (except for specific hashes)
- ✅ No eval() or Function()
- ✅ No external connections (all client-side)
- ✅ No form submissions to external sites

### 6.2 Subresource Integrity (SRI)

All external scripts include SRI hashes:

```html
<script src="https://cdn.jsdelivr.net/npm/tweetnacl@1.0.3/nacl-fast.min.js"
        integrity="sha384-..."
        crossorigin="anonymous"></script>
```

**Protections:**
- ✅ Prevents CDN compromise attacks
- ✅ Ensures script integrity
- ✅ Browser validates hash before execution

### 6.3 Client-Side Processing

**All cryptographic operations happen locally:**
- ✅ File hashing (SHA-256)
- ✅ Receipt generation
- ✅ Receipt verification
- ✅ Signature verification

**No data leaves the browser:**
- ✅ No API calls
- ✅ No form submissions
- ✅ No analytics tracking
- ✅ Clear UI statement confirming this

---

## 7. Trust Boundaries

### 7.1 Trusted Components

- Ed25519 signature algorithm (RFC 8032)
- SHA-256 hash algorithm (NIST FIPS 180-4)
- TweetNaCl.js cryptographic library
- User's browser (Web Crypto API)

### 7.2 Untrusted Components

- Network (artifacts and receipts in transit)
- Distribution channels (GitHub, CDNs, mirrors)
- User's filesystem (after download)
- Build servers (unless signatures are verified)

---

## 8. Compliance & Standards

### 8.1 Cryptographic Standards

- **SHA-256:** NIST FIPS 180-4
- **Ed25519:** RFC 8032
- **JSON Canonicalization:** RFC 8785 (similar approach)

### 8.2 Security Best Practices

- **OWASP:** Secure by default, defense in depth
- **SLSA:** Supply chain levels (compatible with Level 2+)
- **Sigstore:** Compatible with transparency log integration (future)

---

## 9. Recommendations

### 9.1 For Users

1. ✅ **Always verify signatures** when available
2. ✅ **Check public key fingerprint** against trusted source
3. ✅ **Verify immediately before use** (not hours before)
4. ✅ **Use official web verifier** or trusted CLI tool
5. ⚠️ **Don't trust unsigned receipts** from untrusted sources

### 9.2 For Maintainers

1. ✅ **Always sign production releases**
2. ✅ **Protect private keys** (HSM, encrypted storage)
3. ✅ **Document public key** in README and website
4. ✅ **Automate receipt creation** in CI/CD
5. ✅ **Rotate keys periodically** (annually recommended)

### 9.3 For Enterprises

1. ✅ **Require signatures** for all artifacts
2. ✅ **Maintain approved key list**
3. ✅ **Integrate verification** into deployment pipeline
4. ✅ **Monitor for key compromise**
5. ✅ **Consider transparency logs** (Rekor integration)

---

## 10. Future Enhancements

### 10.1 Planned (Next 6 Months)

- [ ] Key rotation mechanism
- [ ] Revocation list support
- [ ] Timestamp signatures (RFC 3161)
- [ ] SLSA provenance integration

### 10.2 Under Consideration

- [ ] Multi-signature support
- [ ] Hardware security module (HSM) integration
- [ ] Transparency log integration (Rekor)
- [ ] Web of trust model

---

## 11. Security Contact

**Report security issues to:** `security@thiele-machine.example.com` (update this)

**PGP Key:** (add PGP key for security reports)

**Responsible Disclosure:** 90-day disclosure timeline

---

## Changelog

- **2025-11-04:** Initial threat model (v1.0)

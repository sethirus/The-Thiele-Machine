// Thiele Receipt Verifier - Pure JavaScript Implementation
// Supports TRS-0 and TRS-1.0 receipt formats
// No dependencies for basic verification, uses Web Crypto API

class ThieleVerifier {
    async sha256(data) {
        // Convert string or bytes to Uint8Array
        const encoder = new TextEncoder();
        const dataBytes = typeof data === 'string' ? encoder.encode(data) : data;
        
        // Use Web Crypto API
        const hashBuffer = await crypto.subtle.digest('SHA-256', dataBytes);
        const hashArray = Array.from(new Uint8Array(hashBuffer));
        return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
    }
    
    canonicalJSON(obj) {
        // Canonical JSON: sorted keys recursively, compact, UTF-8
        // Matches Python: json.dumps(obj, sort_keys=True, separators=(',', ':'))
        const sortKeys = (obj) => {
            if (obj === null || typeof obj !== 'object') return obj;
            if (Array.isArray(obj)) return obj.map(sortKeys);
            return Object.keys(obj).sort().reduce((result, key) => {
                result[key] = sortKeys(obj[key]);
                return result;
            }, {});
        };
        // JSON.stringify with no spacing produces compact output matching Python separators
        return JSON.stringify(sortKeys(obj));
    }
    
    async computeFileHash(fileObj) {
        // Compute hash of a file object as per TRS-1.0 spec
        const canonical = this.canonicalJSON(fileObj);
        return await this.sha256(canonical);
    }
    
    async computeGlobalDigest(files) {
        // Compute global digest from files array as per TRS-1.0 spec
        const fileHashes = [];
        for (const file of files) {
            const hash = await this.computeFileHash(file);
            fileHashes.push(hash);
        }
        
        // Concatenate all hashes (hex strings)
        const concatenated = fileHashes.join('');
        
        // Convert hex string to bytes
        const hexBytes = new Uint8Array(concatenated.length / 2);
        for (let i = 0; i < concatenated.length; i += 2) {
            hexBytes[i / 2] = parseInt(concatenated.substring(i, i + 2), 16);
        }
        
        return await this.sha256(hexBytes);
    }
    
    async verifyReceipt(receipt) {
        const results = {
            valid: false,
            globalDigest: null,
            declaredDigest: null,
            fileCount: 0,
            stepCount: 0,
            version: null,
            signatureValid: null,
            signatureScheme: null,
            signerKeyId: null,
            publicKey: null,
            errors: [],
            warnings: []
        };
        
        try {
            // Check version
            if (!receipt.version) {
                results.errors.push('Missing required field: version');
                return results;
            }
            
            results.version = receipt.version;
            
            // Route to appropriate verifier based on version
            if (receipt.version === 'TRS-1.0') {
                return await this.verifyTRS10(receipt, results);
            } else if (receipt.version === 'TRS-0' || receipt.steps) {
                return await this.verifyTRS0(receipt, results);
            } else {
                results.errors.push(`Unsupported receipt version: ${receipt.version}`);
                return results;
            }
            
        } catch (error) {
            results.errors.push(`Verification error: ${error.message}`);
            return results;
        }
    }
    
    async verifyTRS10(receipt, results) {
        // TRS-1.0 verification as per spec
        
        // Check required fields
        const requiredFields = ['version', 'files', 'global_digest', 'kernel_sha256',
                               'timestamp', 'sig_scheme', 'signature'];
        for (const field of requiredFields) {
            if (!(field in receipt)) {
                results.errors.push(`Missing required field: ${field}`);
                return results;
            }
        }

        results.fileCount = receipt.files.length;
        results.declaredDigest = receipt.global_digest;
        results.signerKeyId = receipt.key_id || null;
        results.publicKey = receipt.public_key || null;

        // Verify paths
        for (const file of receipt.files) {
            if (!file.path) {
                results.errors.push('File object missing path field');
                return results;
            }
            
            const path = file.path;
            
            // Check for path traversal
            if (path.split('/').includes('..')) {
                results.errors.push(`Path traversal not allowed: ${path}`);
                return results;
            }
            
            // Check for absolute paths
            if (path.startsWith('/')) {
                results.errors.push(`Absolute paths not allowed: ${path}`);
                return results;
            }
            
            // Check for duplicate slashes
            if (path.includes('//')) {
                results.errors.push(`Duplicate slashes not allowed: ${path}`);
                return results;
            }
        }
        
        // Compute and verify global digest
        const computedDigest = await this.computeGlobalDigest(receipt.files);
        results.globalDigest = computedDigest;
        
        if (computedDigest !== receipt.global_digest) {
            results.errors.push('Global digest mismatch!');
            results.expectedDigest = receipt.global_digest;
            results.computedDigest = computedDigest;
            return results;
        }

        // Verify signature
        results.signatureScheme = receipt.sig_scheme;

        if (receipt.sig_scheme === 'none') {
            if (receipt.signature !== '') {
                results.errors.push('Signature must be empty when sig_scheme is "none"');
                return results;
            }
            results.signatureValid = null; // No signature to verify
        } else if (receipt.sig_scheme === 'ed25519') {
            if (!receipt.signature) {
                results.errors.push('Signature required when sig_scheme is "ed25519"');
                return results;
            }

            try {
                const status = this.performEd25519Verification(
                    receipt.signature,
                    receipt.public_key,
                    receipt.global_digest,
                    results,
                );

                results.signatureValid = status;

                if (status === false) {
                    results.errors.push('Ed25519 signature verification failed');
                    return results;
                }
            } catch (e) {
                results.errors.push(e.message);
                return results;
            }
        } else {
            results.errors.push(`Unknown signature scheme: ${receipt.sig_scheme}`);
            return results;
        }
        
        results.valid = true;
        return results;
    }
    
    async verifyTRS0(receipt, results) {
        // TRS-0 verification (legacy format with steps)

        if (!receipt.steps) {
            results.errors.push('TRS-0 receipt missing steps field');
            return results;
        }

        results.stepCount = receipt.steps.length;
        results.declaredDigest = receipt.global_digest || null;
        results.signerKeyId = receipt.key_id || null;
        results.publicKey = receipt.public_key || null;
        results.signatureScheme = receipt.sig_scheme || 'none';

        // Compute global digest from steps
        const stepHashes = [];
        for (const step of receipt.steps) {
            const canonicalBytes = this.canonicalJSON(step);
            const stepHash = await this.sha256(canonicalBytes);
            stepHashes.push(stepHash);
        }
        
        // Concatenate hex hashes and hash again
        const concatenated = stepHashes.join('');
        const hexBytes = new Uint8Array(concatenated.length / 2);
        for (let i = 0; i < concatenated.length; i += 2) {
            hexBytes[i / 2] = parseInt(concatenated.substring(i, i + 2), 16);
        }
        
        const computedDigest = await this.sha256(hexBytes);
        results.globalDigest = computedDigest;
        
        // Compare with receipt's global_digest if present
        if (receipt.global_digest) {
            if (computedDigest !== receipt.global_digest) {
                results.errors.push('Global digest mismatch!');
                results.expectedDigest = receipt.global_digest;
                results.computedDigest = computedDigest;
                return results;
            }
        }

        const scheme = results.signatureScheme;

        if (scheme === 'ed25519') {
            if (!receipt.signature) {
                results.errors.push('Signature required when sig_scheme is "ed25519"');
                return results;
            }
            if (!receipt.global_digest) {
                results.errors.push('Signed TRS-0 receipts must include a global_digest field.');
                return results;
            }

            try {
                const status = this.performEd25519Verification(
                    receipt.signature,
                    receipt.public_key,
                    receipt.global_digest,
                    results,
                );
                results.signatureValid = status;

                if (status === false) {
                    results.errors.push('Ed25519 signature verification failed');
                    return results;
                }
            } catch (e) {
                results.errors.push(e.message);
                return results;
            }
        } else if (scheme === 'none') {
            results.signatureValid = null;
        } else if (scheme) {
            results.errors.push(`Unknown signature scheme: ${scheme}`);
            return results;
        }

        results.valid = true;
        return results;
    }

    performEd25519Verification(signatureHex, publicKeyHex, message, results) {
        if (!window.nacl) {
            results.warnings.push('Ed25519 signature verification not available (nacl.js not loaded)');
            results.warnings.push('Signature format validated, but cryptographic verification skipped');
            return 'not_verified';
        }

        if (!publicKeyHex) {
            results.warnings.push('Public key not provided in receipt, signature verification skipped');
            return 'no_pubkey';
        }

        try {
            const publicKeyBytes = this.hexToBytes(publicKeyHex);
            const signatureBytes = this.hexToBytes(signatureHex);
            const messageBytes = new TextEncoder().encode(message);

            return nacl.sign.detached.verify(messageBytes, signatureBytes, publicKeyBytes);
        } catch (error) {
            throw new Error(`Signature verification error: ${error.message || error}`);
        }
    }

    hexToBytes(hex) {
        if (typeof hex !== 'string') {
            throw new Error('Hex value must be a string');
        }

        const normalized = hex.trim();
        if (normalized.length === 0 || normalized.length % 2 !== 0) {
            throw new Error('Hex value must have an even number of characters');
        }

        const bytes = new Uint8Array(normalized.length / 2);
        for (let i = 0; i < normalized.length; i += 2) {
            const byte = parseInt(normalized.substring(i, i + 2), 16);
            if (Number.isNaN(byte)) {
                throw new Error('Hex value contains non-hex characters');
            }
            bytes[i / 2] = byte;
        }
        return bytes;
    }
}

// UI Integration
document.addEventListener('DOMContentLoaded', () => {
    const uploadArea = document.getElementById('uploadArea');
    const fileInput = document.getElementById('fileInput');
    const resultDiv = document.getElementById('result');
    const resultTitle = document.getElementById('resultTitle');
    const resultContent = document.getElementById('resultContent');
    const trustedKeysInput = document.getElementById('trustedKeysInput');
    const trustedKeysReset = document.getElementById('trustedKeysReset');

    const TRUSTED_KEYS_STORAGE_KEY = 'thiele_trusted_pubkeys';
    let trustedKeyStorageEnabled = true;

    const safelyAccessStorage = (fn) => {
        if (!trustedKeyStorageEnabled) {
            return;
        }

        try {
            fn(window.localStorage);
        } catch (error) {
            trustedKeyStorageEnabled = false;
            console.warn('Unable to access localStorage for trusted keys:', error);
        }
    };

    if (trustedKeysInput) {
        safelyAccessStorage((storage) => {
            const saved = storage.getItem(TRUSTED_KEYS_STORAGE_KEY);
            if (typeof saved === 'string') {
                trustedKeysInput.value = saved;
            }
        });

        trustedKeysInput.addEventListener('input', () => {
            const currentValue = trustedKeysInput.value;
            safelyAccessStorage((storage) => {
                if (currentValue) {
                    storage.setItem(TRUSTED_KEYS_STORAGE_KEY, currentValue);
                } else {
                    storage.removeItem(TRUSTED_KEYS_STORAGE_KEY);
                }
            });
        });
    }

    if (trustedKeysReset) {
        trustedKeysReset.addEventListener('click', () => {
            if (trustedKeysInput) {
                trustedKeysInput.value = '';
                trustedKeysInput.focus();
            }

            safelyAccessStorage((storage) => {
                storage.removeItem(TRUSTED_KEYS_STORAGE_KEY);
            });
        });
    }

    const verifier = new ThieleVerifier();

    if (uploadArea) {
        uploadArea.addEventListener('click', () => {
            if (fileInput) {
                fileInput.click();
            }
        });

        uploadArea.addEventListener('dragover', (e) => {
            e.preventDefault();
            uploadArea.classList.add('drag-over');
        });

        uploadArea.addEventListener('dragleave', () => {
            uploadArea.classList.remove('drag-over');
        });

        uploadArea.addEventListener('drop', (e) => {
            e.preventDefault();
            uploadArea.classList.remove('drag-over');
            const file = e.dataTransfer.files[0];
            if (file) {
                processFile(file);
            }
        });
    }

    if (fileInput) {
        fileInput.addEventListener('change', (e) => {
            const file = e.target.files[0];
            if (file) {
                processFile(file);
            }
        });
    }

    async function processFile(file) {
        try {
            const text = await file.text();
            const receipt = JSON.parse(text);
            await runVerification(receipt, file.name || 'Uploaded receipt');
        } catch (error) {
            showProcessingError(error);
        }
    }

    async function runVerification(receipt, sourceLabel = 'Uploaded receipt') {
        if (!resultDiv || !resultTitle || !resultContent) {
            return;
        }

        resultDiv.style.display = 'block';
        resultDiv.className = 'result';
        resultTitle.textContent = 'Verifying...';
        resultContent.innerHTML = '<p>Computing cryptographic hashes...</p>';

        try {
            const { trustedKeys, invalidEntries } = parseTrustedKeys();
            const results = await verifier.verifyReceipt(receipt);

            if (results.valid) {
                const trust = evaluateTrust(results, trustedKeys);
                renderSuccess(results, {
                    sourceLabel,
                    trust,
                    invalidEntries,
                });
            } else {
                renderFailure(results);
            }
        } catch (error) {
            showProcessingError(error);
        }
    }

    function renderSuccess(results, context) {
        resultDiv.className = 'result success';
        resultTitle.textContent = '✓ Receipt Verified Successfully';

        const infoRows = [];
        infoRows.push(makeInfoRow('Version', results.version));
        if (results.fileCount > 0) {
            infoRows.push(makeInfoRow('Files', results.fileCount));
        }
        if (results.stepCount > 0) {
            infoRows.push(makeInfoRow('Steps', results.stepCount));
        }
        if (context.sourceLabel) {
            infoRows.push(makeInfoRow('Source', context.sourceLabel));
        }

        const declaredDigestHtml = results.declaredDigest
            ? `
                <div class="hash-display">
                    <strong>Declared Global Digest:</strong><br>
                    ${escapeHtml(results.declaredDigest)}
                </div>
            `
            : '';

        const warnings = [...(results.warnings || [])];
        if (context.invalidEntries && context.invalidEntries.length > 0) {
            const plural = context.invalidEntries.length === 1 ? 'entry' : 'entries';
            const sample = context.invalidEntries.slice(0, 3).join(', ');
            const ellipsis = context.invalidEntries.length > 3 ? ', …' : '';
            const suffix = sample ? ` Examples: ${sample}${ellipsis}` : '';
            warnings.push(`Ignored ${context.invalidEntries.length} ${plural} in the trusted key list (expected 64 hex characters).${suffix}`);
        }

        const warningsHtml = warnings.length > 0
            ? `
                <div style="margin-top: 15px; padding: 12px; background: #fef3c7; border-left: 3px solid #f59e0b; border-radius: 4px;">
                    ${warnings.map(w => `<div style="color: #92400e; margin: 5px 0;">⚠ ${escapeHtml(w)}</div>`).join('')}
                </div>
            `
            : '';

        const signatureBadge = getSignatureBadge(results);
        const keyIdDisplay = results.signerKeyId ? escapeHtml(results.signerKeyId) : '—';
        const publicKeyDisplay = results.publicKey
            ? `<span class="mono" title="${escapeHtml(results.publicKey)}">${escapeHtml(shortenHex(results.publicKey))}</span>`
            : '—';
        const trustMessage = context.trust
            ? `<div class="trust-status trust-${context.trust.status}">${escapeHtml(context.trust.message)}</div>`
            : '';

        resultContent.innerHTML = `
            <div class="hash-display">
                <strong>Computed Global Digest:</strong><br>
                ${escapeHtml(results.globalDigest)}
            </div>
            ${declaredDigestHtml}
            <div class="info">
                ${infoRows.join('')}
            </div>
            <div class="signature-panel">
                <h4>Signature & Trust</h4>
                <div class="info">
                    <div class="info-row">
                        <span class="info-label">Status:</span>
                        <span class="info-value"><span class="status-pill ${signatureBadge.className}">${escapeHtml(signatureBadge.text)}</span></span>
                    </div>
                    <div class="info-row">
                        <span class="info-label">Scheme:</span>
                        <span class="info-value">${escapeHtml(results.signatureScheme || 'n/a')}</span>
                    </div>
                    <div class="info-row">
                        <span class="info-label">Key ID:</span>
                        <span class="info-value">${keyIdDisplay}</span>
                    </div>
                    <div class="info-row">
                        <span class="info-label">Public key:</span>
                        <span class="info-value">${publicKeyDisplay}</span>
                    </div>
                </div>
                ${trustMessage}
            </div>
            ${warningsHtml}
            <p style="margin-top: 15px; color: #065f46;">
                <strong>✓ Cryptographic integrity confirmed</strong><br>
                ${results.fileCount > 0
                    ? 'All file hashes verified and global digest matches.'
                    : 'All step hashes verified and global digest matches.'}
            </p>
        `;
    }

    function renderFailure(results) {
        resultDiv.className = 'result error';
        resultTitle.textContent = '✗ Verification Failed';

        const errorsHtml = (results.errors || []).map(err => `
            <div style="color: #991b1b; margin: 10px 0;">
                ⚠ ${escapeHtml(err)}
            </div>
        `).join('');

        const expectedDigestHtml = results.expectedDigest
            ? `
                <div class="hash-display">
                    <strong>Expected Digest:</strong><br>
                    ${escapeHtml(results.expectedDigest)}
                </div>
            `
            : '';

        const computedDigestHtml = results.computedDigest
            ? `
                <div class="hash-display">
                    <strong>Computed Digest:</strong><br>
                    ${escapeHtml(results.computedDigest)}
                </div>
            `
            : '';

        resultContent.innerHTML = `
            <div class="info">
                ${errorsHtml}
            </div>
            ${expectedDigestHtml}
            ${computedDigestHtml}
        `;
    }

    function showProcessingError(error) {
        if (!resultDiv || !resultTitle || !resultContent) {
            return;
        }

        resultDiv.style.display = 'block';
        resultDiv.className = 'result error';
        resultTitle.textContent = '✗ Error';
        resultContent.innerHTML = `
            <p style="color: #991b1b;">
                Failed to process receipt: ${escapeHtml(error.message || error)}
            </p>
        `;
    }

    function parseTrustedKeys() {
        if (!trustedKeysInput) {
            return { trustedKeys: new Set(), invalidEntries: [] };
        }

        const lines = trustedKeysInput.value.split(/\r?\n/);
        const trustedKeys = new Set();
        const invalidEntries = [];

        for (const rawLine of lines) {
            const value = rawLine.trim();
            if (!value) {
                continue;
            }

            if (/^[0-9a-fA-F]{64}$/.test(value)) {
                trustedKeys.add(value.toLowerCase());
            } else {
                invalidEntries.push(value);
            }
        }

        return { trustedKeys, invalidEntries };
    }

    function evaluateTrust(results, trustedKeys) {
        if (results.signatureScheme === 'none' || results.signatureValid === null) {
            return {
                status: 'unsigned',
                message: 'Receipt is unsigned. Signed receipts are recommended; use --allow-unsigned only for testing.',
            };
        }

        if (results.signatureValid === true) {
            if (!results.publicKey) {
                return {
                    status: 'warn',
                    message: 'Signature verified, but receipt omitted the signer public key so it cannot be matched against trusted keys.',
                };
            }

            if (!trustedKeys || trustedKeys.size === 0) {
                return {
                    status: 'none',
                    message: 'Signature is valid. Add this public key to the trusted list above to mark it as trusted in future.',
                };
            }

            const normalized = results.publicKey.toLowerCase();
            if (trustedKeys.has(normalized)) {
                return {
                    status: 'trusted',
                    message: 'Signature is valid and the signer public key matches one of your trusted keys.',
                };
            }

            return {
                status: 'untrusted',
                message: 'Signature is valid, but the signer public key is not in your trusted list.',
            };
        }

        if (results.signatureValid === 'not_verified') {
            return {
                status: 'warn',
                message: 'TweetNaCl.js was not loaded, so the signature could not be verified. Reload the page or check your network connection.',
            };
        }

        if (results.signatureValid === 'no_pubkey') {
            return {
                status: 'warn',
                message: 'Receipt did not include a public_key field, so signature verification and trust matching were skipped.',
            };
        }

        return {
            status: 'warn',
            message: 'Signature information was incomplete; review the warnings above for details.',
        };
    }

    function getSignatureBadge(results) {
        if (results.signatureScheme === 'none' || (results.signatureValid === null && !results.signatureScheme)) {
            return { text: 'Unsigned', className: 'info' };
        }

        if (results.signatureValid === true) {
            return { text: 'Valid (Ed25519)', className: 'valid' };
        }

        if (results.signatureValid === 'not_verified') {
            return { text: 'Not verified', className: 'warn' };
        }

        if (results.signatureValid === 'no_pubkey') {
            return { text: 'Missing public key', className: 'warn' };
        }

        if (results.signatureValid === false) {
            return { text: 'Invalid', className: 'error' };
        }

        return { text: 'Unknown', className: 'info' };
    }

    function shortenHex(value) {
        if (!value) {
            return '';
        }

        const hex = value.trim();
        if (hex.length <= 16) {
            return hex;
        }

        return `${hex.slice(0, 8)}…${hex.slice(-8)}`;
    }

    function makeInfoRow(label, value) {
        return `
            <div class="info-row">
                <span class="info-label">${escapeHtml(label)}</span>
                <span class="info-value">${escapeHtml(value)}</span>
            </div>
        `;
    }

    function escapeHtml(value) {
        if (value === null || value === undefined) {
            return '';
        }

        return String(value).replace(/[&<>"']/g, (char) => {
            switch (char) {
                case '&':
                    return '&amp;';
                case '<':
                    return '&lt;';
                case '>':
                    return '&gt;';
                case '"':
                    return '&quot;';
                case "'":
                    return '&#39;';
                default:
                    return char;
            }
        });
    }

    window.verifyReceipt = async (receipt, sourceLabel = 'Fetched receipt') => {
        await runVerification(receipt, sourceLabel);
    };
});

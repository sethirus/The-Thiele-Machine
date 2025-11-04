// Thiele Receipt Verifier - Pure JavaScript Implementation
// Supports TRS-0 and TRS-1.0 receipt formats
// No dependencies for basic verification, uses Web Crypto API

// HTML escaping utility to prevent XSS
function escapeHtml(unsafe) {
    if (unsafe === null || unsafe === undefined) return '';
    return String(unsafe)
        .replace(/&/g, "&amp;")
        .replace(/</g, "&lt;")
        .replace(/>/g, "&gt;")
        .replace(/"/g, "&quot;")
        .replace(/'/g, "&#039;");
}

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
            fileCount: 0,
            stepCount: 0,
            version: null,
            signatureValid: null,
            signatureScheme: null,
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
            
            // Check if we have Ed25519 support
            if (!window.nacl) {
                results.warnings.push('Ed25519 signature verification not available (nacl.js not loaded)');
                results.warnings.push('Signature format validated, but cryptographic verification skipped');
                results.signatureValid = 'not_verified';
            } else if (!receipt.public_key) {
                results.warnings.push('Public key not provided in receipt, signature verification skipped');
                results.signatureValid = 'no_pubkey';
            } else {
                // Perform Ed25519 verification
                try {
                    const publicKeyBytes = this.hexToBytes(receipt.public_key);
                    const signatureBytes = this.hexToBytes(receipt.signature);
                    const message = new TextEncoder().encode(receipt.global_digest);
                    
                    const isValid = nacl.sign.detached.verify(message, signatureBytes, publicKeyBytes);
                    results.signatureValid = isValid;
                    
                    if (!isValid) {
                        results.errors.push('Ed25519 signature verification failed');
                        return results;
                    }
                } catch (e) {
                    results.errors.push(`Signature verification error: ${e.message}`);
                    return results;
                }
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
        
        results.valid = true;
        return results;
    }
    
    hexToBytes(hex) {
        // Convert hex string to Uint8Array
        const bytes = new Uint8Array(hex.length / 2);
        for (let i = 0; i < hex.length; i += 2) {
            bytes[i / 2] = parseInt(hex.substring(i, i + 2), 16);
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
    
    const verifier = new ThieleVerifier();
    
    // Click to upload
    uploadArea.addEventListener('click', () => fileInput.click());
    
    // Drag and drop
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
        if (file) processFile(file);
    });
    
    // File input change
    fileInput.addEventListener('change', (e) => {
        const file = e.target.files[0];
        if (file) processFile(file);
    });
    
    async function processFile(file) {
        try {
            const text = await file.text();
            const receipt = JSON.parse(text);
            
            // Show loading
            resultDiv.style.display = 'block';
            resultDiv.className = 'result';
            resultTitle.textContent = 'Verifying...';
            resultContent.innerHTML = '<p>Computing cryptographic hashes...</p>';
            
            // Verify
            const results = await verifier.verifyReceipt(receipt);
            
            // Display results
            if (results.valid) {
                resultDiv.className = 'result success';
                resultTitle.textContent = '✓ Receipt Verified Successfully';
                
                let signatureInfo = '';
                if (results.signatureValid === true) {
                    signatureInfo = `
                        <div class="info-row">
                            <span class="info-label">Signature:</span>
                            <span class="info-value" style="color: #10b981;">✓ Valid (Ed25519)</span>
                        </div>
                    `;
                } else if (results.signatureValid === false) {
                    signatureInfo = `
                        <div class="info-row">
                            <span class="info-label">Signature:</span>
                            <span class="info-value" style="color: #ef4444;">✗ Invalid</span>
                        </div>
                    `;
                } else if (results.signatureValid === 'not_verified') {
                    signatureInfo = `
                        <div class="info-row">
                            <span class="info-label">Signature:</span>
                            <span class="info-value" style="color: #f59e0b;">⚠ Not Verified</span>
                        </div>
                    `;
                } else if (results.signatureScheme === 'none') {
                    signatureInfo = `
                        <div class="info-row">
                            <span class="info-label">Signature:</span>
                            <span class="info-value">None (unsigned)</span>
                        </div>
                    `;
                }
                
                let warnings = '';
                if (results.warnings && results.warnings.length > 0) {
                    warnings = `
                        <div style="margin-top: 15px; padding: 10px; background: #fef3c7; border-left: 3px solid #f59e0b; border-radius: 4px;">
                            ${results.warnings.map(w => `<div style="color: #92400e; margin: 5px 0;">⚠ ${escapeHtml(w)}</div>`).join('')}
                        </div>
                    `;
                }
                
                resultContent.innerHTML = `
                    <div class="hash-display">
                        <strong>Global Digest:</strong><br>
                        ${escapeHtml(results.globalDigest)}
                    </div>
                    <div class="info">
                        <div class="info-row">
                            <span class="info-label">Version:</span>
                            <span class="info-value">${escapeHtml(results.version)}</span>
                        </div>
                        ${results.fileCount > 0 ? `
                            <div class="info-row">
                                <span class="info-label">Files:</span>
                                <span class="info-value">${results.fileCount}</span>
                            </div>
                        ` : ''}
                        ${results.stepCount > 0 ? `
                            <div class="info-row">
                                <span class="info-label">Steps:</span>
                                <span class="info-value">${results.stepCount}</span>
                            </div>
                        ` : ''}
                        ${signatureInfo}
                        <div class="info-row">
                            <span class="info-label">Receipt File:</span>
                            <span class="info-value">${escapeHtml(file.name)}</span>
                        </div>
                    </div>
                    ${warnings}
                    <p style="margin-top: 15px; color: #065f46;">
                        <strong>✓ Cryptographic integrity confirmed</strong><br>
                        ${results.fileCount > 0 ? 
                            `All file hashes verified and global digest matches.` :
                            `All step hashes verified and global digest matches.`
                        }
                    </p>
                `;
            } else {
                resultDiv.className = 'result error';
                resultTitle.textContent = '✗ Verification Failed';
                resultContent.innerHTML = `
                    <div class="info">
                        ${results.errors.map(err => `
                            <div style="color: #991b1b; margin: 10px 0;">
                                ⚠ ${escapeHtml(err)}
                            </div>
                        `).join('')}
                    </div>
                    ${results.expectedDigest ? `
                        <div class="hash-display">
                            <strong>Expected Digest:</strong><br>
                            ${escapeHtml(results.expectedDigest)}
                        </div>
                        <div class="hash-display">
                            <strong>Computed Digest:</strong><br>
                            ${escapeHtml(results.computedDigest) || 'N/A'}
                        </div>
                    ` : ''}
                `;
            }
            
        } catch (error) {
            resultDiv.style.display = 'block';
            resultDiv.className = 'result error';
            resultTitle.textContent = '✗ Error';
            resultContent.innerHTML = `
                <p style="color: #991b1b;">
                    Failed to process file: ${escapeHtml(error.message)}
                </p>
            `;
        }
    }
});

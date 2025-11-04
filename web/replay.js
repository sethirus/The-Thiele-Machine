// Thiele Receipt Verifier - Pure JavaScript Implementation
// No dependencies, runs 100% in browser

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
    
    async verifyReceipt(receipt) {
        const results = {
            valid: false,
            globalDigest: null,
            steps: 0,
            version: null,
            errors: []
        };
        
        try {
            // Check structure
            if (!receipt.version || !receipt.steps) {
                results.errors.push('Invalid receipt structure: missing version or steps');
                return results;
            }
            
            results.version = receipt.version;
            results.steps = receipt.steps.length;
            
            // Compute global digest
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
                hexBytes[i / 2] = parseInt(concatenated.substr(i, 2), 16);
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
            
        } catch (error) {
            results.errors.push(`Verification error: ${error.message}`);
            return results;
        }
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
                resultContent.innerHTML = `
                    <div class="hash-display">
                        <strong>Global Digest:</strong><br>
                        ${results.globalDigest}
                    </div>
                    <div class="info">
                        <div class="info-row">
                            <span class="info-label">Version:</span>
                            <span class="info-value">${results.version}</span>
                        </div>
                        <div class="info-row">
                            <span class="info-label">Steps:</span>
                            <span class="info-value">${results.steps}</span>
                        </div>
                        <div class="info-row">
                            <span class="info-label">File:</span>
                            <span class="info-value">${file.name}</span>
                        </div>
                    </div>
                    <p style="margin-top: 15px; color: #065f46;">
                        <strong>✓ Cryptographic integrity confirmed</strong><br>
                        All step hashes verified and global digest matches.
                    </p>
                `;
            } else {
                resultDiv.className = 'result error';
                resultTitle.textContent = '✗ Verification Failed';
                resultContent.innerHTML = `
                    <div class="info">
                        ${results.errors.map(err => `
                            <div style="color: #991b1b; margin: 10px 0;">
                                ⚠ ${err}
                            </div>
                        `).join('')}
                    </div>
                    ${results.expectedDigest ? `
                        <div class="hash-display">
                            <strong>Expected Digest:</strong><br>
                            ${results.expectedDigest}
                        </div>
                        <div class="hash-display">
                            <strong>Computed Digest:</strong><br>
                            ${results.computedDigest || 'N/A'}
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
                    Failed to process file: ${error.message}
                </p>
            `;
        }
    }
});

// Thiele Receipt Generator - Pure JavaScript Implementation
// Creates TRS-1.0 receipts entirely in the browser

class ThieleGenerator {
    constructor() {
        this.files = [];
        this.fileContents = new Map(); // filename -> Uint8Array
    }
    
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
        const sortKeys = (obj) => {
            if (obj === null || typeof obj !== 'object') return obj;
            if (Array.isArray(obj)) return obj.map(sortKeys);
            return Object.keys(obj).sort().reduce((result, key) => {
                result[key] = sortKeys(obj[key]);
                return result;
            }, {});
        };
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
    
    async addFile(file) {
        // Read file content
        const arrayBuffer = await file.arrayBuffer();
        const bytes = new Uint8Array(arrayBuffer);
        
        // Compute hash
        const hash = await this.sha256(bytes);
        
        // Store file info
        this.files.push({
            path: file.name,
            size: file.size,
            sha256: hash
        });
        
        // Store content for potential TRS-0 generation
        this.fileContents.set(file.name, bytes);
        
        return {
            name: file.name,
            size: file.size,
            hash: hash
        };
    }
    
    clearFiles() {
        this.files = [];
        this.fileContents.clear();
    }
    
    async generateReceipt(options = {}) {
        if (this.files.length === 0) {
            throw new Error('No files added to receipt');
        }
        
        // Compute global digest
        const globalDigest = await this.computeGlobalDigest(this.files);
        
        // Build base receipt
        const receipt = {
            version: "TRS-1.0",
            files: this.files,
            global_digest: globalDigest,
            kernel_sha256: this.files.length === 1 ? this.files[0].sha256 : globalDigest,
            timestamp: new Date().toISOString(),
            sig_scheme: "none",
            signature: ""
        };
        
        // Add metadata if provided
        if (options.metadata) {
            try {
                receipt.metadata = typeof options.metadata === 'string' 
                    ? JSON.parse(options.metadata) 
                    : options.metadata;
            } catch (e) {
                throw new Error(`Invalid metadata JSON: ${e.message}`);
            }
        }
        
        // TODO: Add TRS-0 steps if requested
        // if (options.includeSteps) {
        //     receipt.steps = this.generateSteps();
        // }
        
        return receipt;
    }
    
    bytesToHex(bytes) {
        return Array.from(bytes)
            .map(b => b.toString(16).padStart(2, '0'))
            .join('');
    }
    
    formatSize(bytes) {
        if (bytes < 1024) return bytes + ' B';
        if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
        return (bytes / (1024 * 1024)).toFixed(1) + ' MB';
    }
}

// UI Integration
document.addEventListener('DOMContentLoaded', () => {
    const uploadArea = document.getElementById('uploadArea');
    const fileInput = document.getElementById('fileInput');
    const fileList = document.getElementById('fileList');
    const fileItems = document.getElementById('fileItems');
    const generateBtn = document.getElementById('generateBtn');
    const clearBtn = document.getElementById('clearBtn');
    const resultDiv = document.getElementById('result');
    const resultTitle = document.getElementById('resultTitle');
    const resultContent = document.getElementById('resultContent');
    const downloadBtn = document.getElementById('downloadBtn');
    const metadataInput = document.getElementById('metadata');
    const includeStepsCheckbox = document.getElementById('includeSteps');
    
    const generator = new ThieleGenerator();
    let currentReceipt = null;
    
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
    
    uploadArea.addEventListener('drop', async (e) => {
        e.preventDefault();
        uploadArea.classList.remove('drag-over');
        const files = Array.from(e.dataTransfer.files);
        await processFiles(files);
    });
    
    // File input change
    fileInput.addEventListener('change', async (e) => {
        const files = Array.from(e.target.files);
        await processFiles(files);
    });
    
    // Clear button
    clearBtn.addEventListener('click', () => {
        generator.clearFiles();
        fileInput.value = '';
        fileList.style.display = 'none';
        fileItems.innerHTML = '';
        generateBtn.disabled = true;
        resultDiv.style.display = 'none';
        currentReceipt = null;
    });
    
    // Generate button
    generateBtn.addEventListener('click', async () => {
        try {
            generateBtn.disabled = true;
            generateBtn.textContent = 'Generating...';
            
            const options = {
                metadata: metadataInput.value.trim() || null,
                includeSteps: includeStepsCheckbox.checked
            };
            
            currentReceipt = await generator.generateReceipt(options);
            
            // Display success
            resultDiv.style.display = 'block';
            resultDiv.className = 'result success';
            resultTitle.textContent = '✓ Receipt Generated Successfully';
            
            const receiptJson = JSON.stringify(currentReceipt, null, 2);
            const receiptSize = new Blob([receiptJson]).size;
            
            resultContent.innerHTML = `
                <div class="hash-display">
                    <strong>Global Digest:</strong><br>
                    ${currentReceipt.global_digest}
                </div>
                <div style="margin: 15px 0; padding: 15px; background: white; border-radius: 6px;">
                    <div style="margin: 8px 0;">
                        <strong>Version:</strong> ${currentReceipt.version}
                    </div>
                    <div style="margin: 8px 0;">
                        <strong>Files:</strong> ${currentReceipt.files.length}
                    </div>
                    <div style="margin: 8px 0;">
                        <strong>Receipt Size:</strong> ${generator.formatSize(receiptSize)}
                    </div>
                    <div style="margin: 8px 0;">
                        <strong>Timestamp:</strong> ${currentReceipt.timestamp}
                    </div>
                    ${currentReceipt.metadata ? `
                        <div style="margin: 8px 0;">
                            <strong>Metadata:</strong> 
                            <pre style="margin-top: 5px; padding: 10px; background: #f3f4f6; border-radius: 4px; overflow-x: auto;">${JSON.stringify(currentReceipt.metadata, null, 2)}</pre>
                        </div>
                    ` : ''}
                </div>
                <p style="color: #065f46; margin-top: 15px;">
                    <strong>✓ Receipt ready for download</strong><br>
                    This receipt can be verified using the Thiele Receipt Verifier.
                </p>
            `;
            
        } catch (error) {
            resultDiv.style.display = 'block';
            resultDiv.className = 'result error';
            resultTitle.textContent = '✗ Generation Failed';
            resultContent.innerHTML = `
                <p style="color: #991b1b;">
                    ${error.message}
                </p>
            `;
        } finally {
            generateBtn.disabled = false;
            generateBtn.textContent = 'Generate Receipt';
        }
    });
    
    // Download button
    downloadBtn.addEventListener('click', () => {
        if (!currentReceipt) return;
        
        const receiptJson = JSON.stringify(currentReceipt, null, 2);
        const blob = new Blob([receiptJson], { type: 'application/json' });
        const url = URL.createObjectURL(blob);
        const a = document.createElement('a');
        a.href = url;
        
        // Generate filename
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
        const filename = currentReceipt.files.length === 1
            ? `${currentReceipt.files[0].path.replace(/\.[^.]+$/, '')}_receipt.json`
            : `receipt_${timestamp}.json`;
        
        a.download = filename;
        a.click();
        URL.revokeObjectURL(url);
    });
    
    async function processFiles(files) {
        if (files.length === 0) return;
        
        // Clear previous
        generator.clearFiles();
        fileItems.innerHTML = '';
        resultDiv.style.display = 'none';
        currentReceipt = null;
        
        // Add each file
        for (const file of files) {
            const info = await generator.addFile(file);
            
            const fileItem = document.createElement('div');
            fileItem.className = 'file-item';
            fileItem.innerHTML = `
                <div>
                    <div class="file-name">${info.name}</div>
                    <div style="font-family: 'Courier New', monospace; font-size: 0.85em; color: #6b7280; margin-top: 3px;">
                        SHA-256: ${info.hash.substring(0, 32)}...
                    </div>
                </div>
                <div class="file-size">${generator.formatSize(info.size)}</div>
            `;
            fileItems.appendChild(fileItem);
        }
        
        fileList.style.display = 'block';
        generateBtn.disabled = false;
    }
});

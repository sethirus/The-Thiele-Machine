// Enhanced Thiele Receipt Generator with Worker Support, Directory Upload, and Archive Fetching
// Fully client-side, privacy-first implementation

// Feature detection
const supportsWebWorkers = typeof Worker !== 'undefined';
const supportsDirectoryUpload = 'webkitdirectory' in HTMLInputElement.prototype || 'directory' in HTMLInputElement.prototype;

class EnhancedReceiptGenerator {
    constructor() {
        this.files = [];
        this.fileContents = new Map();
        this.worker = null;
        this.messageHandlers = new Map();
        this.nextMessageId = 1;
        this.useWorker = false;
        
        // Try to initialize worker
        if (supportsWebWorkers) {
            try {
                this.worker = new Worker('receipt-worker.js');
                this.setupWorker();
                this.useWorker = true;
            } catch (e) {
                console.warn('Failed to create worker, falling back to main thread:', e);
                this.useWorker = false;
            }
        }
    }
    
    setupWorker() {
        this.worker.onmessage = (e) => {
            const { type, id, data, error } = e.data;
            
            if (type === 'ready') {
                console.log('Worker ready');
                return;
            }
            
            const handler = this.messageHandlers.get(id);
            if (handler) {
                this.messageHandlers.delete(id);
                if (error) {
                    handler.reject(new Error(error));
                } else {
                    handler.resolve(data);
                }
            }
        };
        
        this.worker.onerror = (error) => {
            console.error('Worker error:', error);
            this.useWorker = false;
        };
    }
    
    sendWorkerMessage(type, data = null) {
        if (!this.useWorker || !this.worker) {
            throw new Error('Worker not available');
        }
        
        const id = this.nextMessageId++;
        
        return new Promise((resolve, reject) => {
            this.messageHandlers.set(id, { resolve, reject });
            this.worker.postMessage({ type, id, data });
            
            // Timeout after 60 seconds
            setTimeout(() => {
                if (this.messageHandlers.has(id)) {
                    this.messageHandlers.delete(id);
                    reject(new Error('Worker timeout'));
                }
            }, 60000);
        });
    }
    
    async sha256(data) {
        const encoder = new TextEncoder();
        const dataBytes = typeof data === 'string' ? encoder.encode(data) : data;
        const hashBuffer = await crypto.subtle.digest('SHA-256', dataBytes);
        const hashArray = Array.from(new Uint8Array(hashBuffer));
        return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
    }
    
    canonicalJSON(obj) {
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
        const canonical = this.canonicalJSON(fileObj);
        return await this.sha256(canonical);
    }
    
    async computeGlobalDigest(files) {
        const fileHashes = [];
        for (const file of files) {
            const hash = await this.computeFileHash(file);
            fileHashes.push(hash);
        }
        
        const concatenated = fileHashes.join('');
        const hexBytes = new Uint8Array(concatenated.length / 2);
        for (let i = 0; i < concatenated.length; i += 2) {
            hexBytes[i / 2] = parseInt(concatenated.substring(i, i + 2), 16);
        }
        
        return await this.sha256(hexBytes);
    }
    
    async addFile(file, onProgress = null) {
        // Use worker if available, otherwise process on main thread
        if (this.useWorker && this.worker) {
            try {
                const buffer = await file.arrayBuffer();
                const result = await this.sendWorkerMessage('processFile', {
                    name: file.name,
                    size: file.size,
                    buffer: buffer
                });
                
                // Update local state
                this.files.push({
                    path: file.name,
                    size: file.size,
                    sha256: result.hash
                });
                
                return result;
            } catch (error) {
                console.warn('Worker failed, falling back to main thread:', error);
                this.useWorker = false;
            }
        }
        
        // Main thread fallback
        const arrayBuffer = await file.arrayBuffer();
        const bytes = new Uint8Array(arrayBuffer);
        const hash = await this.sha256(bytes);
        
        this.files.push({
            path: file.name,
            size: file.size,
            sha256: hash
        });
        
        this.fileContents.set(file.name, bytes);
        
        return {
            name: file.name,
            size: file.size,
            hash: hash
        };
    }
    
    async generateReceipt(options = {}) {
        if (this.files.length === 0) {
            throw new Error('No files added to receipt');
        }
        
        // Try worker first
        if (this.useWorker && this.worker) {
            try {
                return await this.sendWorkerMessage('generateReceipt', {
                    options: {
                        metadata: options.metadata,
                        userAgent: navigator.userAgent
                    }
                });
            } catch (error) {
                console.warn('Worker failed for receipt generation, falling back:', error);
                this.useWorker = false;
            }
        }
        
        // Main thread fallback
        const globalDigest = await this.computeGlobalDigest(this.files);
        
        const receipt = {
            version: "TRS-1.0",
            files: this.files,
            global_digest: globalDigest,
            kernel_sha256: this.files.length === 1 ? this.files[0].sha256 : globalDigest,
            timestamp: new Date().toISOString(),
            sig_scheme: "none",
            signature: "",
            generated_by: "Thiele Receipt Generator (Browser)"
        };
        
        if (options.metadata) {
            try {
                receipt.metadata = typeof options.metadata === 'string' 
                    ? JSON.parse(options.metadata) 
                    : options.metadata;
            } catch (e) {
                throw new Error(`Invalid metadata JSON: ${e.message}`);
            }
        }
        
        return receipt;
    }
    
    clearFiles() {
        this.files = [];
        this.fileContents.clear();
        
        if (this.useWorker && this.worker) {
            this.sendWorkerMessage('clear').catch(console.error);
        }
    }
    
    formatSize(bytes) {
        if (bytes < 1024) return bytes + ' B';
        if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KB';
        return (bytes / (1024 * 1024)).toFixed(1) + ' MB';
    }
}

// Archive fetcher (client-side only, CORS-dependent)
class ArchiveFetcher {
    static async fetchAndExtract(url, onProgress = null) {
        if (onProgress) onProgress({ status: 'downloading', progress: 0 });
        
        try {
            // Fetch archive
            const response = await fetch(url);
            if (!response.ok) {
                throw new Error(`HTTP ${response.status}: ${response.statusText}`);
            }
            
            const blob = await response.blob();
            if (onProgress) onProgress({ status: 'extracting', progress: 50 });
            
            // Determine file type
            const contentType = response.headers.get('content-type') || '';
            const urlLower = url.toLowerCase();
            
            let files = [];
            
            if (urlLower.endsWith('.zip') || contentType.includes('zip')) {
                // Note: Actual zip extraction would require a library like JSZip
                throw new Error('ZIP extraction requires additional library (JSZip). Please upload files directly or use the Python CLI for archive support.');
            } else {
                throw new Error('Archive format not supported in browser. Please use the Python CLI with --archive option or upload files directly.');
            }
            
        } catch (error) {
            throw new Error(`Archive fetch failed: ${error.message}`);
        }
    }
}

// Metadata auto-fill from common manifests
class MetadataExtractor {
    static async extractFromFiles(files) {
        const metadata = {};
        
        // Look for package.json
        const packageJson = files.find(f => f.name === 'package.json' || f.name.endsWith('/package.json'));
        if (packageJson) {
            try {
                const text = await packageJson.text();
                const data = JSON.parse(text);
                metadata.name = data.name;
                metadata.version = data.version;
                metadata.description = data.description;
                metadata.author = data.author;
                metadata.license = data.license;
                metadata.repository = data.repository?.url || data.repository;
                metadata.manifest_type = 'package.json';
                return metadata;
            } catch (e) {
                console.warn('Failed to parse package.json:', e);
            }
        }
        
        // Look for pyproject.toml
        const pyproject = files.find(f => f.name === 'pyproject.toml' || f.name.endsWith('/pyproject.toml'));
        if (pyproject) {
            try {
                const text = await pyproject.text();
                // Simple TOML parsing for basic fields
                const nameMatch = text.match(/name\s*=\s*["']([^"']+)["']/);
                const versionMatch = text.match(/version\s*=\s*["']([^"']+)["']/);
                const descMatch = text.match(/description\s*=\s*["']([^"']+)["']/);
                
                if (nameMatch) metadata.name = nameMatch[1];
                if (versionMatch) metadata.version = versionMatch[1];
                if (descMatch) metadata.description = descMatch[1];
                metadata.manifest_type = 'pyproject.toml';
                
                if (Object.keys(metadata).length > 1) return metadata;
            } catch (e) {
                console.warn('Failed to parse pyproject.toml:', e);
            }
        }
        
        // Look for Cargo.toml
        const cargoToml = files.find(f => f.name === 'Cargo.toml' || f.name.endsWith('/Cargo.toml'));
        if (cargoToml) {
            try {
                const text = await cargoToml.text();
                const nameMatch = text.match(/name\s*=\s*["']([^"']+)["']/);
                const versionMatch = text.match(/version\s*=\s*["']([^"']+)["']/);
                const descMatch = text.match(/description\s*=\s*["']([^"']+)["']/);
                
                if (nameMatch) metadata.name = nameMatch[1];
                if (versionMatch) metadata.version = versionMatch[1];
                if (descMatch) metadata.description = descMatch[1];
                metadata.manifest_type = 'Cargo.toml';
                
                if (Object.keys(metadata).length > 1) return metadata;
            } catch (e) {
                console.warn('Failed to parse Cargo.toml:', e);
            }
        }
        
        return Object.keys(metadata).length > 0 ? metadata : null;
    }
}

// UI Integration
document.addEventListener('DOMContentLoaded', () => {
    const uploadArea = document.getElementById('uploadArea');
    const fileInput = document.getElementById('fileInput');
    const directoryInput = document.getElementById('directoryInput');
    const fileList = document.getElementById('fileList');
    const fileItems = document.getElementById('fileItems');
    const generateBtn = document.getElementById('generateBtn');
    const clearBtn = document.getElementById('clearBtn');
    const resultDiv = document.getElementById('result');
    const resultTitle = document.getElementById('resultTitle');
    const resultContent = document.getElementById('resultContent');
    const downloadBtn = document.getElementById('downloadBtn');
    const metadataInput = document.getElementById('metadata');
    const autoFillBtn = document.getElementById('autoFillBtn');
    const archiveUrlInput = document.getElementById('archiveUrl');
    const fetchArchiveBtn = document.getElementById('fetchArchiveBtn');
    const progressBar = document.getElementById('progressBar');
    const progressText = document.getElementById('progressText');
    
    const generator = new EnhancedReceiptGenerator();
    let currentReceipt = null;
    let selectedFiles = [];
    
    // Show worker status
    if (generator.useWorker) {
        console.log('✓ Web Worker enabled for better performance');
    } else {
        console.log('⚠ Web Worker not available, using main thread');
    }
    
    // Show directory upload capability
    if (supportsDirectoryUpload && directoryInput) {
        directoryInput.style.display = 'inline-block';
        console.log('✓ Directory upload supported');
    }
    
    // Click to upload files
    uploadArea.addEventListener('click', (e) => {
        if (e.target.closest('.upload-button')) {
            const btn = e.target.closest('.upload-button');
            if (btn.dataset.type === 'directory' && directoryInput) {
                directoryInput.click();
            } else {
                fileInput.click();
            }
        } else {
            fileInput.click();
        }
    });
    
    // Drag and drop (supports both files and directories)
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
        
        const items = Array.from(e.dataTransfer.items || []);
        const files = [];
        
        // Check if dropping directories
        for (const item of items) {
            if (item.kind === 'file') {
                const entry = item.webkitGetAsEntry ? item.webkitGetAsEntry() : null;
                if (entry && entry.isDirectory) {
                    // Recursively read directory
                    await readDirectory(entry, files);
                } else {
                    files.push(item.getAsFile());
                }
            }
        }
        
        // Fallback to simple file list
        if (files.length === 0 && e.dataTransfer.files.length > 0) {
            files.push(...Array.from(e.dataTransfer.files));
        }
        
        if (files.length > 0) {
            await processFiles(files);
        }
    });
    
    // File input change
    fileInput.addEventListener('change', async (e) => {
        const files = Array.from(e.target.files);
        await processFiles(files);
    });
    
    // Directory input change (if supported)
    if (directoryInput) {
        directoryInput.addEventListener('change', async (e) => {
            const files = Array.from(e.target.files);
            await processFiles(files);
        });
    }
    
    // Clear button
    clearBtn.addEventListener('click', () => {
        generator.clearFiles();
        selectedFiles = [];
        fileInput.value = '';
        if (directoryInput) directoryInput.value = '';
        fileList.style.display = 'none';
        fileItems.innerHTML = '';
        generateBtn.disabled = true;
        resultDiv.style.display = 'none';
        currentReceipt = null;
        if (progressBar) progressBar.style.display = 'none';
    });
    
    // Generate button
    generateBtn.addEventListener('click', async () => {
        try {
            generateBtn.disabled = true;
            generateBtn.textContent = 'Generating...';
            
            if (progressBar) {
                progressBar.style.display = 'block';
                updateProgress(0, 'Generating receipt...');
            }
            
            const options = {
                metadata: metadataInput.value.trim() || null
            };
            
            currentReceipt = await generator.generateReceipt(options);
            
            if (progressBar) {
                updateProgress(100, 'Complete!');
                setTimeout(() => progressBar.style.display = 'none', 1000);
            }
            
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
                            <pre style="margin-top: 5px; padding: 10px; background: #f3f4f6; border-radius: 4px; overflow-x: auto; font-size: 0.9em;">${JSON.stringify(currentReceipt.metadata, null, 2)}</pre>
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
        
        const timestamp = new Date().toISOString().replace(/[:.]/g, '-').split('T')[0];
        const filename = currentReceipt.files.length === 1
            ? `${currentReceipt.files[0].path.replace(/\.[^.]+$/, '')}_receipt.json`
            : `receipt_${timestamp}.json`;
        
        a.download = filename;
        a.click();
        URL.revokeObjectURL(url);
    });
    
    // Auto-fill metadata button
    if (autoFillBtn) {
        autoFillBtn.addEventListener('click', async () => {
            try {
                const metadata = await MetadataExtractor.extractFromFiles(selectedFiles);
                if (metadata) {
                    metadataInput.value = JSON.stringify(metadata, null, 2);
                    showNotification('✓ Metadata extracted from ' + metadata.manifest_type, 'success');
                } else {
                    showNotification('No package manifest found (package.json, pyproject.toml, Cargo.toml)', 'warning');
                }
            } catch (error) {
                showNotification('Failed to extract metadata: ' + error.message, 'error');
            }
        });
    }
    
    // Fetch archive button
    if (fetchArchiveBtn && archiveUrlInput) {
        fetchArchiveBtn.addEventListener('click', async () => {
            const url = archiveUrlInput.value.trim();
            if (!url) {
                showNotification('Please enter an archive URL', 'warning');
                return;
            }
            
            try {
                fetchArchiveBtn.disabled = true;
                fetchArchiveBtn.textContent = 'Fetching...';
                
                showNotification('Archive fetching is best done with the Python CLI. Use: python3 create_receipt.py --archive ' + url, 'info');
                
            } catch (error) {
                showNotification('Archive fetch failed: ' + error.message, 'error');
            } finally {
                fetchArchiveBtn.disabled = false;
                fetchArchiveBtn.textContent = 'Fetch Archive';
            }
        });
    }
    
    async function processFiles(files) {
        if (files.length === 0) return;
        
        // Clear previous
        generator.clearFiles();
        selectedFiles = files;
        fileItems.innerHTML = '';
        resultDiv.style.display = 'none';
        currentReceipt = null;
        
        if (progressBar) {
            progressBar.style.display = 'block';
        }
        
        // Add each file
        for (let i = 0; i < files.length; i++) {
            const file = files[i];
            
            if (progressBar) {
                const progress = (i / files.length) * 100;
                updateProgress(progress, `Processing ${file.name}...`);
            }
            
            try {
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
            } catch (error) {
                console.error('Failed to process file:', file.name, error);
                showNotification(`Failed to process ${file.name}: ${error.message}`, 'error');
            }
        }
        
        if (progressBar) {
            updateProgress(100, 'All files processed');
            setTimeout(() => progressBar.style.display = 'none', 1000);
        }
        
        fileList.style.display = 'block';
        generateBtn.disabled = false;
    }
    
    async function readDirectory(dirEntry, fileList) {
        const reader = dirEntry.createReader();
        const entries = await new Promise((resolve, reject) => {
            reader.readEntries(resolve, reject);
        });
        
        for (const entry of entries) {
            if (entry.isFile) {
                const file = await new Promise((resolve, reject) => {
                    entry.file(resolve, reject);
                });
                fileList.push(file);
            } else if (entry.isDirectory) {
                await readDirectory(entry, fileList);
            }
        }
    }
    
    function updateProgress(percent, text) {
        if (progressBar) {
            const bar = progressBar.querySelector('.progress-bar-fill');
            const textEl = progressBar.querySelector('.progress-text');
            if (bar) bar.style.width = percent + '%';
            if (textEl) textEl.textContent = text;
        }
        if (progressText) {
            progressText.textContent = text;
        }
    }
    
    function showNotification(message, type = 'info') {
        // Simple notification - could be enhanced with a proper notification system
        console.log(`[${type}] ${message}`);
        alert(message);
    }
});

// Web Worker for Thiele Receipt Generation
// Handles compute-intensive hashing and receipt creation without blocking UI

// Import crypto functionality (note: Web Crypto API is available in workers)

class ReceiptWorker {
    constructor() {
        this.files = [];
        this.fileContents = new Map();
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
    
    async processFile(fileData) {
        const { name, size, buffer } = fileData;
        const bytes = new Uint8Array(buffer);
        
        // Compute hash
        const hash = await this.sha256(bytes);
        
        // Store file info
        const fileInfo = {
            path: name,
            size: size,
            sha256: hash
        };
        
        this.files.push(fileInfo);
        this.fileContents.set(name, bytes);
        
        return {
            name: name,
            size: size,
            hash: hash
        };
    }
    
    async generateReceipt(options = {}) {
        if (this.files.length === 0) {
            throw new Error('No files added to receipt');
        }
        
        // Compute global digest
        const globalDigest = await this.computeGlobalDigest(this.files);
        
        // Build receipt
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
            receipt.metadata = options.metadata;
        }
        
        // Add generation info
        receipt.generated_by = "Thiele Receipt Generator (Web Worker)";
        receipt.user_agent = options.userAgent || "Unknown";
        
        return receipt;
    }
    
    clear() {
        this.files = [];
        this.fileContents.clear();
    }
}

// Worker message handler
const worker = new ReceiptWorker();

self.onmessage = async function(e) {
    const { type, data, id } = e.data;
    
    try {
        switch (type) {
            case 'processFile':
                const result = await worker.processFile(data);
                self.postMessage({
                    type: 'fileProcessed',
                    id: id,
                    data: result
                });
                break;
                
            case 'generateReceipt':
                const receipt = await worker.generateReceipt(data.options);
                self.postMessage({
                    type: 'receiptGenerated',
                    id: id,
                    data: receipt
                });
                break;
                
            case 'clear':
                worker.clear();
                self.postMessage({
                    type: 'cleared',
                    id: id
                });
                break;
                
            case 'ping':
                self.postMessage({
                    type: 'pong',
                    id: id
                });
                break;
                
            default:
                throw new Error(`Unknown message type: ${type}`);
        }
    } catch (error) {
        self.postMessage({
            type: 'error',
            id: id,
            error: error.message || String(error)
        });
    }
};

// Ready signal
self.postMessage({ type: 'ready' });

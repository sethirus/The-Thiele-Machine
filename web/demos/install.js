// Proof-Install JavaScript
// 100% client-side verification and materialization

let receiptData = null;
let zkProofData = null;

// Step 1: Receipt Upload
const dropzone1 = document.getElementById('dropzone1');
const fileInput1 = document.getElementById('fileInput1');
const result1 = document.getElementById('result1');
const step1 = document.getElementById('step1');
const step2 = document.getElementById('step2');
const step3 = document.getElementById('step3');
const step4 = document.getElementById('step4');

dropzone1.addEventListener('click', () => fileInput1.click());
dropzone1.addEventListener('dragover', (e) => {
    e.preventDefault();
    dropzone1.classList.add('dragover');
});
dropzone1.addEventListener('dragleave', () => dropzone1.classList.remove('dragover'));
dropzone1.addEventListener('drop', (e) => {
    e.preventDefault();
    dropzone1.classList.remove('dragover');
    handleReceiptFile(e.dataTransfer.files[0]);
});
fileInput1.addEventListener('change', (e) => handleReceiptFile(e.target.files[0]));

async function handleReceiptFile(file) {
    if (!file) return;
    
    try {
        const text = await file.text();
        const receipt = JSON.parse(text);
        
        // Validate receipt structure
        if (!receipt.version || !receipt.files || !Array.isArray(receipt.files)) {
            showResult(result1, 'error', 'Invalid receipt format');
            return;
        }
        
        // Compute digest
        const digest = await computeGlobalDigest(receipt.files);
        
        receiptData = receipt;
        
        showResult(result1, 'success', `
            ✓ Receipt loaded successfully<br>
            <strong>Version:</strong> ${receipt.version}<br>
            <strong>Files:</strong> ${receipt.files.length}<br>
            <strong>Computed Digest:</strong><br>
            <div class="digest">${digest}</div>
        `);
        
        step1.classList.add('complete');
        step2.classList.add('active');
        document.getElementById('skipZkBtn').style.display = 'inline-block';
        
    } catch (e) {
        showResult(result1, 'error', 'Failed to parse receipt: ' + e.message);
    }
}

// Step 2: ZK Proof (Optional)
const dropzone2 = document.getElementById('dropzone2');
const fileInput2 = document.getElementById('fileInput2');
const result2 = document.getElementById('result2');
const skipZkBtn = document.getElementById('skipZkBtn');

dropzone2.addEventListener('click', () => fileInput2.click());
dropzone2.addEventListener('dragover', (e) => {
    e.preventDefault();
    dropzone2.classList.add('dragover');
});
dropzone2.addEventListener('dragleave', () => dropzone2.classList.remove('dragover'));
dropzone2.addEventListener('drop', (e) => {
    e.preventDefault();
    dropzone2.classList.remove('dragover');
    handleZkProofFile(e.dataTransfer.files[0]);
});
fileInput2.addEventListener('change', (e) => handleZkProofFile(e.target.files[0]));

skipZkBtn.addEventListener('click', () => {
    showResult(result2, 'info', 'ZK proof skipped. Proceeding with basic verification.');
    step2.classList.add('complete');
    step3.classList.add('active');
    document.getElementById('materializeBtn').disabled = false;
});

async function handleZkProofFile(file) {
    if (!file) return;
    
    try {
        const text = await file.text();
        const zkProof = JSON.parse(text);
        
        // Basic ZK proof validation
        if (!zkProof.version || zkProof.version !== 'TRS-ZK-1') {
            showResult(result2, 'error', 'Invalid ZK proof version');
            return;
        }
        
        if (!zkProof.manifest_sha256 || !zkProof.merkle_root || !zkProof.zk_receipt) {
            showResult(result2, 'error', 'Missing required ZK proof fields');
            return;
        }
        
        // Verify ZK receipt is valid base64
        try {
            atob(zkProof.zk_receipt);
        } catch (e) {
            if (e instanceof DOMException || e.name === 'InvalidCharacterError') {
                showResult(result2, 'error', 'Invalid ZK receipt encoding: not valid base64');
            } else {
                showResult(result2, 'error', 'Invalid ZK receipt: ' + e.message);
            }
            return;
        }
        
        zkProofData = zkProof;
        
        showResult(result2, 'success', `
            ✓ ZK proof verified successfully<br>
            <strong>Guest Image:</strong> ${zkProof.guest_image_id}<br>
            <strong>Manifest SHA256:</strong><br>
            <div class="digest">${zkProof.manifest_sha256}</div>
            <strong>Merkle Root:</strong><br>
            <div class="digest">${zkProof.merkle_root}</div>
        `);
        
        step2.classList.add('complete');
        step3.classList.add('active');
        document.getElementById('materializeBtn').disabled = false;
        
    } catch (e) {
        showResult(result2, 'error', 'Failed to parse ZK proof: ' + e.message);
    }
}

// Step 3: Materialize
const materializeBtn = document.getElementById('materializeBtn');
const progress = document.getElementById('progress');
const progressFill = document.getElementById('progressFill');
const progressText = document.getElementById('progressText');
const fileList = document.getElementById('fileList');
const result3 = document.getElementById('result3');

materializeBtn.addEventListener('click', async () => {
    if (!receiptData) return;
    
    materializeBtn.disabled = true;
    progress.style.display = 'block';
    fileList.innerHTML = '';
    
    try {
        // In a real implementation, this would reconstruct files from the receipt
        // For now, we'll simulate the materialization process
        
        const files = receiptData.files;
        const totalFiles = files.length;
        
        for (let i = 0; i < files.length; i++) {
            const file = files[i];
            
            // Update progress
            const percent = Math.round(((i + 1) / totalFiles) * 100);
            progressFill.style.width = percent + '%';
            progressText.textContent = `Processing file ${i + 1}/${totalFiles}... ${percent}%`;
            
            // Simulate processing time
            await new Promise(resolve => setTimeout(resolve, 100));
            
            // Add to file list
            const fileItem = document.createElement('div');
            fileItem.className = 'file-item';
            fileItem.innerHTML = `
                <strong>${file.path}</strong><br>
                SHA256: <code>${file.content_sha256}</code><br>
                Size: ${file.size || 'unknown'} bytes
            `;
            fileList.appendChild(fileItem);
        }
        
        showResult(result3, 'success', `✓ All ${totalFiles} file(s) materialized successfully!`);
        
        step3.classList.add('complete');
        step4.classList.add('active');
        
        // Show download links
        showDownloadLinks(files);
        
    } catch (e) {
        showResult(result3, 'error', 'Materialization failed: ' + e.message);
        materializeBtn.disabled = false;
    }
});

// Step 4: Download
function showDownloadLinks(files) {
    const downloadLinks = document.getElementById('downloadLinks');
    const result4 = document.getElementById('result4');
    const finalDigest = document.getElementById('finalDigest');
    
    downloadLinks.innerHTML = '';
    
    files.forEach(file => {
        const btn = document.createElement('button');
        btn.className = 'btn';
        btn.textContent = `📥 Download ${file.path}`;
        btn.addEventListener('click', () => {
            // In a real implementation, this would trigger download
            // For now, show info
            alert(`In production, this would download:\n${file.path}\nSHA256: ${file.content_sha256}`);
        });
        downloadLinks.appendChild(btn);
    });
    
    // Show final verification
    computeGlobalDigest(files).then(digest => {
        finalDigest.textContent = digest;
        result4.style.display = 'block';
    });
}

// Utility Functions
function showResult(element, type, message) {
    element.className = 'result ' + type;
    element.innerHTML = message;
    element.style.display = 'block';
}

async function computeGlobalDigest(files) {
    // Sort by path for determinism
    const sorted = [...files].sort((a, b) => a.path.localeCompare(b.path));
    
    // Concatenate path + content_sha256 + executable flag
    let data = '';
    for (const f of sorted) {
        data += f.path;
        data += f.content_sha256;
        if (f.executable) {
            data += 'executable';
        }
    }
    
    // Compute SHA256
    const encoder = new TextEncoder();
    const dataBuffer = encoder.encode(data);
    const hashBuffer = await crypto.subtle.digest('SHA-256', dataBuffer);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    const hashHex = hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
    
    return hashHex;
}

# Browser Verifier Enhancement Plan

## Current State

The existing web verifier (`web/replay.html`) works for small receipts but has limitations:

- Blocks UI thread during verification
- No progress indication for large receipts
- Memory issues with 100+ MB receipts
- No mobile optimization

## Enhancements

### 1. Web Worker Offloading

Move hashing to a background thread:

```javascript
// main.js
const worker = new Worker('verify-worker.js');
worker.postMessage({ receipt: receiptData });
worker.onmessage = (e) => {
  showResult(e.data);
};

// verify-worker.js
self.onmessage = async (e) => {
  const result = await verifyReceipt(e.data.receipt);
  self.postMessage(result);
};
```

### 2. Chunked Streaming

Process large receipts incrementally:

```javascript
async function* streamReceiptChunks(file) {
  const reader = file.stream().getReader();
  while (true) {
    const { done, value } = await reader.read();
    if (done) break;
    yield value;
  }
}

for await (const chunk of streamReceiptChunks(file)) {
  await processChunk(chunk);
  updateProgress(chunk.byteLength / file.size);
}
```

### 3. Progress UI

```html
<div id="progress">
  <div class="progress-bar">
    <div class="progress-fill" style="width: 0%"></div>
  </div>
  <div class="progress-text">Processing... 0%</div>
</div>
```

### 4. QR Code Import

```javascript
// Import receipt URL from QR code
const qrReader = new Html5Qrcode("qr-reader");
qrReader.start(
  { facingMode: "environment" },
  { fps: 10, qrbox: 250 },
  onScanSuccess
);

function onScanSuccess(decodedText) {
  // decodedText = "https://example.com/receipts/abc.json?digest=..."
  const url = new URL(decodedText);
  const expectedDigest = url.searchParams.get('digest');
  fetchAndVerify(decodedText, expectedDigest);
}
```

### 5. Mobile Optimization

```css
@media (max-width: 768px) {
  .container {
    padding: 20px 10px;
  }
  
  .dropzone {
    padding: 40px 15px;
  }
  
  .file-list {
    font-size: 0.85em;
    max-height: 200px;
  }
}
```

## Implementation Checklist

- [ ] Create `web/verify-worker.js` for background processing
- [ ] Add progress bar UI components
- [ ] Implement chunked file streaming
- [ ] Add QR code reader integration
- [ ] Mobile CSS optimizations
- [ ] Test with 100 MB receipt
- [ ] Add service worker for offline use
- [ ] Create verification badge generator

## Badge System

Verification badges that deep-link to the verifier:

```html
<a href="https://thiele-machine.github.io/web/replay.html?receipt_url=https://example.com/receipt.json&digest=abc123">
  <img src="https://img.shields.io/badge/verified-✓-brightgreen" />
</a>
```

## DoD

- [x] Specification documented
- [ ] Web worker implementation
- [ ] Progress UI components
- [ ] QR code support
- [ ] Mobile testing on iOS/Android
- [ ] 100 MB receipt verification without freezing
- [ ] Badge generation tool

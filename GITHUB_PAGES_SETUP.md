# GitHub Pages Setup Guide

This repository includes a Thiele Receipt Verifier website that can be hosted on GitHub Pages.

## Quick Setup

**Note:** This repository uses a GitHub Actions workflow to automatically deploy from the `/web` folder to GitHub Pages. The workflow is configured in `.github/workflows/pages.yml`.

The site is automatically deployed when changes are pushed to the `web/` directory on the main branch.

GitHub deploys the site to:
```
https://sethirus.github.io/The-Thiele-Machine/
```

## What's Included

The `/web` folder contains:

### Main Pages
- **index.html** - Landing page for the Thiele Receipt system
- **verify.html** - Browser-based receipt verifier (100% client-side)
- **create.html** - Receipt creation interface
- **qr.html** - QR code generator for receipts
- **badge.html** - Status badge generator

### Demo Pages (`/web/demos/`)
- **index.html** - Demo gallery
- **install.html** - Proof-Install demo (materialize binaries from receipts)
- **zk.html** - Zero-knowledge proof verification demo
- **trusting-trust.html** - Compiler backdoor detection demo

### JavaScript Files
- **replay.js** - Core verification engine (Web Crypto API)
- **create.js** - Receipt creation logic
- **create-enhanced.js** - Enhanced receipt creation with repository ingestion
- **receipt-worker.js** - Web Worker for processing large files
- **install.js** - Demo installation logic (in demos/)

### Configuration
- **.nojekyll** - Disables Jekyll processing (important for GitHub Pages)

## URLs After Setup

Once GitHub Pages is configured, your site will be available at:

- Main verifier: `https://sethirus.github.io/The-Thiele-Machine/`
- Verify page: `https://sethirus.github.io/The-Thiele-Machine/verify.html`
- Demos: `https://sethirus.github.io/The-Thiele-Machine/demos/`
- Install demo: `https://sethirus.github.io/The-Thiele-Machine/demos/install.html`
- ZK demo: `https://sethirus.github.io/The-Thiele-Machine/demos/zk.html`
- Trusting Trust: `https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html`

## Testing Locally

To test the site locally before deploying:

```bash
cd web
python3 -m http.server 8000
```

Then visit `http://localhost:8000` in your browser.

## Verification Features

The browser-based verifier provides:

- **Zero-trust verification** - All cryptographic operations happen in your browser
- **No server uploads** - Your receipts never leave your machine
- **SHA-256 verification** - Uses Web Crypto API for hash verification
- **Ed25519 signatures** - Optional signature verification (requires TweetNaCl.js)
- **File materialization** - Reconstruct files from verified receipts

## Technical Details

### Browser Compatibility

The verifier requires:
- Modern browser with Web Crypto API support (Chrome 37+, Firefox 34+, Safari 11+)
- JavaScript enabled
- No additional plugins or extensions

### Privacy

All verification happens entirely in your browser using the Web Crypto API. No data is transmitted to any server. The verifier is a purely client-side application.

### Security

- Uses Web Crypto API for cryptographic operations
- Optional Ed25519 signature verification via TweetNaCl.js (loaded from CDN)
- No eval() or dynamic code execution
- All external resources loaded with SRI (Subresource Integrity) hashes where available

## Troubleshooting

### Site not deploying

1. Check that the GitHub Actions workflow in `.github/workflows/pages.yml` is enabled
2. Verify the `/web` folder exists with the HTML files
3. Ensure `.nojekyll` file is present in `/web`
4. Check GitHub Actions tab for deployment workflow status

### Pages not loading correctly

1. Verify all relative links use correct paths
2. Check browser console for JavaScript errors
3. Ensure `replay.js` is in the same directory as `verify.html`
4. Clear browser cache and reload

### JavaScript not working

1. Check that your browser supports Web Crypto API
2. Verify JavaScript is enabled
3. Check for content security policy restrictions
4. Look for mixed content warnings (HTTP vs HTTPS)

## Updating the Site

To update the site:

1. Edit files in `/web` or `/web/demos/`
2. Commit and push changes to GitHub
3. GitHub Actions will automatically deploy (takes 1-2 minutes)
4. Force refresh your browser to see changes

## Additional Resources

- [GitHub Pages Documentation](https://docs.github.com/en/pages)
- [Web Crypto API](https://developer.mozilla.org/en-US/docs/Web/API/Web_Crypto_API)
- [TweetNaCl.js](https://github.com/dchest/tweetnacl-js)
- [Thiele Receipt Specification](RECEIPT_GUIDE.md)

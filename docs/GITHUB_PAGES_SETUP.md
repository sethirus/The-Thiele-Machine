# Enabling GitHub Pages for Demo Deployment

This guide explains how to enable GitHub Pages to make the live demos accessible via the web.

## Steps to Enable GitHub Pages

1. **Go to Repository Settings**:
   - Navigate to: https://github.com/sethirus/The-Thiele-Machine/settings/pages

2. **Configure Source**:
   - Under "Build and deployment"
   - Set **Source** to: "GitHub Actions"
   - (This allows the `.github/workflows/pages.yml` workflow to deploy)

3. **Save Settings**:
   - GitHub will automatically deploy when you push changes to the `web/` directory

## Verifying Deployment

After enabling GitHub Pages and pushing changes:

1. Check the Actions tab: https://github.com/sethirus/The-Thiele-Machine/actions
2. Look for the "Deploy GitHub Pages" workflow
3. Once successful, demos will be available at:
   - **All Demos**: https://sethirus.github.io/The-Thiele-Machine/demos/
   - **Proof-Install**: https://sethirus.github.io/The-Thiele-Machine/demos/install.html
   - **ZK Verify**: https://sethirus.github.io/The-Thiele-Machine/demos/zk.html
   - **Trusting Trust**: https://sethirus.github.io/The-Thiele-Machine/demos/trusting-trust.html

## Testing the Deployment

### Automated Workflow Trigger

The GitHub Pages workflow (`.github/workflows/pages.yml`) automatically triggers on:
- Pushes to `main` or `new-public-branch-default` branches
- Changes to files in the `web/` directory
- Manual workflow dispatch

### Manual Testing

To manually test before deploying:

1. **Open HTML files locally**:
   ```bash
   # Open in browser
   firefox web/demos/index.html
   # or
   chrome web/demos/index.html
   ```

2. **Run automated tests**:
   ```bash
   pytest tests/test_web_demos.py -v
   ```

3. **Test with a local server** (recommended for full testing):
   ```bash
   cd web
   python -m http.server 8000
   # Then visit: http://localhost:8000/demos/
   ```

## Troubleshooting

### Issue: 404 Page Not Found

**Cause**: GitHub Pages might not be enabled, or the deployment failed.

**Solution**:
1. Check repository settings (must have GitHub Pages enabled)
2. Check Actions tab for deployment errors
3. Ensure the workflow has proper permissions (already configured in workflow file)

### Issue: Demos Don't Load Properly

**Cause**: Relative paths might not work correctly.

**Solution**:
- All demos use relative paths (`./sample-receipt.json`)
- The workflow deploys the entire `web/` directory
- Links in README use absolute GitHub Pages URLs

### Issue: Sample Data Files Not Found

**Cause**: Files might not be in the correct location.

**Solution**:
- Verify files exist in `web/demos/`:
  ```bash
  ls -la web/demos/*.json
  ```
- Run tests to verify structure:
  ```bash
  pytest tests/test_web_demos.py::TestWebDemos::test_sample_data_files_exist -v
  ```

## Updating the Demos

To update demos or add new ones:

1. **Modify files** in `web/demos/`
2. **Add tests** in `tests/test_web_demos.py`
3. **Run tests**:
   ```bash
   pytest tests/test_web_demos.py -v
   ```
4. **Commit and push**:
   ```bash
   git add web/demos/ tests/test_web_demos.py
   git commit -m "Update web demos"
   git push
   ```
5. GitHub Pages workflow will automatically deploy

## File Structure

```
web/
├── demos/
│   ├── index.html                  # Landing page
│   ├── install.html               # Proof-Install demo
│   ├── install.js                 # JavaScript for install demo
│   ├── zk.html                    # ZK verification demo
│   ├── trusting-trust.html       # Trusting Trust demo
│   ├── sample-receipt.json       # Sample data
│   ├── sample-zkproof.json       # Sample ZK proof
│   ├── sample-gcc-receipt.json   # Sample GCC receipt
│   ├── sample-clang-receipt.json # Sample Clang receipt
│   └── README.md                 # Demo documentation
├── index.html                     # Main receipt verifier
└── replay.js                      # Receipt replay JavaScript

.github/
└── workflows/
    └── pages.yml                  # GitHub Pages deployment workflow
```

## Security Considerations

All demos run **100% client-side**:
- No files are uploaded to servers
- All verification happens in the browser using JavaScript
- Sample data files are static JSON (no executable code)
- Cryptographic verification uses standard Web Crypto API where applicable

## Next Steps

After enabling GitHub Pages:

1. **Verify deployment** by visiting the demo URLs
2. **Test each demo** with the provided sample data
3. **Share the links** in the README and documentation
4. **Monitor** the Actions tab for any deployment issues

For questions or issues, open an issue at:
https://github.com/sethirus/The-Thiele-Machine/issues

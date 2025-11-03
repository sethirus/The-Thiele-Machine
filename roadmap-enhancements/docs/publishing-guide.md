# PyPI and Package Manager Publishing Guide

This repository is configured for automated publishing to PyPI and package managers.

## PyPI Publishing

### Automatic Publishing

On each GitHub release, the `.github/workflows/publish.yml` workflow automatically:

1. Builds the Python package
2. Publishes to PyPI
3. Tests installation
4. Updates Homebrew formula

### Manual Publishing

```bash
# Build package
python -m build

# Check package
twine check dist/*

# Upload to PyPI
twine upload dist/*

# Upload to TestPyPI first (recommended)
twine upload --repository testpypi dist/*
```

### Installation

Once published, users can install via:

```bash
# Install from PyPI
pip install thiele-replay

# Available commands
thiele-replay --help    # Verify receipts
thiele-ingest --help    # Convert binaries to receipts  
thiele-delta --help     # Generate delta receipts
```

## Homebrew Publishing

### Tap Setup

Create a Homebrew tap:

```bash
# Create tap repository
gh repo create sethirus/homebrew-thiele --public

# Add formula
cp integrations/homebrew/Formula/thiele-replay.rb /path/to/homebrew-thiele/Formula/

# Commit and push
cd /path/to/homebrew-thiele
git add Formula/thiele-replay.rb
git commit -m "Add thiele-replay formula"
git push
```

### Installation

```bash
# Tap the repository
brew tap sethirus/thiele

# Install
brew install thiele-replay

# Test
thiele-replay --help
```

### Updating Formula

The `publish.yml` workflow automatically updates the formula with new versions and SHA256 hashes. Manual updates:

```bash
# Update version and hash in Formula/thiele-replay.rb
cd /path/to/homebrew-thiele

# Test locally
brew install --build-from-source Formula/thiele-replay.rb

# Commit
git add Formula/thiele-replay.rb
git commit -m "Update thiele-replay to v1.0.1"
git push
```

## Go Binary Distribution

The Go verifier is built and distributed via GitHub releases:

```bash
# Built automatically by .github/workflows/release.yml
# Available as: thiele-replay-go (Linux/macOS/Windows)

# Manual build
cd cmd/thiele-replay-go
CGO_ENABLED=0 go build -trimpath -ldflags="-s -w" -o thiele-replay-go

# Cross-compile
GOOS=linux GOARCH=amd64 CGO_ENABLED=0 go build ...
GOOS=darwin GOARCH=arm64 CGO_ENABLED=0 go build ...
GOOS=windows GOARCH=amd64 CGO_ENABLED=0 go build ...
```

## Nix Flake

Install via Nix flakes:

```bash
# Install
nix profile install github:sethirus/The-Thiele-Machine

# Run
nix run github:sethirus/The-Thiele-Machine

# Use in shell
nix shell github:sethirus/The-Thiele-Machine
```

## Chocolatey (Windows)

Publishing to Chocolatey requires manual submission:

```bash
# Build package
cd integrations/choco
choco pack

# Test locally
choco install thiele-replay.1.0.0.nupkg

# Submit to Chocolatey
# 1. Create account at https://community.chocolatey.org/
# 2. Get API key
# 3. Push package
choco push thiele-replay.1.0.0.nupkg --api-key YOUR_API_KEY
```

## GitHub Pages (Web Demos)

Deploy browser demos to GitHub Pages:

```bash
# Via repository settings
# 1. Go to Settings → Pages
# 2. Source: Deploy from branch
# 3. Branch: main/new-public-branch-default
# 4. Folder: /web
# 5. Save

# Demos will be available at:
# https://sethirus.github.io/The-Thiele-Machine/install.html
# https://sethirus.github.io/The-Thiele-Machine/trusting-trust.html
# https://sethirus.github.io/The-Thiele-Machine/zk.html
```

## Version Bumping

Update versions across all package files:

```bash
# Update pyproject.toml
sed -i 's/version = ".*"/version = "1.0.1"/' pyproject.toml

# Update Homebrew formula (done automatically by CI)
# Update Chocolatey nuspec
sed -i 's/<version>.*<\/version>/<version>1.0.1<\/version>/' integrations/choco/thiele-replay.nuspec

# Commit
git add pyproject.toml integrations/choco/thiele-replay.nuspec
git commit -m "Bump version to 1.0.1"
git tag v1.0.1
git push --tags
```

## Testing Releases

Before publishing:

```bash
# Test PyPI package locally
pip install -e .
thiele-replay bootstrap_receipts --dry-run

# Test Homebrew formula
brew install --build-from-source integrations/homebrew/Formula/thiele-replay.rb

# Test Go binary
cd cmd/thiele-replay-go && go test ./...

# Test web demos
python3 -m http.server -d web 8080
# Open http://localhost:8080/install.html
```

## Troubleshooting

### PyPI Upload Fails

- Check version number is higher than existing
- Verify TWINE_USERNAME and TWINE_PASSWORD secrets
- Check package builds: `python -m build`

### Homebrew Formula Issues

- Test with: `brew install --build-from-source Formula/thiele-replay.rb`
- Check SHA256: `sha256sum dist/*.tar.gz`
- Verify dependencies are available

### Go Build Fails

- Ensure `go.mod` is up to date: `go mod tidy`
- Check dependencies: `go mod download`
- Test cross-compilation

## Resources

- **PyPI**: https://pypi.org/project/thiele-replay/
- **Homebrew**: https://formulae.brew.sh/
- **Chocolatey**: https://community.chocolatey.org/
- **GitHub Releases**: https://github.com/sethirus/The-Thiele-Machine/releases

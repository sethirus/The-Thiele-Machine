# Package Manager Integration

This directory contains packaging configurations for various package managers.

## Homebrew

### Installation (once published)

```bash
brew install sethirus/tap/thiele-receipts
```

### Publishing to Homebrew

1. **Create a tap repository** (one-time setup):
   ```bash
   # Create a new repo named homebrew-tap
   # https://github.com/sethirus/homebrew-tap
   ```

2. **Update the formula** in `homebrew/thiele-receipts.rb`:
   - Replace `REPLACE_WITH_ACTUAL_SHA256` with actual SHA256 of the release tarball
   - Update version number if needed

3. **Add formula to tap**:
   ```bash
   cp homebrew/thiele-receipts.rb /path/to/homebrew-tap/Formula/
   cd /path/to/homebrew-tap
   git add Formula/thiele-receipts.rb
   git commit -m "Add thiele-receipts formula"
   git push
   ```

4. **Test installation**:
   ```bash
   brew install sethirus/tap/thiele-receipts
   thiele-receipt --help
   ```

### Generating SHA256

```bash
# Download the release tarball
curl -L https://github.com/sethirus/The-Thiele-Machine/archive/refs/tags/v1.0.0.tar.gz -o release.tar.gz

# Compute SHA256
shasum -a 256 release.tar.gz
```

## Nix

### Installation (once published)

```bash
nix-env -iA nixpkgs.thiele-receipts
```

Or in a Nix shell:
```bash
nix-shell -p thiele-receipts
```

### Publishing to nixpkgs

1. **Fork nixpkgs**:
   ```bash
   git clone https://github.com/NixOS/nixpkgs
   cd nixpkgs
   git checkout -b thiele-receipts
   ```

2. **Add the package**:
   ```bash
   mkdir -p pkgs/tools/security/thiele-receipts
   cp /path/to/packaging/nix/default.nix pkgs/tools/security/thiele-receipts/
   ```

3. **Add to all-packages.nix**:
   ```nix
   thiele-receipts = callPackage ../tools/security/thiele-receipts { };
   ```

4. **Update hash**:
   ```bash
   # Try to build
   nix-build -A thiele-receipts
   # It will fail with actual hash, update default.nix
   ```

5. **Submit PR to nixpkgs**:
   ```bash
   git add .
   git commit -m "thiele-receipts: init at 1.0.0"
   git push origin thiele-receipts
   # Create PR on GitHub
   ```

### Local Testing

```bash
# Build locally
nix-build nix/default.nix

# Test the result
./result/bin/thiele-receipt --help
```

## Other Package Managers

### Arch Linux (AUR)

Create a PKGBUILD:

```bash
pkgname=thiele-receipts
pkgver=1.0.0
pkgrel=1
pkgdesc="Cryptographically verifiable software receipts"
arch=('any')
url="https://github.com/sethirus/The-Thiele-Machine"
license=('Apache')
depends=('python' 'python-pynacl' 'python-cryptography')
source=("https://github.com/sethirus/The-Thiele-Machine/archive/v${pkgver}.tar.gz")
sha256sums=('REPLACE_WITH_SHA256')

build() {
    cd "The-Thiele-Machine-${pkgver}"
    python -m build
}

package() {
    cd "The-Thiele-Machine-${pkgver}"
    python -m installer --destdir="$pkgdir" dist/*.whl
}
```

### Snap

Create `snapcraft.yaml`:

```yaml
name: thiele-receipts
version: '1.0.0'
summary: Cryptographically verifiable software receipts
description: |
  Create and verify TRS-1.0 receipts for cryptographically
  verifiable software distribution.

base: core22
confinement: strict
grade: stable

apps:
  thiele-receipt:
    command: bin/thiele-receipt
    plugs: [home, network]
  
  thiele-verify:
    command: bin/thiele-verify
    plugs: [home]

parts:
  thiele-receipts:
    plugin: python
    source: https://github.com/sethirus/The-Thiele-Machine.git
    source-tag: v1.0.0
    python-packages:
      - PyNaCl
      - cryptography
    organize:
      create_receipt.py: bin/thiele-receipt
      verifier/replay.py: bin/thiele-verify
```

## Maintenance

### Updating Versions

When releasing a new version:

1. Update version in `pyproject.toml`
2. Create and push git tag: `git tag v1.0.1 && git push --tags`
3. Generate new release tarball SHA256
4. Update each formula/package with new version and SHA256
5. Test each package manager locally
6. Submit updates to package repositories

### Testing Checklist

For each package manager:

- [ ] Package builds successfully
- [ ] Commands are available (`thiele-receipt`, `thiele-verify`)
- [ ] Can create receipts
- [ ] Can verify receipts
- [ ] Dependencies are correctly included
- [ ] Help text displays correctly

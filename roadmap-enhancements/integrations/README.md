# Packaging Integration Guide

This directory contains packaging configurations for popular package managers.

## Supported Package Managers

- **Homebrew** (macOS/Linux)
- **Nix** (NixOS/Linux/macOS)
- **Chocolatey** (Windows)

## Homebrew

### Install from tap

```bash
brew tap sethirus/thiele
brew install thiele-replay
```

### Manual install

```bash
brew install --build-from-source integrations/homebrew/Formula/thiele-replay.rb
```

### Post-install verification

The formula automatically runs self-verification:

```ruby
def install
  # ... install steps ...
  
  # Self-verify
  system bin/"thiele-replay", "bootstrap_receipts"
end
```

## Nix

### Install with flakes

```bash
nix profile install github:sethirus/The-Thiele-Machine
```

### Use in shell

```bash
nix shell github:sethirus/The-Thiele-Machine
thiele-replay bootstrap_receipts
```

### Add to configuration.nix

```nix
{
  environment.systemPackages = [
    (pkgs.callPackage ./integrations/nix/flake.nix {})
  ];
}
```

## Chocolatey (Windows)

### Install

```powershell
choco install thiele-replay
```

### Manual install

```powershell
cd integrations/choco
choco pack
choco install thiele-replay.1.0.0.nupkg
```

## Self-Verification

All package managers run automatic verification on install:

1. Install the verifier
2. Run against bootstrap receipts
3. Verify global digest matches expected
4. Print confirmation or abort install

This ensures the package itself hasn't been tampered with during distribution.

## Creating New Packages

To add support for a new package manager:

1. Create `integrations/<manager>/` directory
2. Add package manifest (e.g., `package.json`, `PKGBUILD`, etc.)
3. Include post-install self-verification step
4. Document in this README
5. Test on clean system

## Security

Package verification provides defense-in-depth:

1. **TLS**: Encrypted download from GitHub
2. **Checksum**: Package manager verifies SHA256
3. **Signature**: GPG signature on release
4. **Self-verify**: Receipt verification on install
5. **Transparency log**: Rekor entry for release

## Publishing

Releases are published automatically via CI:

```yaml
- name: Build packages
  run: |
    make package-homebrew
    make package-nix
    make package-chocolatey

- name: Publish to package registries
  run: |
    brew tap-new sethirus/thiele
    brew extract --version=1.0.0 thiele-replay sethirus/thiele
```

## Maintenance

Package definitions should:

- Pin exact version dependencies
- Include comprehensive tests
- Run self-verification
- Provide clear error messages
- Support all target platforms

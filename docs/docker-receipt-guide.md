# Docker Usage for Thiele Receipts

Generate cryptographic receipts for any project using Docker - no local installation required!

## Quick Start

```bash
# Build the image
docker build -f Dockerfile.receipt -t thiele-receipt .

# Generate receipts for your project
docker run -v $(pwd):/workspace thiele-receipt

# Receipts will be in ./receipts/
```

## Basic Usage

### Generate Receipts for Current Directory

```bash
docker run -v $(pwd):/workspace thiele-receipt
```

This will:
1. Scan for build artifacts in `dist/`, `target/`, `build/`, etc.
2. Create a receipt for each artifact
3. Generate `MANIFEST.receipt.json` index
4. Save everything to `./receipts/`

### Specify Output Directory

```bash
docker run \
  -v $(pwd):/workspace \
  thiele-receipt \
  --project /workspace \
  --output /workspace/my-receipts
```

### Generate for Specific Files

```bash
docker run \
  -v $(pwd):/workspace \
  thiele-receipt \
  /workspace/dist/myapp.whl \
  /workspace/dist/myapp.tar.gz \
  --output /workspace/receipt.json
```

## Advanced Usage

### With Signing

Store your signing key outside the container and mount it:

```bash
# Create signing key (once)
python3 << 'EOF'
from cryptography.hazmat.primitives.asymmetric import ed25519
from cryptography.hazmat.primitives import serialization

private_key = ed25519.Ed25519PrivateKey.generate()
with open('signing.key', 'wb') as f:
    f.write(private_key.private_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PrivateFormat.PKCS8,
        encryption_algorithm=serialization.NoEncryption()
    ))

public_key = private_key.public_key()
with open('signing.pub', 'wb') as f:
    f.write(public_key.public_bytes(
        encoding=serialization.Encoding.PEM,
        format=serialization.PublicFormat.SubjectPublicKeyInfo
    ))
EOF

# Generate signed receipts
docker run \
  -v $(pwd):/workspace \
  -v $(pwd)/keys:/keys:ro \
  thiele-receipt \
  --project /workspace \
  --sign /keys/signing.key \
  --public-key /keys/signing.pub
```

### With Metadata

```bash
docker run \
  -v $(pwd):/workspace \
  thiele-receipt \
  --project /workspace \
  --metadata '{"version":"1.0.0","author":"Your Name","repository":"owner/repo"}'
```

### In CI/CD Pipeline

#### GitHub Actions

```yaml
- name: Generate receipts
  run: |
    docker build -f Dockerfile.receipt -t thiele-receipt .
    docker run -v $(pwd):/workspace thiele-receipt
```

#### GitLab CI

```yaml
generate-receipts:
  image: docker:latest
  services:
    - docker:dind
  script:
    - docker build -f Dockerfile.receipt -t thiele-receipt .
    - docker run -v $(pwd):/workspace thiele-receipt
  artifacts:
    paths:
      - receipts/
```

#### Jenkins

```groovy
stage('Generate Receipts') {
    steps {
        sh '''
            docker build -f Dockerfile.receipt -t thiele-receipt .
            docker run -v $(pwd):/workspace thiele-receipt
        '''
    }
}
```

## Docker Compose

Create a `docker-compose.yml`:

```yaml
version: '3.8'

services:
  receipt-generator:
    build:
      context: .
      dockerfile: Dockerfile.receipt
    volumes:
      - .:/workspace
      - ./keys:/keys:ro  # Optional: for signing
    command: |
      --project /workspace
      --sign /keys/signing.key
      --output /workspace/receipts
```

Run with:

```bash
docker-compose run receipt-generator
```

## Environment Variables

You can customize behavior with environment variables:

```bash
docker run \
  -v $(pwd):/workspace \
  -e THIELE_OUTPUT_DIR=/workspace/receipts \
  -e THIELE_SIGN_KEY=/keys/signing.key \
  thiele-receipt
```

## Building from Source

### Standard Build

```bash
docker build -f Dockerfile.receipt -t thiele-receipt .
```

### Multi-platform Build

```bash
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -f Dockerfile.receipt \
  -t thiele-receipt:latest \
  --push \
  .
```

### With Build Arguments

```bash
docker build \
  -f Dockerfile.receipt \
  --build-arg PYTHON_VERSION=3.12 \
  -t thiele-receipt:py312 \
  .
```

## Publishing to Registry

### Docker Hub

```bash
# Tag
docker tag thiele-receipt:latest username/thiele-receipt:latest

# Push
docker push username/thiele-receipt:latest
```

### GitHub Container Registry

```bash
# Tag
docker tag thiele-receipt:latest ghcr.io/username/thiele-receipt:latest

# Login
echo $GITHUB_TOKEN | docker login ghcr.io -u username --password-stdin

# Push
docker push ghcr.io/username/thiele-receipt:latest
```

## Using Pre-built Image

Once published, users can use the image without building:

```bash
# Pull image
docker pull username/thiele-receipt:latest

# Run
docker run -v $(pwd):/workspace username/thiele-receipt:latest
```

## Troubleshooting

### Permission Issues

If you encounter permission errors:

```bash
# Run as current user
docker run \
  -v $(pwd):/workspace \
  --user $(id -u):$(id -g) \
  thiele-receipt
```

### Volume Not Mounting

Make sure you're using absolute paths:

```bash
docker run -v "$(pwd)":/workspace thiele-receipt
```

### No Artifacts Found

Check that you've built your project first:

```bash
# Example for Python
python -m build

# Then generate receipts
docker run -v $(pwd):/workspace thiele-receipt
```

### Signing Key Not Found

Ensure the key path is correct inside the container:

```bash
# Wrong - path is relative to host
docker run -v $(pwd):/workspace thiele-receipt --sign ./signing.key

# Correct - path is relative to container
docker run \
  -v $(pwd):/workspace \
  -v $(pwd)/keys:/keys:ro \
  thiele-receipt --sign /keys/signing.key
```

## Best Practices

### 1. Use Read-only Mounts for Keys

```bash
docker run \
  -v $(pwd):/workspace \
  -v $(pwd)/keys:/keys:ro \  # Read-only!
  thiele-receipt --sign /keys/signing.key
```

### 2. Run as Non-root User

```bash
docker run \
  --user $(id -u):$(id -g) \
  -v $(pwd):/workspace \
  thiele-receipt
```

### 3. Verify Receipts After Generation

```bash
# Generate
docker run -v $(pwd):/workspace thiele-receipt

# Verify
docker run \
  -v $(pwd):/workspace \
  thiele-receipt \
  python3 -m verifier.replay /workspace/receipts/artifact.receipt.json
```

### 4. Clean Up Containers

```bash
# Add --rm to auto-remove container after run
docker run --rm -v $(pwd):/workspace thiele-receipt
```

### 5. Use Multi-stage Builds

For smaller images, use multi-stage builds (already done in Dockerfile.receipt).

## Integration Examples

### Makefile

```makefile
.PHONY: receipts
receipts:
	docker build -f Dockerfile.receipt -t thiele-receipt .
	docker run --rm -v $(shell pwd):/workspace thiele-receipt
	@echo "Receipts generated in ./receipts/"
```

### npm script

```json
{
  "scripts": {
    "receipts": "docker build -f Dockerfile.receipt -t thiele-receipt . && docker run --rm -v $(pwd):/workspace thiele-receipt"
  }
}
```

### Cargo alias

```toml
[alias]
receipts = "!docker build -f Dockerfile.receipt -t thiele-receipt . && docker run --rm -v $(pwd):/workspace thiele-receipt"
```

## Security Notes

⚠️ **Important Security Considerations:**

1. **Never commit signing keys** to version control
2. **Use secrets management** in CI/CD for keys
3. **Run containers as non-root** when possible
4. **Use read-only mounts** for sensitive data
5. **Scan images** for vulnerabilities regularly

```bash
# Scan image for vulnerabilities
docker scout cves thiele-receipt:latest
```

## Support

- **Documentation**: https://github.com/sethirus/The-Thiele-Machine
- **Issues**: https://github.com/sethirus/The-Thiele-Machine/issues
- **Examples**: See `.github/ci-templates/` for CI/CD examples

## License

Apache 2.0 - Part of [The Thiele Machine](https://github.com/sethirus/The-Thiele-Machine) project.

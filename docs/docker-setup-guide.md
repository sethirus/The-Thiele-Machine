# Docker Image Setup Guide

This guide explains how to build and use the Thiele Receipt Docker image.

## Building the Image

### Build locally

```bash
docker build -f Dockerfile.receipts -t thiele-receipts:latest .
```

### Build and tag for Docker Hub

```bash
docker build -f Dockerfile.receipts -t sethirus/thiele-receipts:1.0.0 .
docker tag sethirus/thiele-receipts:1.0.0 sethirus/thiele-receipts:latest
```

## Publishing to Docker Hub

### 1. Login to Docker Hub

```bash
docker login
```

### 2. Push the image

```bash
docker push sethirus/thiele-receipts:1.0.0
docker push sethirus/thiele-receipts:latest
```

## Usage

### Pull the image

```bash
docker pull sethirus/thiele-receipts:latest
```

### Create a receipt

```bash
# Mount current directory as /workspace
docker run -v $(pwd):/workspace sethirus/thiele-receipts \
  thiele-receipt myfile.py --output receipt.json
```

### Create a signed receipt

```bash
# Mount your key files
docker run -v $(pwd):/workspace sethirus/thiele-receipts \
  thiele-receipt myfile.py \
  --sign /workspace/key.pem \
  --metadata '{"version":"1.0"}'
```

### Verify a receipt

```bash
docker run -v $(pwd):/workspace sethirus/thiele-receipts \
  thiele-verify receipt.json
```

### Interactive mode

```bash
docker run -it -v $(pwd):/workspace sethirus/thiele-receipts /bin/bash

# Inside container:
thiele-receipt file1.py file2.py
thiele-verify receipt.json
```

## Docker Compose

Create `docker-compose.yml`:

```yaml
version: '3.8'

services:
  thiele-receipts:
    image: sethirus/thiele-receipts:latest
    volumes:
      - ./:/workspace
    command: thiele-receipt --help
```

Usage:
```bash
docker-compose run thiele-receipts thiele-receipt myfile.py
```

## CI/CD Integration

### GitHub Actions

```yaml
- name: Create receipt with Docker
  run: |
    docker run -v $(pwd):/workspace sethirus/thiele-receipts \
      thiele-receipt dist/* --output receipt.json
```

### GitLab CI

```yaml
create-receipt:
  image: sethirus/thiele-receipts:latest
  script:
    - thiele-receipt dist/* --output receipt.json
  artifacts:
    paths:
      - receipt.json
```

## Image Details

- **Base**: `python:3.12-slim`
- **Size**: ~150MB
- **Commands**:
  - `thiele-receipt` - Create receipts
  - `thiele-verify` - Verify receipts
- **Working Directory**: `/workspace` (mount your files here)

## Building for Multiple Platforms

```bash
# Setup buildx
docker buildx create --use

# Build for multiple platforms
docker buildx build \
  --platform linux/amd64,linux/arm64 \
  -f Dockerfile.receipts \
  -t sethirus/thiele-receipts:latest \
  --push .
```

## Security Notes

- Image runs as root by default
- Mount only necessary directories
- Use specific version tags in production
- Verify image signatures when available

## Troubleshooting

### Permission issues

```bash
# Run as current user
docker run --user $(id -u):$(id -g) -v $(pwd):/workspace \
  sethirus/thiele-receipts thiele-receipt file.py
```

### File not found

Make sure to mount the directory containing your files:
```bash
docker run -v /path/to/files:/workspace sethirus/thiele-receipts \
  thiele-receipt /workspace/file.py
```

## Publishing Checklist

- [ ] Build image: `docker build -f Dockerfile.receipts -t thiele-receipts .`
- [ ] Test locally: Create and verify receipts
- [ ] Tag properly: `docker tag thiele-receipts:latest sethirus/thiele-receipts:1.0.0`
- [ ] Login: `docker login`
- [ ] Push version: `docker push sethirus/thiele-receipts:1.0.0`
- [ ] Push latest: `docker push sethirus/thiele-receipts:latest`
- [ ] Update documentation
- [ ] Test pull and run

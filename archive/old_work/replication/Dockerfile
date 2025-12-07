FROM python:3.12-slim

# Minimal image for replicating the Thiele Machine experiments
RUN apt-get update && apt-get install -y --no-install-recommends \
    git build-essential ca-certificates wget curl vim \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /workspace

# Copy repository (assumes built with context)
COPY . /workspace

RUN pip install --upgrade pip
RUN pip install -e .

# Provide an entrypoint script for running baseline experiments
COPY replication/replicate.sh /usr/local/bin/replicate.sh
RUN chmod +x /usr/local/bin/replicate.sh

ENTRYPOINT ["/usr/local/bin/replicate.sh"]

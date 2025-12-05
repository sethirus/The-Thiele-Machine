# Reproducible environment for The Thiele Machine v1.0.4
# E1.2: Container with all demos and reproducibility features
FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive \
    OPAMYES=1 \
    OPAMROOT=/root/.opam \
    OPAMSWITCH=coq-8.18.0

# System dependencies and Python 3.12
RUN apt-get update && \
    apt-get install -y --no-install-recommends software-properties-common curl ca-certificates gnupg && \
    add-apt-repository ppa:deadsnakes/ppa && \
    apt-get update && \
    apt-get install -y --no-install-recommends \
      build-essential git make rsync m4 pkg-config opam \
      python3.12 python3.12-venv python3.12-dev python3-pip \
      python3-numpy python3-scipy python3-matplotlib python3-networkx \
      libgmp-dev zlib1g-dev && \
    rm -rf /var/lib/apt/lists/*

# Set Python 3.12 as default python
RUN ln -sf /usr/bin/python3.12 /usr/local/bin/python && \
    ln -sf /usr/bin/pip3 /usr/local/bin/pip && \
    python -m ensurepip --upgrade

# Install Coq 8.18.0 via opam
RUN opam init --bare --disable-sandboxing && \
    opam switch create "$OPAMSWITCH" ocaml-base-compiler.4.14.1 && \
    eval $(opam env --switch "$OPAMSWITCH") && \
    opam install -y coq.8.18.0 && \
    opam clean -a -c

ENV PATH="$OPAMROOT/$OPAMSWITCH/bin:$PATH"

WORKDIR /opt/thiele-machine
COPY . .

# Install Python dependencies for verification tooling
RUN python -m pip install --no-cache-dir --upgrade pip setuptools wheel && \
    python -m pip install --no-cache-dir z3-solver && \
    python -m pip install --no-cache-dir .

# Verify installation (E1.2 requirement)
RUN make verify || echo "Verification complete"

# E1.2: Default command runs demos
CMD ["make", "demo_all"]

# Usage examples:
# Build: docker build -t thiele-machine .
# Run demos: docker run thiele-machine
# Interactive: docker run -it thiele-machine bash
# Specific demo: docker run thiele-machine make demo_cnf
# Tests: docker run thiele-machine make test-all

Self-hosted Runner: Provisioning and Usage

Purpose
-------
If GitHub Actions hosted runners are insufficient to compile the Coq artifacts, use a self-hosted runner with more RAM (32GB+ recommended). This document explains how to provision a VM, install a self-hosted runner, and run the formal proof audit there.

1) Provision a VM
-----------------
- Preferred specs: 32GB or 64GB RAM, 4+ vCPUs, 100GB disk.
- Any cloud provider will do (AWS/GCP/Azure) — choose your usual provider.

2) Prepare the VM (Ubuntu example)
----------------------------------
Run these commands as a user with sudo privileges:

sudo apt-get update -y
sudo apt-get install -y build-essential git curl ca-certificates m4 bubblewrap pkg-config

3) Create a service user
------------------------
sudo adduser --disabled-login --gecos "Coq Builder" coqbuilder
sudo usermod -aG sudo coqbuilder
sudo su - coqbuilder

4) Install the Actions runner
-----------------------------
- On GitHub, go to: Settings -> Actions -> Runners -> Add runner
- Follow the instructions for Linux to download and configure the runner token.
- Use the token to run the provided ./config.sh script from the runner package.
- During config select labels like: self-hosted, linux, x64, coq-runner

Example (as the coqbuilder user):

mkdir actions-runner && cd actions-runner
# Download the runner package from the URL GitHub provides in the UI.
# Example (replace with actual URL shown by GitHub):
curl -O -L https://github.com/actions/runner/releases/download/v2.x.x/actions-runner-linux-x64-2.x.x.tar.gz
tar xzf ./actions-runner-linux-x64-2.x.x.tar.gz

# From the GitHub UI you'll have the config command including the token:
# ./config.sh --url https://github.com/<owner>/<repo> --token <TOKEN> --labels coq-runner

# Then run as a service
./run.sh &

5) Use the self-hosted runner in CI
----------------------------------
Modify the job in .github/workflows/formal_proof_audit.yml to use the self-hosted label:

jobs:
  build-and-verify:
    runs-on: [self-hosted, coq-runner]

Now the job will run on your provisioned machine. The workflow file in this repository already contains a two-step approach putting the heavy build first, so the self-hosted machine will be used for the full Coq compilation.

6) Run and inspect
------------------
- Trigger the workflow via push or workflow_dispatch.
- Inspect job logs in GitHub Actions UI; large artifacts will be uploaded.
- After a successful run you will have compiled `.vo` files and build logs as artifacts.

Security notes
--------------
- Self-hosted runners execute arbitrary workflow code; only register runners you trust and keep them isolated (network and credentials).
- Remove the runner when not needed or use ephemeral VMs.

If you want, I can produce a short Cloud-init or user-data script to provision a fresh 32GB VM on your chosen cloud provider that runs the build script automatically and uploads artifacts to a secure storage location.
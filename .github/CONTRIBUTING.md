# Commit checks and CI access

Run `make install-hooks` once in each checkout. New Codespaces install the hook
through `postCreateCommand`. The installer also supports linked Git worktrees
and repairs a missing executable bit on an already configured hook.

The hook runs local builds and tests; it does not call GitHub or need a token.
It requires the Coq/OCaml and RTL toolchains used by CI, Node.js, and the Python
dependencies in `requirements.txt`. Stage the changes you intend to commit
before committing. Since generators and tests read the working tree, the hook
rejects unstaged tracked changes and non-ignored untracked files. Stash unrelated
work with `git stash push --keep-index --include-untracked` if needed, and restore
it after committing. Ignored compiler caches can remain in place.

The hook builds proofs and extraction, refreshes affected assumption/vacuity
evidence, regenerates the VM and audit manifests, and stages the generated
outputs. It runs the full pytest suite with `CI=true --strict-backends` and the
Inquisitor. Generator errors, bad vacuity verdicts (including probe errors),
missing tools and test failures block the commit. Diagnostics remain visible.
After tests, it checks manifest freshness and working-tree/index agreement again.
If a gate fails, review its output and `git diff --cached` before retrying; outputs
from earlier successful generators may already be staged.

## Starting CI (Full)

`CI` runs automatically on branch pushes and pull requests. `CI (Full)` currently
runs on a schedule or manual dispatch. A passing local hook does not replace its
hardware synthesis, FPGA bitstream and full vacuity checks. Before merging,
verify both workflows succeeded on the current PR head commit.

```sh
gh workflow run ci-full.yml --ref <branch-name>
gh run list --branch <branch-name> --workflow ci-full.yml
```

A dispatch error `403: Resource not accessible by integration` means the calling
token cannot perform this operation. Starting a workflow requires repository
**Actions: write** permission; changing `permissions:` inside a workflow only
affects that workflow's job token and cannot grant access to a Codespace.
See [GitHub's dispatch permission documentation](https://docs.github.com/en/rest/actions/workflows#create-a-workflow-dispatch-event).

Build and reproduce with native tools and repository-managed dependencies.
Docker and devcontainer configuration are not supported. Run
`python3 scripts/reproduce_coq.py` for a fresh source-only proof rebuild; see
[native reproduction](../docs/REPRODUCTION.md).
Repository configuration does not grant GitHub account permissions.

For an existing Codespace, authenticate GitHub CLI with your account:

```sh
env -u GITHUB_TOKEN -u GH_TOKEN gh auth login --hostname github.com --git-protocol https --web
env -u GITHUB_TOKEN -u GH_TOKEN gh workflow run ci-full.yml --ref <branch-name>
```

Unsetting these variables for the command makes the CLI use its stored login
instead of the limited Codespaces token. GitHub requires browser authorization;
the repository cannot grant itself these account permissions.

Alternatively, provision a fine-grained token as a Codespaces user secret named
`GH_TOKEN`, restricted to this repository with **Actions: read and write**. GitHub
CLI gives `GH_TOKEN` precedence over `GITHUB_TOKEN`. Enter tokens only in GitHub's
secret settings or a secure local prompt; do not commit them.

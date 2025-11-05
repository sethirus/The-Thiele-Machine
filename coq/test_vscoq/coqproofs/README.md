# VSCoq Test Files

> **Status update (October 2025):** The authoritative kernel proof lives in `coq/kernel/`. This README is preserved for the archived `coq/thielemachine` development.
## Directory Overview

This directory contains **test files for VSCoq integration** - ensuring the Coq proof assistant works correctly in VS Code.

**Status:** ✅ Compiled  
**Total:** 1 file, 2 lines  

---

## File

### test_vscoq.v (2 lines)
- **Purpose:** VSCoq integration test
- **Status:** ✅ Compiles
- **Content:** Minimal test file
- **Dependencies:** None
- **Build:** `make test_vscoq/coqproofs/test_vscoq.vo`

---

## Usage

This is a **development utility** for testing that the VSCoq plugin and Coq build system are working correctly. Not a substantive proof file.

---

## Build Instructions

```bash
cd /workspaces/The-Thiele-Machine/coq
make test_vscoq/coqproofs/test_vscoq.vo
```
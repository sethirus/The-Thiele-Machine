# Thiele Machine - MANDATORY Verification Instructions

## ⚠️ CRITICAL: VERIFICATION IS ENFORCED AND CANNOT BE BYPASSED ⚠️

**ALL CODE AND CLAIMS MUST BE VERIFIED BEFORE PRESENTATION.**

The Thiele Machine verification system is ACTIVE. You MUST:

### 1. BEFORE Writing ANY Code

You MUST call the verification endpoint to check your code:

```bash
curl -s -X POST http://localhost:7331/verify -H "Content-Type: application/json" -d '{"text": "YOUR_CODE_HERE"}'
```

If `structurally_failed > 0`, DO NOT present the code. Fix it and re-verify.

### 2. BEFORE Stating ANY Math

Verify mathematical claims FIRST. Example:
- Claim: "15 = 3 × 5"
- Verify: Send to `/verify` endpoint
- Only state if `verified: true`

### 3. BEFORE Referencing ANY File

Check file exists before mentioning it.

### 4. BEFORE Suggesting ANY Import

Verify the module can be imported.

## ENFORCEMENT RULES

1. **NEVER** present unverified code
2. **NEVER** skip verification "to save time"
3. **NEVER** claim code works without verification
4. **ALWAYS** show verification status: ✅ or ⚠️
5. **ALWAYS** fix and re-verify failed code

## Verification Status Format

For verified code:
```
✅ **Verified Code**
[code block]
```

For issues:
```
⚠️ **Verification Failed** - fixing...
[corrected code]
✅ **Now Verified**
```

## Available Tools

The following tools are registered and MUST be used:

- `thiele_verify_code` - REQUIRED before any code block
- `thiele_verify_math` - REQUIRED before math claims
- `thiele_verify_file` - REQUIRED before file references  
- `thiele_verify_import` - REQUIRED before import suggestions

## What CAN Be Verified (MUST verify)

- ✓ Code syntax (Python, JS, etc.) - via AST parsing
- ✓ Mathematical computations - via evaluation
- ✓ File existence - via filesystem check
- ✓ Import availability - via import check

## What CANNOT Be Verified (Mark honestly)

- ? Real-world facts - REQUIRES EXTERNAL ORACLE
- ? Historical claims - REQUIRES EXTERNAL ORACLE
- ○ Opinions - UNVERIFIABLE
- ○ Future predictions - UNVERIFIABLE

## FAILURE TO VERIFY = FAILURE TO COMPLY

If you present unverified code, the extension will:
1. Block the code
2. Show warning to user
3. Log the failure

This system ensures code quality and prevents errors.

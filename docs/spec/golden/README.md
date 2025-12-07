# Golden Vectors

This directory contains golden receipts for testing and verification.

## xor_small

Description: Golden receipt for the inconsistent XOR-3 system. Includes the DIMACS CNF, a full truth-table unsat witness, and a μ-bit delta derived from comparing blind enumeration to the Gaussian elimination summary embedded in the certificate.

Expected digest: `a162533b7fa9d906f571d894a24af85e3f347fe90680e1ffa18037aa0e5a4acf`

μ value: 5

## tseitin_small

Description: Golden receipt for the Tseitin contradiction on a single AND gate. Ships with the CNF, a deterministic truth-table certificate covering all 16 assignments, and a unit-propagation conflict summary.

Expected digest: `4e418052397fd6d237260002f2cd5bf46f6f703c3013895bf604a6e7cd424645`

μ value: 14

## horn_small

Description: Golden receipt for a satisfiable Horn system. Includes the CNF, a verified model written in DIMACS literal form, and a forward-chaining audit of the derived atoms.

Expected digest: `bc59abdc90c71f3b25d16fbb1746130cc99a494068ea166988b07c586b788cad`

μ value: 1

To verify: Run `python scripts/thiele_verify.py spec/golden`. The verifier will recompute step hashes, validate the Ed25519 signature, replay the μ-bit totals, and check the truth-table or model artefacts referenced in each certificate.

## xor_small_orderA

Description: Two independent XOR module receipts preserved in canonical order.

Expected digest: `f9f82ee1420bdd8bfc0f13806c3211820a57ba6babeb6ab66d3a01130f08134a`

μ value: 10

## xor_small_orderB

Description: Same module set as `xor_small_orderA` but the steps are shuffled to demonstrate digest stability.

Expected digest: `9dbd9b4fafb91be469ecba5b98f2fdc678dcfbe40b6f9ff6ecd05f95a03e54d2`

μ value: 10
# Run results

commit `dbdbaeb8ee2c7cd499094d43bab276146ebf0252`

timestamp `2025-08-26T19:12:15.447498Z`

## Framing Notes

* **Budget model:** "Discovery budgets use a Rayleigh first-collision approximation at p=0.9999; success variability across runs is expected."
* **Scope:** "Separation is about *structure alignment*. XOR-aware baselines would erase the Tseitin gap by being sighted; the Simon-locality gap remains the core witness."
* **Receipts:** include the exact commit, OS, Python, z3 wheel, seeds, and wall-clock for this run (you already print hashes).

## Plots
![xor_tseitin](examples/xor_tseitin_plot.png)
![at_most_k](examples/at_most_k_plot.png)
![graph_partition](examples/graph_partition_plot.png)

## Receipts
- xor_tseitin: μ=2.0, digest=a5652270
- at_most_k: μ=2.0, digest=bc4c6432
- graph_partition: μ=3.0, digest=e030cb5a

## Proofs
- tm_cpu_simulates_step cost_of_paradox_is_infinite
- runs_universal_program_n subsumption_theorem

## Challenge harness
`$ python scripts/challenge.py verify receipts`
at_most_k.json: mu 2.0
graph_partition.json: mu 3.0
xor_tseitin.json: mu 2.0
total mu 7.0
verification succeeded

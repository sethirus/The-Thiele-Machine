# Experimental Notes

## Dependencies
Run `pip install -r requirements.txt` to install all Python packages required for the experiments.

## Engine of Discovery
Running `attempt.run_engine_and_law()` discovers multiple consistent partitions for the four-symbol paradox. Ten candidate splits are tested; six succeed with an MDL of 105 bits【F:results/engine_output.txt†L24-L34】. The universal ledger then compares blind, partition-aware and discovery modes, showing that only the blind solver pays information debt【F:results/engine_output.txt†L54-L58】.

## Tseitin Instances
Structured Tseitin instances of three sizes were generated and solved.  The blind
solver is a SAT engine limited by a conflict and propagation budget, while the
sighted solver performs Gaussian elimination on the XOR system.

| `n` | Blind Conflicts | Blind Props | Blind Decisions | Sighted Rank Gap |
|-----|----------------:|------------:|----------------:|-----------------:|
| 8   | 27              | 159         | 26              | 1 |
| 10  | 56              | 389         | 55              | 1 |
| 12  | 54              | 298         | 67              | 1 |

Raw receipts are stored under `results/` as `tseitin_output_n8.json`,
`tseitin_output_n10.json` and `tseitin_output_n12.json`.

## Automated Harness
To reproduce the measurements, run

```bash
python scripts/run_all_experiments.py
```

The script regenerates all receipts and prints their SHA256 hashes.  The current
hashes are recorded below to enable verification:

- `engine_output.txt` – `c9bd9b1eec1c62b5f63962572c63dce733f24bb86d17d66d0e9a043272e31bb4`
- `tseitin_output_n8.json` – `098e0424380c20e050559f1af165dccde660a3eccc1aa48965e2853534c40eba`
- `tseitin_output_n10.json` – `f0f724ffb22ff1132a4429dfbfb82889fcef63e1c07c3bc9d725fc9b8117a382`
- `tseitin_output_n12.json` – `f8ec305ba3a8ea5e8cb03773d9a7e4770b9616ffc44df6dc9bfb52bcdef45e5d`

Regenerating the experiments should yield the same hashes on a deterministic
platform.

# AWS thermodynamic bridge (no-keys runbook)

This runbook executes the thesis falsifiability dataset (energy vs μ) on AWS.

## Why bare-metal

To record a real energy observable in the harness we use Linux Intel RAPL counters:

- `/sys/class/powercap/intel-rapl:*/energy_uj`

These are usually available only on Intel **bare-metal** instances.

## Launch (recommended)

- EC2 instance type: `c6i.metal` (or `c5.metal` as fallback)
- AMI: Ubuntu 24.04 LTS
- Access: **Session Manager** (no SSH keys required)

### Required IAM role

Attach an instance profile with the managed policy:

- `AmazonSSMManagedInstanceCore`

## Connect (no keys)

- EC2 → Instances → select instance
- Connect → Session Manager → Connect

## Hard checkpoint: RAPL exists

In the Session Manager shell:

- `ls -1 /sys/class/powercap/intel-rapl:*/energy_uj`
- `cat /sys/class/powercap/intel-rapl:*/energy_uj; sleep 1; cat /sys/class/powercap/intel-rapl:*/energy_uj`

If this fails (no files), you can still run μ-only, but you cannot collect the energy falsifiability dataset on this host.

## Run (one command)

From repo root:

- `bash scripts/falsifiability_all.sh`

Outputs a timestamped bundle under `results/falsifiability_bundle/`.

### Tuning knobs

Main knobs:
- `ENERGY_REPS=20000` increases the energy signal (recommended to start here).
- `ENERGY_MODE=none` runs μ-only and skips energy measurement.
- `CPU_PIN=0` pins the run to a single core (reduces noise).
- `INSTALL_OS_DEPS=1` installs OS packages via `apt-get` (fresh Ubuntu instances).
- `THERMO_TEMPERATURE_K=300` sets the temperature used in the Landauer term.

Example:

- `INSTALL_OS_DEPS=1 ENERGY_REPS=50000 THERMO_TEMPERATURE_K=300 bash scripts/falsifiability_all.sh`

## Stop costs

Terminate the instance when done.

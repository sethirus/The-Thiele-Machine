# Landauer Principle Experimental Verification Protocol
## Thiele Machine μ-Cost to Heat Conversion

**Date:** 2026-03-11
**Objective:** Empirically verify that the μ-cost function bounds heat dissipation according to Landauer's principle.

---

## Executive Summary

This protocol tests whether executing a Thiele program incurring Δμ μ-units of cost requires a minimum heat dissipation of:

$$Q_{\min} = \Delta\mu \cdot k_B \cdot T \cdot \ln(2)$$

where:
- $\Delta\mu$ = μ-cost measured from the VM state counter
- $k_B$ = Boltzmann's constant (1.380649 × 10⁻²³ J/K)
- $T$ = absolute temperature (K)
- $\ln(2)$ ≈ 0.693

**Theorem being tested** (Coq): `mu_cost_landauer_bound` in `coq/kernel/LandauerBound.v`

**Physical principle** (empirical): Landauer's principle (Bérut et al., 2012; Shizume, 1995)

---

## Preconditions

### Hardware Requirements

1. **FPGA Development Board:**
   - ULX3S ECP5 (primary target)
   - Or equivalent with:
     - UART interface (115200 baud, 8N1)
     - Accessible power rails (≥ 1 rail at 3.3V ± 5%)
     - Board must fit synthesized Thiele CPU (37 LUTs for base, per synthesis report)

2. **Power Measurement Instrument:**
   - INA219 current/voltage monitor (I²C bus, ±3.2A range)
   - Or equivalent:
     - ±0.1% accuracy on voltage measurements
     - ±0.1% accuracy on current measurements
     - Bandwidth ≥ 100 kHz (to resolve per-cycle power transients)
   - Measurement must sample the **program execution rail** (typically 3.3V VDD)

3. **Temperature Control:**
   - Environmental chamber or thermal stabilization to ±0.5 K
   - Thermometer (RTD Pt100 or equivalent) mounted on board, resolved to 0.1 K
   - Equilibration time: 30 minutes before each run

4. **Host Computer:**
   - Linux or macOS with Python 3.9+
   - USB-UART bridge (FTDI or compatible)
   - I²C interface (RPi, BeagleBone, or USB-I2C adapter)

5. **Verification / Reference Standards:**
   - Resistance standard (1Ω × 0.1%, metal film resistor) for calibration
   - Oscilloscope (100 MHz, optional) to validate power rail stability during test

### Software Preconditions

1. **Build the Thiele FPGA bitstream:**
   ```bash
   cd /workspaces/The-Thiele-Machine
   scripts/fpga_build.sh
   # Output: build/thiele_ecp5.config (or .bit)
   ```

2. **Assembler ready:**
   ```bash
   python3 scripts/thiele_asm.py --help
   # Should output usage with test programs available
   ```

3. **UART loader utility:**
   - `scripts/fpga_upload.py` should send program over UART and read back execution state

4. **Power measurement logger:**
   - Build or use standard INA219 library (e.g., Adafruit INA219 Python package)
   - Should log voltage (V), current (A), time (ms) at 1 kHz or faster

---

## Test Design

### Test Programs

Create three benchmark programs with known μ-costs:

#### Program A: No-Op Baseline (Δμ ≈ 0)
```
Label start
    ; 100 iterations of NOP (cost 0)
    INT i 0
loop:
    PNEW {0} 0         ; cost 0 (allocate empty region, free immediately)
    JNEZ i loop_continue
    JMP loop_end
loop_continue:
    IDEC i
    JMP loop
loop_end:
    HALT
```
**Expected Δμ:** 1 (for HALT only)

#### Program B: Moderate Cost (Δμ ≈ 256)
```
Label start
    ; 256 iterations of LRAT (cost 1 per iteration)
    INT i 0
    PNEW {0,1024} 256  ; allocate region, cost ~1-2
loop:
    LRAT 0 0 1         ; cost 1 (verify empty LRAT)
    IDEC i
    JNEZ i loop
    HALT
```
**Expected Δμ:** 256 + ~2 = ~258

#### Program C: High Cost (Δμ ≈ 1024)
```
Label start
    ; 1024 iterations of ADD (cost 0) wrapped with 1024 REVEAL (cost 1)
    INT acc 0
    INT i 0
    PNEW {0,1024} 1024 ; cost ~2
loop:
    ADD acc acc 0      ; cost 0
    REVEAL i acc 1     ; cost 1
    IDEC i
    JNEZ i loop
    HALT
```
**Expected Δμ:** 1024 + ~2 = ~1026

### Test Matrix

| Run | Program | T (K) | Target Δμ | Expected Q_min (mJ) | Notes |
|-----|---------|-------|-----------|---------------------|-------|
| 1   | A       | 293   | 1         | 0.00028             | baseline, verify measurement noise < 1 μJ |
| 2   | A       | 293   | 1         | 0.00028             | repeat for RSD |
| 3   | B       | 293   | 258       | 0.073               | moderate load |
| 4   | B       | 293   | 258       | 0.073               | repeat |
| 5   | C       | 293   | 1026      | 0.291               | high load |
| 6   | C       | 293   | 1026      | 0.291               | repeat |
| 7   | C       | 323   | 1026      | 0.324               | elevated temp |
| 8   | C       | 263   | 1026      | 0.264               | reduced temp |

**Minimum samples required:** 8 runs (3 programs × 2 repeats + 2 temperature variations)

---

## Execution Protocol

### Setup Phase (Day 0: ~2 hours)

1. **Power rail isolation:**
   - Desolder or lift the 3.3V supply on the board (or use a power distribution board with independent rails)
   - Connect the **program execution** rail through the INA219 shunt
   - **critical:** separate from debug/UART power if possible; if not, measure UART current separately and subtract

2. **Thermocouple placement:**
   - Attach RTD/thermocouple to the FPGA die or board substrate as close to the ECP5 as possible
   - Insulate from air currents
   - Log reference temperature sensor in chamber

3. **Calibration:**
   - Apply known constant current (10 mA) through 1Ω reference resistor
   - Verify INA219 reads 10 mV across shunt ± 0.1 mV
   - If not, adjust INA219 gain or replace sensor

4. **FPGA programming:**
   - Connect UART and power
   - Upload bitstream via openFPGALoader or equivalent
   - Verify CFG LED lights up (heartbeat visible)

5. **Software setup:**
   - Run `scripts/fpga_upload.py` with Program A as a dry run
   - Verify HALT is reached and reported back
   - Read μ-counter from debug dump; should be ~1

### Measurement Phase (Per Run: ~10 minutes)

1. **Thermal equilibration:**
   - Place board in chamber at target temperature
   - Wait 30 minutes
   - Log temperature; proceed only if ΔT < 0.5 K over last 5 minutes

2. **Idle power baseline:**
   - Run data logger for 30 seconds with board idle (FPGA in halted state)
   - Record baseline current $I_{idle}$ (should be < 50 mA for idle ECP5)
   - Save to `baseline/run_N.csv`

3. **Program load:**
   - Assemble target program
   - Load into board via UART (program upload takes ~100 ms)

4. **Execution window:**
   - **T = 0:** send UART command to start execution
   - **T = t_exec:** CPU halts; logger stops
   - Logger settings:
     - Sample rate: 1 kHz (1 ms resolution)
     - Channels: Voltage (mV), Current (mA), Time (ms), Temperature (K)
     - File: `measurements/run_N.csv`

5. **Data capture:**
   - Read μ-counter from halted state (debug dump via FPGA_upload.py)
   - Record as `run_N_metadata.json`:
     ```json
     {
       "run": N,
       "program": "A|B|C",
       "T": 293.0,
       "wall_clock_start": "2026-03-15T14:23:45.123Z",
       "wall_clock_stop": "2026-03-15T14:23:45.850Z",
       "exec_time_ms": 725,
       "mu_initial": 0,
       "mu_final": 258,
       "delta_mu": 258,
       "log_file": "measurements/run_N.csv"
     }
     ```

6. **Cool-down:**
   - Wait 5 minutes before next run (allow ECP5 to return to ambient)
   - Verify via temperature sensor

### Data Processing Phase (End of Day)

For each run N:

1. **Load CSV:** `measurements/run_N.csv` → Pandas DataFrame
   - Columns: `time_ms`, `voltage_mV`, `current_mA`, `temperature_K`

2. **Power computation:**
   ```python
   P(t) = V(t) × I(t)  # instantaneous power in mW
   ```

3. **Idle power subtraction:**
   ```python
   P_cpu(t) = P(t) - (V_avg × I_idle)  # CPU-only power
   ```

4. **Heat integration:**
   ```python
   Q_measured = ∫_0^{t_exec} P_cpu(t) dt  # joules
   ```
   Use trapezoidal integration over sampled time points.

5. **Theoretical prediction:**
   ```
   Q_predicted = Δμ × k_B × T × ln(2)
                = Δμ × 1.380649e-23 × T × 0.693147
                [units: joules]
   ```

6. **Comparison:**
   ```
   Ratio = Q_measured / Q_predicted

   Interpretation:
   - Ratio ≥ 1.0  ✓ Consistent with Landauer bound
   - Ratio < 1.0  ✗ Violates Landauer principle (indicates measurement error or theory problem)
   ```

   Record in results table:
   | Run | Program | T (K) | Δμ | Q_pred (mJ) | Q_meas (mJ) | Q_meas/Q_pred | Status |
   |-----|---------|-------|----|-----------  |-------------|----------------|--------|

---

## Success Criteria

The experiment PASSES if:

1. **Measurement noise is below signal:**
   - For Program A (Δμ ≈ 1), measured Q should be 0.0001–0.001 mJ
   - RSD across 2 runs < 20% (or absolute std dev < 50 μJ)

2. **Monotonicity:**
   - Median Q_measured increases monotonically with Δμ
   - Program A < Program B < Program C (all at same T)

3. **Temperature scaling:**
   - Q increases ∝ T (linear regression, R² > 0.9)
   - Run 7 on Program C at 323K: Q_measured > predicted at 293K

4. **Landauer compliance (main result):**
   - For all 8 runs: Q_measured ≥ 0.95 × Q_predicted (95% efficiency)
   - No run violates the bound: Q_measured < 0.9 × Q_predicted
   - If any violation: repeat that run; if persists, investigate hardware/assembly

**Interpretation:**
- **All criteria met:** Landauer principle appears to hold for the Thiele CPU. μ-cost is a valid lower bound on physical heat.
- **Criterion 3 fails:** Temperature scaling wrong → either Landauer doesn't apply to this device, or something else is generating heat (non-μ-related).
- **Criterion 4 fails by small amount (0.9–0.95):** Measurement error or inefficiency in FPGA implementation.
- **Criterion 4 fails by large amount (< 0.7):** Serious theoretical question: either μ-accounting is incomplete, or physics prediction is wrong.

---

## Failure Modes & Investigation

If the experiment fails, investigate in this order:

### A. Measurement Errors (High Priority)

1. **Calibration drift:**
   - Re-calibrate INA219 with reference resistor before resuming
   - Check sensor hasn't drifted > 1% over day

2. **Power rail contamination:**
   - Non-program activity (UART, debug, oscillator) drawing current?
   - Measure each component's idle current separately
   - Subtract from total correctly

3. **Temperature reading:**
   - Is thermocouple in contact with die? Check continuity.
   - Does temperature logger agree with chamber sensor? If not, offsets?
   - Fluctuation > 0.5 K during run?

4. **UART upload overhead:**
   - Does UART power consumption hide in above measurements?
   - Repeat with program resident in block RAM (pre-loaded at boot)

### B. Hardware Implementation Issues (Medium Priority)

1. **FPGA bitstream mismatch:**
   - Did synthesis actually include all 31 opcodes in build?
   - Check RTL by inspecting generated Verilog or post-PAR netlist
   - Count LUTs; should be ~31,000 for full Thiele CPU

2. **Memory initialization:**
   - Are program and partition tables correctly loaded?
   - Step program in simulation, verify μ-counter advances correctly
   - If cosim differs from hardware, FPGA build is wrong

3. **Power supply stability:**
   - Is VDD rail actually 3.3V throughout run, or drooping?
   - Measure with oscilloscope; ripple should be < 100 mV

### C. Assembly/Program Issues (Lower Priority)

1. **μ-counter mismatch:**
   - Did FPGA actually execute the right number of high-cost instructions?
   - Dump instruction trace (debug_dumper captures last PC); does it match assembly?

2. **Halt condition:**
   - Is program actually halting, or hanging in loop?
   - If hanging, thread can't advance and μ not added

---

## Reporting

After all runs complete, produce a lab report:

### Report Structure

1. **Summary:** One paragraph of main finding (pass/fail + binding result)

2. **Methods:**
   - Board model, INA219 specs, chamber specs
   - Test programs (assembly listings)
   - Temperature(s) used
   - Sampling rate, calibration procedure

3. **Results:**
   - Table of all 8 runs with Δμ, T, Q_pred, Q_meas, ratio
   - Plot: Δμ vs. (Q_meas / Q_pred), should be flat at y=1
   - Plot: T vs. Q_meas for Program C, should be linear
   - Any failed runs and repeat results

4. **Uncertainty Analysis:**
   - INA219 calibration uncertainty (< 0.1%)
   - Measurement RSD (typically 2–5%)
   - Temperature uncertainty (< 0.5 K)
   - Combined uncertainty in Q_pred / Q_meas ratio

5. **Conclusion:**
   - State whether Landauer bound is satisfied (with confidence interval)
   - Discuss any deviations and their likely causes
   - Comment on whether μ-cost is a physically meaningful quantity

6. **Data Availability:**
   - All CSV logs, metadata JSON, and code in public repository
   - Bitstream and assembled programs in reproducibility folder

---

## Timeline & Resource Estimate

| Phase | Duration | Notes |
|-------|----------|-------|
| Hardware setup | 4–6 hours | soldering, INA219 wiring, chamber setup |
| Software integration | 2–3 hours | test UART, assemble programs, verify GPIO |
| Test runs (8 total) | 2–3 hours | 10 min/run + cool-down |
| Data processing | 1–2 hours | CSV parsing, integration, plotting |
| Report writing | 2–3 hours | analysis, uncertainty, conclusion |
| **Total** | **11–17 hours** | spread over 2–3 days (thermal equilibration costly) |

---

## Success Reference

**Relevant prior experimental work:**

- **Bérut et al. (2012):** "Experimental demonstration of Landauer's principle linking information and thermodynamics," Nature 483, 187–189.
  - Demonstrates Q ≥ kT ln 2 for bit erasure in a colloidal particle system
  - Measurement agreement: 95–100%

- **Shizume (1995):** "Heat generation required by erasure," Phys. Rev. E 52, 3495.
  - Theoretical foundation for Landauer's principle
  - Shows minimum heat is unavoidable for information-destroying processes

---

## Appendix: Python Driver Skeleton

```python
#!/usr/bin/env python3
import serial
import csv
import json
import time
from pathlib import Path
from ina219 import INA219

# Configuration
FPGA_PORT = "/dev/ttyUSB0"
FPGA_BAUD = 115200
I2C_ADDR = 0x40  # INA219 default
SAMPLE_RATE = 1000  # Hz (1 ms intervals)

class LandauerExperiment:
    def __init__(self, run_number, program_name, target_temp_k):
        self.run = run_number
        self.program = program_name
        self.target_temp = target_temp_k
        self.output_dir = Path("measurements")
        self.output_dir.mkdir(exist_ok=True)

    def idle_baseline(self, duration_s=30):
        """Measure idle power for 30 seconds."""
        voltages, currents, times = [], [], []
        start = time.time()
        while time.time() - start < duration_s:
            v = self.ina.voltage()
            i = self.ina.current()
            voltages.append(v)
            currents.append(i)
            times.append(time.time() - start)
            time.sleep(1 / SAMPLE_RATE)

        idle_current = sum(currents) / len(currents)
        with open(self.output_dir / f"baseline_run_{self.run}.csv", "w") as f:
            writer = csv.DictWriter(f, fieldnames=["time_s", "voltage_mV", "current_mA"])
            writer.writeheader()
            for t, v, i in zip(times, voltages, currents):
                writer.writerow({"time_s": t, "voltage_mV": v*1000, "current_mA": i*1000})

        return idle_current

    def execute_program(self, program_binary):
        """Execute program and log power."""
        voltages, currents, times = [], [], []

        # Send program to FPGA
        self.ser.write(program_binary)

        # Log power during execution
        start = time.time()
        while True:  # until HALT received
            v = self.ina.voltage()
            i = self.ina.current()
            voltages.append(v)
            currents.append(i)
            times.append(time.time() - start)

            # Check for halt (UART message)
            if self.ser.in_waiting:
                msg = self.ser.readline()
                if b"HALT" in msg:
                    break

            time.sleep(1 / SAMPLE_RATE)

        # Save data
        csv_file = self.output_dir / f"measurements_run_{self.run}.csv"
        with open(csv_file, "w") as f:
            writer = csv.DictWriter(f, fieldnames=["time_ms", "voltage_mV", "current_mA"])
            writer.writeheader()
            for t, v, i in zip(times, voltages, currents):
                writer.writerow({"time_ms": t*1000, "voltage_mV": v*1000, "current_mA": i*1000})

        # Store metadata
        metadata = {
            "run": self.run,
            "program": self.program,
            "target_temp_k": self.target_temp,
            "exec_time_ms": times[-1] * 1000,
            "csv_file": str(csv_file)
        }
        with open(self.output_dir / f"metadata_run_{self.run}.json", "w") as f:
            json.dump(metadata, f, indent=2)

if __name__ == "__main__":
    import sys
    run_num = int(sys.argv[1]) if len(sys.argv) > 1 else 1

    exp = LandauerExperiment(run_num, "Program_A", 293.0)

    # Connect to hardware
    ser = serial.Serial(FPGA_PORT, FPGA_BAUD, timeout=1)
    ina = INA219(I2C_ADDR)

    # Baseline
    idle_i = exp.idle_baseline()
    print(f"Idle current: {idle_i*1000:.1f} mA")

    # Run program (placeholder binary)
    program_bytes = b"\x00" * 100  # TODO: load from .hex file
    exp.execute_program(program_bytes)

    print(f"Run {run_num} complete. Data in {exp.output_dir}/")
```

---

**Prepared by:** Thiele Machine Team
**Date:** 2026-03-11
**Status:** Experimental Protocol Defined (awaiting hardware)

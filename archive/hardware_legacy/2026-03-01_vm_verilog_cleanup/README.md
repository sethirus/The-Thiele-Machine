# VM + Verilog Cleanup Archive (2026-03-01)

This archive was created to declutter active working folders while preserving older generated artifacts.

## Source folders trimmed

- `build/`
- `thielecpu/hardware/rtl/`

## Archived under this directory

- `build/verilator/` (generated Verilator build cache and objects)
- VM runner binaries and simulation outputs:
  - `build/vm_runner`
  - `build/extracted_vm_runner`
  - `build/extracted_vm_runner_native`
  - `build/thiele_kami_test.vvp`
  - `build/thiele_kami_batch.vvp`
  - `build/thiele_cpu_kami_tb.out`
  - `build/hw_trace.json`
  - `build/verify_trace.txt`
- Verilog byproducts:
  - `thielecpu/hardware/rtl/synth_full_out.v`
  - `thielecpu/hardware/rtl/synth_lite_clean.log`
  - `thielecpu/hardware/rtl/thiele_cpu_tb.vcd`

## Notes

- Active RTL sources and currently used synthesis outputs were kept in place.
- Equivalent cleanup can be repeated via:
  - `make archive-vm-verilog`
  - Optional custom tag: `make archive-vm-verilog ARCHIVE_TAG=2026-03-01_custom`

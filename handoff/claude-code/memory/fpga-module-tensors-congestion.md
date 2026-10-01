---
name: fpga-module-tensors-congestion
description: "Why CI (Full) bitstream timed out on work/v3.2.2-review-fixes; RegFile fix, failed DSP detour, and the 128x128 CHSH multiplier split (2026-09-26)"
metadata:
  node_type: memory
  type: project
  originSessionId: a5c67d8f-1460-46c9-bc1c-722d5b65416d
  modified: 2026-09-25T19:03:25.438Z
---

CI (Full) FPGA job on work/v3.2.2-review-fixes hits its 180 min cap in nextpnr router2 (overuse plateaus ~14k; main converges). Cause, proven by bisection on 2026-09-25 (hand-patched Verilog, FPGA job only): tying off `module_tensors$EN` routes (1h39m); tying off the coupling FSM does not; tying off the CHSH FSM routes in 20 min (its LUT-mapped 384x384 multiplier is what leaves little headroom). A per-row rewrite of the tensor write alone did NOT fix it (still ~14k), so any flip-flop implementation of the 16x16x32 tensor store with its read mux is too much; it must become a RegFile/LUTRAM.

Fix chosen: no Coq change. `scripts/bsv_regfile_transform.py` gains a matrix pass (`MATRIX_REGS = {"module_tensors"}`) mapping the 2-D Kami vector register to `RegFile#(Bit#(8), Bit#(32))` via `mkRegFileFullZero` (clears after reset before sub/upd enable, like mem/imem), rewriting the one nested update to `if (we) upd({mod,idx}, v)` and the TENSOR_GET read to `sub({mod,idx})`, confined to the `step` rule body (variable names repeat across rules). Then regenerate RTL with `scripts/kami_extract.sh` (bsc 2024.07 unpacked at /tmp/bsc-2024.07-ubuntu-22.04), rerun RTL tests and the RTL transform audit/manifest, and validate on CI.

Do NOT use Kami `BuildVector` for such fixes: vendored PP.ml prints vector literals in an order that is bit-reversed relative to `evalVec` semantics for >= 4 elements (latent, unused).

gh token cannot dispatch or cancel workflows (HTTP 403); experiment branches trigger CI (Full) via a push trigger in their own ci-full.yml. Delete experiment/fpga-* branches (local + remote) and scratch worktrees when done; never merge them.

Update 2026-09-26: RegFile alone got router overuse to 300 at iter 57 but hit the 180 min cap (run 36179146430). Second fix: removed `-nodsp` from synth_xc7.ys. CHSH multiplier operands are zero-extended from <=256 bits, so yosys maps it to 279 DSP48E1 and total LUTs drop ~160K -> ~28K. Committed as 4459e5e5 on work/v3.2.2-review-fixes (full hook passed, pushed); experiment branch deleted. CI (Full) result on 4459e5e5 is the pending proof; Devon must dispatch it from the Actions UI.

Local place-and-route is impossible on this 8 GB codespace: bbaexport for xc7k325t needs >3.5 GB RSS and the environment SIGTERMs processes when MemAvailable < ~1.2 GB. Don't retry it; validate on CI. Also: background jobs started with `nohup ... &` from a Bash call get killed with the shell's process group; use run_in_background instead.

Update 2026-09-26 later: 4459e5e5 (plain DSP inference) stalled on CI in "Running main analytical placer" for 2h44m even though the design packed to 11% LUTs / 279 DSP. Cause: xilinx_dsp builds PCOUT->PCIN cascade chains (up to 20 cells) that nextpnr-xilinx must legalise as rigid macros. Fix: `scratchpad -set xilinx_dsp.multonly 1` before synth_xilinx (0 cascades, ~33K LUTs locally). GitHub's live log view freezes after the ~20K "Port ... has no connections" DSP warnings; read the finished log via `gh api repos/sethirus/The-Thiele-Machine/actions/jobs/<id>/logs`.

Update 2026-09-26 evening (supersedes the multonly fix): b687258e (standalone DSPs) placed in ~90 s but routing was badly congested (overuse 56,011 after 3 router2 passes vs main's 1,430) and hit the 180 min cap. The live GitHub log (and the in-progress jobs/<id>/logs API) truncate around 25K lines, so silence after the DSP warnings says nothing; only the finished log is trustworthy. RegFile + LUT multiplier was converging too slowly (overuse 300 at iter 57, ~15/iter) to fit even 6 h. Devon chose to fix the design: the CHSH FSM now shares a 128x128 multiplier over 29 phases (C_sq in 21..24 and A_times_B in 25..28 summed from four partial products; commit at 29). yosys -nodsp gives ~60K LUTs (was ~160K; main 158.9K). ChshArith.m384_parts_eq proves the four-part sum equals m384. synth_xc7.ys is back to main's `-nodsp` line with no scratchpad option. Generators changed: generate_chsh_phases.py (LAST, ACCUMULATORS, accumulate), generate_chsh_run.py, generate_chsh_retire.py, generate_retire_master.py; hand edits in RetireRunsOps.v and TableInvariantsPreserved.v (chsh_iter 29).

Landed 2026-09-27 as e2457bd0 (full hook: Coq, extraction, 1088 tests passed; pushed), together with Devon's register/prose pass. Receipt re-derived: 12,817 probed, 5,526 closed, 7,291 stdlib-only, zero project-local. Unfold-order trap hit on the way: phase_unfold must unfold chsh_part_* before chsh_mult_*, or the mult terms stay folded and reflexivity fails. Codespace is now 4-core/16 GB (receipt with 4 jobs ~40 min; 2 jobs on 8 GB tripped the guard). Next: Devon dispatches CI (Full) from the Actions UI; then PR to main, v3.2.2 tag and release notes in his words.

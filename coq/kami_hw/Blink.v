(** Blink.v — Trivial Kami module to validate the extraction pipeline.
    A 32-bit counter that increments on every clock cycle.
    If this extracts to Bluespec and compiles to Verilog, the toolchain works. *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.

Set Implicit Arguments.
Set Asymmetric Patterns.

Definition blink :=
  MODULE {
    Register "counter" : Bit 32 <- Default

    with Rule "increment" :=
      Read cnt : Bit 32 <- "counter";
      Write "counter" : Bit 32 <- #cnt + $1;
      Retv
  }.

#[global] Hint Unfold blink : ModuleDefs.

(** Extraction target: convert to synthesizable form *)
Definition blinkS := getModuleS blink.
Definition blinkB := ModulesSToBModules blinkS.

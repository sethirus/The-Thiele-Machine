(** KamiExtraction.v — Extracts Kami hardware modules to OCaml.
    The OCaml code is then used by PP.ml to generate Bluespec,
    which bsc compiles to synthesizable Verilog.

    Pipeline: Coq → OCaml extraction → Bluespec → Verilog *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import CanonicalCPUProof.
From KamiHW Require Import ThieleCPUBusTop.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "../build/kami_hw/Target.ml"
    canonical_cpu_module
    canonical_snapshot_to_vm
    canonical_refinement_relation
    BusReg
    BusCoreView
    BusShadowRegs
    BusWrapperState
    BusOp
    decodeBusReg
    busRegReadable
    busRegWritable
    busRead
    busWrite
    bus_step
    coreViewOfSnapshot.

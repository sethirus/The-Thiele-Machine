(** KamiExtraction.v — Extracts Kami hardware modules to OCaml.
    The OCaml code is then used by PP.ml to generate Bluespec,
    which bsc compiles to synthesizable Verilog.

    Pipeline: Coq → OCaml extraction → Bluespec → Verilog *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
Require Import KamiHW.ThieleCPUCore.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "../build/kami_hw/Target.ml" thieleCoreB.

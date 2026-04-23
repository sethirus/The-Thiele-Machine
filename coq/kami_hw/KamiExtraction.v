(** KamiExtraction.v — Extracts the canonical Coq-generated BModules AST to OCaml.
    The OCaml code is then used by PP.ml to print Bluespec text,
    which bsc compiles to synthesizable Verilog.

    Pipeline: Coq module -> Kami synthesis in Coq -> BModules AST ->
              OCaml extraction -> PP.ml text printing -> Verilog *)

Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import CanonicalCPUProof.

Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.
Extraction Language OCaml.

Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "../build/kami_hw/Target.ml" canonical_cpu_module targetB.

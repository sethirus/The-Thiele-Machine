(** Extracts the composed CPU and loader to OCaml for the Bluespec printer.
    The output is a module named Target, in its own directory, because the
    printer opens Target by name; the CPU-only extraction in
    [KamiExtraction] is unchanged. *)
Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import ThieleSystem.
Require Import ExtrOcamlBasic ExtrOcamlNatInt ExtrOcamlString.

Extraction Language OCaml.
Set Extraction Optimize.
Set Extraction KeepSingleton.
Unset Extraction AutoInline.

Extraction "../build/kami_hw/system/Target.ml" thieleSystemB targetB.

(** ThieleSystem: the CPU and its serial loader composed into one design.

    [thieleSystem] is the Kami composition of [thieleCore] and
    [thieleLoader]. The loader's calls to [loadInstr], [start] and the
    status getters are the CPU's own methods, so the composition is closed
    over them; its remaining methods ([rxSample], [getTx], [getLeds] and the
    CPU getters the loader does not use) are the design's pins.

    Extraction prints the composition as two Bluespec modules and the module
    that connects them; [scripts/kami_system_top.py] gives that connecting
    module its pin interface, and bsc compiles it to Verilog. *)
Require Import Kami.Kami.
Require Import Kami.Synthesize.
Require Import Kami.Ext.BSyntax.
From KamiHW Require Import ThieleTypes ThieleCPUCore ThieleLoader.

Definition thieleSystem := (thieleCore ++ thieleLoader)%kami.
Definition thieleSystemS := getModuleS thieleSystem.
Definition thieleSystemB := ModulesSToBModules thieleSystemS.

(** The syntax the printer receives is the CPU's followed by the loader's. *)
Theorem thieleSystemS_composes :
  thieleSystemS = ConcatModsS thieleCoreS thieleLoaderS.
Proof. reflexivity. Qed.

(** Entry point for the Bluespec printer. *)
Definition targetB (_ : nat) := thieleSystemB.

(** SmEvalL.v: the two evaluators of SmInterp.v as Minsky machines.

    Every function of SmCodes.v and SmInterp.v is turned into a term of the
    lambda calculus L, each with a correctness proof ([computable], checked
    by the Coq kernel; the extraction tactic needs MetaCoq Template). A fuel
    function that is monotone in its fuel then defines an L-computable
    relation of two numbers, by unbounded search over the fuel
    ([L_computable_fuel2]). The vendored theorem
    [L_computable_to_MMA_computable] turns each such relation into a
    program of the vendored alternate Minsky machine (MMA), with the two
    inputs in counters 1 and 2 and the answer in counter 0
    ([sm_ev_MMA], [sm_uev_MMA]).

    The lambda calculus and the Minsky compilers are tools here: they
    produce one fixed counter program for each evaluator and certify its
    input-output relation. The fixed-point argument itself is in
    SmKleene.v.

    Dependencies: Coq standard library, MetaCoq Template (for the
    extraction tactic only), the vendored coq-undecidability library (L,
    MinskyMachines), EarnedCore.v, EarnedGeneric.v, EarnedMulti.v,
    UniversalCodes.v, SmHostBlocks.v, SmCodes.v and SmInterp.v. No axioms,
    no Admitted.                                                           *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here L-computable instances of the evaluators and codes of the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.L.Tactics Require Import GenEncode.
From Undecidability.MinskyMachines Require Import MMA.
From Undecidability.MinskyMachines.Reductions Require Import L_computable_to_MMA_computable.
Require Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmInterp.

MetaCoq Run (tmGenEncode "sm_enc_ki" sm_ki).
#[export] Hint Resolve sm_enc_ki_correct : Lrewrite.

Instance term_sm_KInc : computable sm_KInc. Proof. extract constructor. Qed.
Instance term_sm_KDec : computable sm_KDec. Proof. extract constructor. Qed.
Instance term_sm_KCheck : computable sm_KCheck. Proof. extract constructor. Qed.
Instance term_sm_KCommit : computable sm_KCommit. Proof. extract constructor. Qed.

Instance term_sm_upair : computable Minimal.UniversalCodes.pair. Proof. extract. Qed.
Instance term_sm_hb : computable sm_hb. Proof. extract. Qed.
Instance term_sm_unp : computable sm_unp. Proof. extract. Qed.
Instance term_sm_unpair : computable sm_unpair. Proof. extract. Qed.
Instance term_sm_lencode : computable sm_lencode. Proof. extract. Qed.
Instance term_sm_ldec : computable sm_ldec. Proof. extract. Qed.
Instance term_sm_ldecode : computable sm_ldecode. Proof. extract. Qed.
Instance term_sm_kcode : computable sm_kcode. Proof. extract. Qed.
Instance term_sm_kdec2 : computable sm_kdec2. Proof. extract. Qed.
Instance term_sm_kdec_op : computable sm_kdec_op. Proof. extract. Qed.
Instance term_sm_kdec : computable sm_kdec. Proof. extract. Qed.
Instance term_sm_kpcode : computable sm_kpcode. Proof. extract. Qed.
Instance term_sm_kpdec : computable sm_kpdec. Proof. extract. Qed.
Instance term_sm_rj : computable sm_rj. Proof. extract. Qed.
Instance term_sm_kri : computable sm_kri. Proof. extract. Qed.
Instance term_sm_kreloc : computable sm_kreloc. Proof. extract. Qed.
Instance term_sm_kspec_prog : computable sm_kspec_prog. Proof. extract. Qed.
Instance term_sm_kspec : computable sm_kspec. Proof. extract. Qed.
Instance term_sm_lset : computable sm_lset. Proof. extract. Qed.
Instance term_sm_keval : computable sm_keval. Proof. extract. Qed.
Instance term_sm_kheval : computable sm_kheval. Proof. extract. Qed.
Instance term_sm_kmem : computable sm_kmem. Proof. extract. Qed.
Instance term_sm_kfetch : computable sm_kfetch. Proof. extract. Qed.
Instance term_sm_kexec : computable sm_kexec. Proof. extract. Qed.
Instance term_sm_kstep : computable sm_kstep. Proof. extract. Qed.
Instance term_sm_khalted : computable sm_khalted. Proof. extract. Qed.
Instance term_sm_krun : computable sm_krun. Proof. extract. Qed.
Instance term_sm_kstart : computable sm_kstart. Proof. extract. Qed.
Instance term_sm_kout : computable sm_kout. Proof. extract. Qed.
Instance term_sm_ev : computable sm_ev. Proof. extract. Qed.

Instance term_sm_uev : computable sm_uev. Proof. extract. Qed.

Definition sm_uev2 (d fuel x c : nat) : option nat := sm_uev fuel x c.
Instance term_sm_uev2 : computable sm_uev2. Proof. extract. Qed.

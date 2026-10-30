(** TcEvalL.v: the packed evaluators of TcInterp.v as terms of the lambda
    calculus L.

    Every function of TcCodes.v, TcBlocks.v and TcInterp.v that the two
    evaluators use is turned into a term of L, each with a correctness proof
    ([computable], checked by the Coq kernel; the extraction tactic needs
    MetaCoq Template). TcFuel.v then turns the two evaluators into programs of
    the vendored alternate Minsky machine.

    The lambda calculus and the Minsky compilers are tools here: they
    produce one fixed counter program for each evaluator and certify its
    input-output relation. The fixed-point argument itself is in
    TcKleene.v.

    Dependencies: Coq standard library, MetaCoq Template (for the extraction
    tactic only), the vendored coq-undecidability library (L), EarnedCore.v,
    UniversalCodes.v and the Tc files before it. No axioms and no unfinished proofs.    *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions
  Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.L.Tactics Require Import GenEncode.
Require Minimal.UniversalCodes.
Require Import Minimal.TcBlocks Kernel.TcCodes Kernel.TcInterp.

MetaCoq Run (tmGenEncode "tc_enc_ki" tc_ki).
#[export] Hint Resolve tc_enc_ki_correct : Lrewrite.

Instance term_tc_KInc : computable tc_KInc. Proof. extract constructor. Qed.
Instance term_tc_KDec : computable tc_KDec. Proof. extract constructor. Qed.
Instance term_tc_KCheck : computable tc_KCheck. Proof. extract constructor. Qed.
Instance term_tc_KCommit : computable tc_KCommit. Proof. extract constructor. Qed.

Instance term_tc_upair : computable Minimal.UniversalCodes.pair. Proof. extract. Qed.
Instance term_tc_hb : computable tc_hb. Proof. extract. Qed.
Instance term_tc_unp : computable tc_unp. Proof. extract. Qed.
Instance term_tc_unpair : computable tc_unpair. Proof. extract. Qed.
Instance term_tc_lencode : computable tc_lencode. Proof. extract. Qed.
Instance term_tc_ldec : computable tc_ldec. Proof. extract. Qed.
Instance term_tc_ldecode : computable tc_ldecode. Proof. extract. Qed.
Instance term_tc_kcode : computable tc_kcode. Proof. extract. Qed.
Instance term_tc_kdecD : computable tc_kdecD. Proof. extract. Qed.
Instance term_tc_kdecK : computable tc_kdecK. Proof. extract. Qed.
Instance term_tc_kdecM : computable tc_kdecM. Proof. extract. Qed.
Instance term_tc_kdec_op : computable tc_kdec_op. Proof. extract. Qed.
Instance term_tc_kdec : computable tc_kdec. Proof. extract. Qed.
Instance term_tc_kpcode : computable tc_kpcode. Proof. extract. Qed.
Instance term_tc_kpdec : computable tc_kpdec. Proof. extract. Qed.
Instance term_tc_rj : computable tc_rj. Proof. extract. Qed.
Instance term_tc_kri : computable tc_kri. Proof. extract. Qed.
Instance term_tc_kreloc : computable tc_kreloc. Proof. extract. Qed.
Instance term_tc_kmulblock : computable tc_kmulblock. Proof. extract. Qed.
Instance term_tc_kmulchain : computable tc_kmulchain. Proof. extract. Qed.
Instance term_tc_cn : computable tc_cn. Proof. extract. Qed.
Instance term_tc_knorm : computable tc_knorm. Proof. extract. Qed.
Instance term_tc_kspec_prog : computable tc_kspec_prog. Proof. extract. Qed.
Instance term_tc_kspec : computable tc_kspec. Proof. extract. Qed.
Instance term_tc_keval : computable tc_keval. Proof. extract. Qed.
Instance term_tc_kfeq : computable tc_kfeq. Proof. extract. Qed.
Instance term_tc_kmem : computable tc_kmem. Proof. extract. Qed.
Instance term_tc_kfetch : computable tc_kfetch. Proof. extract. Qed.
Instance term_tc_kexec : computable tc_kexec. Proof. extract. Qed.
Instance term_tc_kstep : computable tc_kstep. Proof. extract. Qed.
Instance term_tc_khalted : computable tc_khalted. Proof. extract. Qed.
Instance term_tc_krun : computable tc_krun. Proof. extract. Qed.
Instance term_tc_kstart : computable tc_kstart. Proof. extract. Qed.
Instance term_tc_kout : computable tc_kout. Proof. extract. Qed.
Instance term_tc_klog_go : computable tc_klog_go. Proof. extract. Qed.
Instance term_tc_klog : computable tc_klog. Proof. extract. Qed.
Instance term_tc_kpk : computable tc_kpk. Proof. extract. Qed.
Instance term_tc_ev : computable tc_ev. Proof. extract. Qed.
Instance term_tc_uev : computable tc_uev. Proof. extract. Qed.

Definition tc_uev2 (d fuel x c : nat) : option nat := tc_uev fuel x c.
Instance term_tc_uev2 : computable tc_uev2. Proof. extract. Qed.

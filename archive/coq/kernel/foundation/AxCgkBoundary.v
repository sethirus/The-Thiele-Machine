(** AxCgkBoundary: the exact boundary of what one run can carry.

    A run of the priced machine, and so a run of U_P, holds at most 16 facts
    (the fact table of the machine holds 16).  A chain of levels is carried by
    the fact table when, at every step of the driven run, the guest holds as
    many facts as there are levels latched.  Then:

      ax_guest_facts_cap      no guest program, from any start, ever holds more
                              than 16 facts;
      ax_thermo               a guest "carries the chain of C from s0 by its
                              facts": for every n with the driver not halted
                              before step n, some run length has exactly
                              ax_cm_lat n facts;
      ax_chain_boundary       a chain machine from s0 (with a presentation) is
                              carried by the facts of some guest program if
                              and only if the heights along the run from s0 are
                              at most 16.

    The direction "if" is the compile of AxCgkRun.v; the direction "only if"
    is the cap.  So the exact boundary of readings that can ride one run in the
    fact table is the table: 16 levels. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is part of the compiler pipeline for chain machines, built on the
   repository's compiler files (CompilerGuest.v and the files it uses). The
   statements that connect it to the axis and to the host that runs the chain
   are AxCgkAxis.v and AxCgkHost.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Require Import Kernel.CompilerCodes Kernel.CompilerChecker Kernel.CompilerLifts.
From Kernel Require Import AxChain AxCgkLang AxCgkGuest AxCgkRun.

Lemma ax_pr_run_cap : forall n (Q : list (@P.pr_instr cg_uprop)) (s : cg_ystate),
  length (G.facts (G.core_of s)) <= 16 ->
  length (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval n Q s))) <= 16.
Proof.
  induction n as [| n IH]; intros Q s H; [exact H |].
  simpl. apply IH. unfold P.pr_step. destruct (P.pr_next_instr Q (G.core_of s)) as [i |]; [| exact H].
  unfold P.pr_exec. cbn [G.core_of].
  exact (P.pr_facts_bounded_step cg_uprop_eqb cg_ueval _ i H).
Qed.

(** No guest program, from any clean start, holds more than 16 facts. *)
Theorem ax_guest_facts_cap : forall (Q : list (@P.pr_instr cg_uprop)) x y N,
  length (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N Q (G.start x y)))) <= 16.
Proof.
  intros Q x y N. apply ax_pr_run_cap. simpl. lia.
Qed.

Section Boundary.

Variable C : ax_chain_mach.
Variable s0 : ax_cm_st C.

Local Notation next := (ax_cm_next C).
Local Notation hh := (ax_cm_h C).

(** The guest carries the chain of C from s0 by its facts. *)
Definition ax_thermo (Q : list (@P.pr_instr cg_uprop)) (st0 : cg_ystate) : Prop :=
  forall n, (forall m, m < n -> next (ax_cm_run C s0 m) <> None) ->
    exists N, length (G.facts (G.core_of (P.pr_run_prog cg_uprop_eqb cg_ueval N Q st0))) = ax_cm_lat C s0 n.

Lemma ax_cm_first_halt : forall N,
  (forall m, m < N -> next (ax_cm_run C s0 m) <> None) \/
  (exists h, h < N /\ next (ax_cm_run C s0 h) = None /\
     forall m, m < h -> next (ax_cm_run C s0 m) <> None).
Proof.
  induction N as [| N IH].
  - left. intros m Hm. lia.
  - destruct IH as [H | (h & Hh & E & Hb)].
    + destruct (next (ax_cm_run C s0 N)) as [i |] eqn:E.
      * left. intros m Hm. destruct (Nat.eq_dec m N) as [-> | Hne]; [rewrite E; discriminate |].
        apply H. lia.
      * right. exists N. split; [lia |]. split; [exact E | exact H].
    + right. exists h. split; [lia |]. split; [exact E | exact Hb].
Qed.

(** The facts of a thermometer guest never exceed 16, so neither do the heights. *)
Theorem ax_thermo_bounded : forall Q x y,
  ax_thermo Q (G.start x y) -> ax_cm_bounded_from C s0.
Proof.
  intros Q x y Ht n.
  destruct (ax_cm_first_halt n) as [H | (h & Hh & E & Hb)].
  - destruct (Ht n H) as [N HN]. pose proof (ax_guest_facts_cap Q x y N) as Hc.
    pose proof (ax_cm_lat_ge_h C n s0). lia.
  - destruct (Ht h Hb) as [N HN]. pose proof (ax_guest_facts_cap Q x y N) as Hc.
    pose proof (ax_cm_lat_ge_h C h s0) as Hl.
    assert (Hr : ax_cm_run C s0 n = ax_cm_run C s0 h).
    { replace n with (h + (n - h)) by lia. rewrite ax_cm_run_add. apply ax_cm_run_halted. exact E. }
    rewrite Hr. lia.
Qed.

End Boundary.

(** The exact boundary. *)
Theorem ax_chain_boundary : forall (C : ax_chain_mach) (cp : ax_chain_pres C) (s0 : ax_cm_st C),
  ax_cm_bounded_from C s0 <->
  exists Q x y, ax_thermo C s0 Q (G.start x y).
Proof.
  intros C cp s0. split.
  - intros Hb. exists (ax_cgk_guest C cp), 0, (cg_gk (ax_cgk_k C cp) (ax_cgk_e0 C s0)).
    intros n Hn. destruct (ax_cgk_guest_matching_points C cp s0 Hb n Hn)
      as (N & _ & _ & _ & _ & _ & _ & _ & Hf & _).
    exists N. exact Hf.
  - intros (Q & x & y & Ht). exact (ax_thermo_bounded C s0 Q x y Ht).
Qed.

Print Assumptions ax_guest_facts_cap.
Print Assumptions ax_thermo_bounded.
Print Assumptions ax_chain_boundary.

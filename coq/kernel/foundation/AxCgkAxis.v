(** AxCgkAxis: a chain of thresholds of a growing record, carried in one run.

    An axis machine X with a presentation Q (AxUniversal.v) and a list of
    thresholds a_1, a_2, ... , a_k that is a chain in the order of the record
    (each at or below the next).  Its chain machine has the height

      h s = the number of thresholds reached from the bottom: the length of the
            longest prefix of the list all of whose members are at or below the
            record of s,

    so, for a sorted list, level j (the j-th threshold) holds at s exactly when
    a_j is at or below the record of s (ax_height_iff).  With a growing record
    the latched level is the level of the last state (ax_chain_levels).

    Results (all closed):

      ax_height_iff      level j holds exactly when the j-th threshold is at or
                         below the record, for a sorted list;
      ax_chain_levels    for a growing record, the j-th threshold is at or below
                         the record after n steps exactly when some state of
                         the first n + 1 reaches level j;
      ax_threshold_chain_host
                         if the chain has at most 16 thresholds and its reading
                         is computably presented, then one run of U_P carries
                         every threshold: at a matching host time the j-th
                         threshold is at or below the record after n steps
                         exactly when the host holds at least j facts, and the
                         host's ledger is the guest ledger of AxChain.v. *)

From Coq Require Import List Arith Lia Bool.
From Coq Require Import Sorting.Sorted.
Import ListNotations.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Minimal.EarnedGeneric Minimal.EarnedPriced.
Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
From Kernel Require Import AxCore AxUniversal AxChain AxCgkLang AxCgkGuest AxCgkRun AxHost AxCgkHost.

Section Bridge.

Context {A : Type} {P0 : BPre A}.
Variable X : AxSys A P0.
Variable Q : ax_presented X.
Variable thr : list A.

(** The number of thresholds reached from the bottom of the list. *)
Fixpoint ax_height (r : A) (l : list A) : nat :=
  match l with
  | [] => 0
  | a :: rest => if bp_leb A P0 a r then S (ax_height r rest) else 0
  end.

Lemma ax_height_iff : forall (l : list A) r,
  StronglySorted (fun a b => bp_le P0 a b) l ->
  forall j a, nth_error l j = Some a -> (S j <= ax_height r l <-> bp_le P0 a r).
Proof.
  induction l as [| a0 l IH]; intros r Hs j a Hn; [destruct j; discriminate |].
  inversion Hs as [| a0' l' Hs' Hall]; subst.
  destruct j as [| j].
  - simpl in Hn. injection Hn as Ha. subst a. simpl. unfold bp_le.
    destruct (bp_leb A P0 a0 r) eqn:E; split; intro H; [reflexivity | lia | lia | discriminate].
  - simpl in Hn. simpl.
    assert (Hin : In a l) by (eapply nth_error_In; exact Hn).
    pose proof (proj1 (Forall_forall _ _) Hall a Hin) as H0a.
    destruct (bp_leb A P0 a0 r) eqn:E.
    + rewrite <- (IH r Hs' j a Hn). lia.
    + split; [intros H; lia |].
      intros H. exfalso. unfold bp_le in H.
      pose proof (bp_trans A P0 a0 a r H0a H) as H1. rewrite E in H1. discriminate.
Qed.

(** The chain machine of the thresholds. *)
Definition ax_chain_machine : ax_chain_mach :=
  ax_mk_chain (ax_state A P0 X) (ax_instr A P0 X) (ax_step A P0 X) (ax_cost A P0 X)
    (fun s => ax_height (ax_rec A P0 X s) thr)
    (axp_next X Q) (axp_scode X Q) (axp_sdec X Q) (axp_icode X Q) (axp_idec X Q)
    (axp_sdec_scode X Q) (axp_idec_icode X Q).

Lemma ax_chain_run : forall n s,
  ax_cm_run ax_chain_machine s n = ax_prun X Q s n.
Proof.
  induction n as [| n IH]; intros s; [reflexivity |].
  simpl. destruct (axp_next X Q s) as [i |]; [apply IH | reflexivity].
Qed.

Lemma ax_cgk_prun_mono : ax_grows (X := X) -> forall m i s, i <= m ->
  bp_le P0 (ax_rec A P0 X (ax_prun X Q s i)) (ax_rec A P0 X (ax_prun X Q s m)).
Proof.
  intros Hg m. induction m as [| m IH]; intros i s Hi.
  - assert (i = 0) by lia. subst. apply bp_le_refl.
  - destruct (Nat.eq_dec i (S m)) as [-> | Hne]; [apply bp_le_refl |].
    eapply bp_le_trans; [apply IH; lia |].
    rewrite <- !ax_chain_run. rewrite (ax_cm_run_succ ax_chain_machine m s).
    destruct (ax_cm_next ax_chain_machine (ax_cm_run ax_chain_machine s m)) as [i0 |];
      [apply Hg | apply bp_le_refl].
Qed.

Theorem ax_chain_levels : ax_grows (X := X) -> StronglySorted (fun a b => bp_le P0 a b) thr ->
  forall s0 n j a, nth_error thr j = Some a ->
    ((exists i, i <= n /\ S j <= ax_cm_h ax_chain_machine (ax_cm_run ax_chain_machine s0 i)) <->
     bp_le P0 a (ax_rec A P0 X (ax_prun X Q s0 n))).
Proof.
  intros Hg Hs s0 n j a Hn. split.
  - intros [i [Hi Hh]]. simpl in Hh. rewrite ax_chain_run in Hh.
    apply (proj1 (ax_height_iff thr _ Hs j a Hn)) in Hh.
    eapply bp_le_trans; [exact Hh |]. apply ax_cgk_prun_mono; [exact Hg | exact Hi].
  - intros H. exists n. split; [lia |]. simpl. rewrite ax_chain_run.
    apply (proj2 (ax_height_iff thr _ Hs j a Hn)). exact H.
Qed.

End Bridge.

(** The chain of thresholds, carried by one run of U_P. *)
Theorem ax_threshold_chain_host :
  forall {A : Type} {P0 : BPre A} (X : AxSys A P0) (Q : ax_presented X) (thr : list A)
    (cp : ax_chain_pres (ax_chain_machine X Q thr)) (s0 : ax_state A P0 X),
  ax_grows (X := X) -> StronglySorted (fun a b => bp_le P0 a b) thr ->
  ax_cm_bounded_from (ax_chain_machine X Q thr) s0 ->
  forall n,
    (forall m, m < n -> axp_next X Q (ax_prun X Q s0 m) <> None) ->
    exists t,
      ax_cgk_decode (ax_chain_machine X Q thr) (hv (ax_cgk_host_at (ax_chain_machine X Q thr) cp s0 t) pu_RB)
        = Some (ax_prun X Q s0 n) /\
      (forall j a, nth_error thr j = Some a ->
         (bp_le P0 a (ax_rec A P0 X (ax_prun X Q s0 n)) <->
          S j <= length (M.facts (M.core_of (ax_cgk_host_at (ax_chain_machine X Q thr) cp s0 t))))) /\
      length (M.facts (M.core_of (ax_cgk_host_at (ax_chain_machine X Q thr) cp s0 t))) <= 16 /\
      M.mu (ax_cgk_host_at (ax_chain_machine X Q thr) cp s0 t) =
        ax_cm_gledger (ax_chain_machine X Q thr) s0 n.
Proof.
  intros A P0 X Q thr cp s0 Hg Hs Hb n Hn.
  assert (Hn' : forall m, m < n -> ax_cm_next (ax_chain_machine X Q thr) (ax_cm_run (ax_chain_machine X Q thr) s0 m) <> None).
  { intros m Hm. rewrite ax_chain_run. apply Hn. exact Hm. }
  destruct (ax_cgk_host_points (ax_chain_machine X Q thr) cp s0 Hb n Hn') as (t & Hd & Hmu & Hrec).
  exists t. split.
  - rewrite ax_chain_run in Hd. exact Hd.
  - split; [| split; [| exact Hmu]].
    + intros j a Hj. rewrite <- (ax_chain_levels X Q thr Hg Hs s0 n j a Hj).
      unfold ax_hrec in Hrec. injection Hrec as _ Hlen _ _. rewrite Hlen.
      rewrite <- (ax_cm_lat_iff (ax_chain_machine X Q thr) n s0 (S j)). reflexivity.
    + unfold ax_hrec in Hrec. injection Hrec as _ Hlen _ _. rewrite Hlen.
      exact (ax_cm_lat_le_from (ax_chain_machine X Q thr) s0 Hb n).
Qed.

Print Assumptions ax_height_iff.
Print Assumptions ax_chain_levels.
Print Assumptions ax_threshold_chain_host.

(** AxUniversal: one host runs every presented machine on the axis, one
    threshold at a time.

    A presented axis machine is an axis system that pays the toll, with a
    driver (the move to take in each state, or none to halt) and number
    codes for its states and moves.  Reading its record through the
    threshold a, "is a at or below the record", gives a presented machine of
    the book's kind.  The five-part universality of the book (the fixed
    program U_P runs every computably presented machine, with the guest's
    state, halting, flag and ledger exact up to the unavoidable surcharge)
    therefore applies to every threshold of every presented axis machine.

    Results (all closed):

      ax_view_run, ax_view_ledger   the thresholds are views of one run:
                              the driven run and the ledger do not depend
                              on which threshold is read.
      ax_view_latch_iff       on a growing record the latch of the
                              threshold a is up after n steps exactly when
                              a is at or below the record after n steps.
      ax_latches_determine_record  on an antisymmetric order the latches of
                              all thresholds after n steps determine the
                              record after n steps.
      ax_view_surcharge_le_two  from a start below the threshold the
                              surcharge is at most 2, for every threshold.
      ax_threshold_universal  the fixed host program U_P, loaded with the
                              compiled guest for the threshold a, reaches a
                              host state decoding to the guest's state after
                              n steps, with host ledger equal to the guest's
                              ledger plus the surcharge and host flag equal
                              to "a is at or below the guest's record after
                              n steps"; the host halts exactly when the
                              guest does; the flag rises exactly when the
                              guest's record gets to a.

    Where this stops.  The host has one flag, a one-point record, so one run
    of the host carries one threshold.  The whole record of the guest is
    carried by the family of runs, one per threshold, all on the same driven
    guest run.  A record that is a chain of three values cannot be carried
    by one flag (chain_needs_bits), so this is not a gap in the proof but a
    property of the host; a host whose own record is the axis is a different
    machine. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Kernel.Presentation Kernel.PresentedUniversal.
Module T := Minimal.ThieleComplete.

Section PresentedAxis.

Context {A : Type} {P : BPre A}.
Variable X : AxSys A P.
Variable Ha : ax_a2 (X := X).

Local Notation S := (ax_state A P X).
Local Notation I := (ax_instr A P X).

(** The data of a presentation, for an axis system. *)
Record ax_presented : Type := mk_axp {
  axp_next : S -> option I;
  axp_scode : S -> nat;
  axp_sdec : nat -> option S;
  axp_icode : I -> nat;
  axp_idec : nat -> option I;
  axp_sdec_scode : forall s, axp_sdec (axp_scode s) = Some s;
  axp_idec_icode : forall i, axp_idec (axp_icode i) = Some i
}.

Variable Q : ax_presented.

(** The presented machine of the book that reads the record through the
    threshold a. *)
Definition ax_view_cs (a : A) : T.CertificationSystem.
Proof.
  refine (T.mk_cert_system (ax_state A P X) (ax_instr A P X) (ax_step A P X)
    (ax_cost A P X) (fun s => bp_leb A P a (ax_rec A P X s)) _).
  intros s i H0 H1. apply (ax_view_a2 X Ha a s i). unfold ax_exits. intro Hle.
  unfold bp_le in Hle. simpl in Hle. rewrite H0, H1 in Hle. discriminate.
Defined.

Definition ax_view_presented (a : A) : presented_machine :=
  mk_presented (ax_view_cs a)
    (axp_next Q) (axp_scode Q) (axp_sdec Q) (axp_icode Q) (axp_idec Q)
    (axp_sdec_scode Q) (axp_idec_icode Q).

(** The driven run of the axis machine. *)
Fixpoint ax_prun (s : S) (n : nat) : S :=
  match n with
  | 0 => s
  | Datatypes.S n' =>
      match axp_next Q s with
      | None => s
      | Some i => ax_prun (ax_step A P X s i) n'
      end
  end.

Fixpoint ax_pledger (s : S) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S n' =>
      match axp_next Q s with
      | None => 0
      | Some i => ax_cost A P X i + ax_pledger (ax_step A P X s i) n'
      end
  end.

Theorem ax_view_run : forall a s n,
  presented_run (ax_view_presented a) s n = ax_prun s n.
Proof.
  intros a s n. revert s. induction n as [| n IH]; intro s; [reflexivity |].
  simpl. destruct (axp_next Q s) as [i |]; [apply IH | reflexivity].
Qed.

Theorem ax_view_ledger : forall a s n,
  mledger (ax_view_presented a) s n = ax_pledger s n.
Proof.
  intros a s n. revert s. induction n as [| n IH]; intro s; [reflexivity |].
  simpl. destruct (axp_next Q s) as [i |]; [| reflexivity].
  f_equal; try apply IH.
Qed.

Lemma ax_prun_grows : ax_grows (X := X) ->
  forall n s, bp_le P (ax_rec A P X s) (ax_rec A P X (ax_prun s n)).
Proof.
  intros Hg n. induction n as [| n IH]; intro s; simpl.
  - apply bp_le_refl.
  - destruct (axp_next Q s) as [i |]; [| apply bp_le_refl].
    eapply bp_le_trans; [apply Hg | apply IH].
Qed.

Lemma ax_prun_mono : ax_grows (X := X) ->
  forall m k s, bp_le P (ax_rec A P X (ax_prun s m)) (ax_rec A P X (ax_prun s (m + k))).
Proof.
  intros Hg m k. induction m as [| m IH]; intro s.
  - simpl. apply (ax_prun_grows Hg).
  - simpl. destruct (axp_next Q s) as [i |]; [apply IH | apply bp_le_refl].
Qed.

(** On a growing record the latch of a threshold is the statement that the
    threshold is at or below the record now. *)
Theorem ax_view_latch_iff : ax_grows (X := X) ->
  forall a s n,
    mlatch (ax_view_presented a) s n = true <->
    bp_le P a (ax_rec A P X (ax_prun s n)).
Proof.
  intros Hg a s n. rewrite presented_mlatch_iff. split.
  - intros [m [Hm Hr]]. rewrite ax_view_run in Hr.
    change (bp_leb A P a (ax_rec A P X (ax_prun s m)) = true) in Hr.
    assert (Hle : bp_le P a (ax_rec A P X (ax_prun s m))) by exact Hr.
    destruct (Nat.le_exists_sub m n Hm) as [k [Hk _]]. 
    replace n with (k + m) by lia. rewrite Nat.add_comm.
    eapply bp_le_trans; [exact Hle | apply (ax_prun_mono Hg)].
  - intro H. exists n. split; [lia |]. rewrite ax_view_run. exact H.
Qed.

(** On an antisymmetric order the latches of all the thresholds determine the
    record. *)
Theorem ax_latches_determine_record : bp_antisym P -> ax_grows (X := X) ->
  forall s t n,
    (forall a, mlatch (ax_view_presented a) s n = mlatch (ax_view_presented a) t n) ->
    ax_rec A P X (ax_prun s n) = ax_rec A P X (ax_prun t n).
Proof.
  intros Hanti Hg s t n H. apply (bp_thresholds_determine A P Hanti). intro a.
  pose proof (H a) as Ha'.
  destruct (bp_leb A P a (ax_rec A P X (ax_prun s n))) eqn:E1;
    destruct (bp_leb A P a (ax_rec A P X (ax_prun t n))) eqn:E2; try reflexivity.
  - exfalso. assert (mlatch (ax_view_presented a) s n = true)
      by (apply ax_view_latch_iff; [exact Hg | exact E1]).
    rewrite Ha' in H0. apply (ax_view_latch_iff Hg) in H0. unfold bp_le in H0.
    rewrite E2 in H0. discriminate.
  - exfalso. assert (mlatch (ax_view_presented a) t n = true)
      by (apply ax_view_latch_iff; [exact Hg | exact E2]).
    rewrite <- Ha' in H0. apply (ax_view_latch_iff Hg) in H0. unfold bp_le in H0.
    rewrite E1 in H0. discriminate.
Qed.

(** From a start below the threshold, the surcharge is at most 2. *)
Theorem ax_view_surcharge_le_two : forall a s n,
  bp_leb A P a (ax_rec A P X s) = false ->
  surcharge (ax_view_presented a) s n <= 2.
Proof.
  intros a s n H. apply presented_surcharge_le_two. exact H.
Qed.

(** One host program runs the presented axis machine, read at any threshold
    that has a computable test. *)
Theorem ax_threshold_universal : ax_grows (X := X) ->
  forall a (pc : cg_presentation (ax_view_presented a)) s0,
    ((exists t, UniversalPBridge.M.pu_halted UniversalPLayout.U_P
         (UniversalPBridge.M.core_of (pu_host_at (ax_view_presented a) pc s0 t)))
     <-> (exists n, mhalted (ax_view_presented a) s0 n)) /\
    (forall n,
       (forall m, m < n -> axp_next Q (ax_prun s0 m) <> None) ->
       exists t,
         pu_decode (ax_view_presented a)
           (UniversalPBridge.M.vals
              (UniversalPBridge.M.core_of (pu_host_at (ax_view_presented a) pc s0 t))
              UniversalPLayout.pu_RB) = Some (ax_prun s0 n) /\
         UniversalPBridge.M.mu (pu_host_at (ax_view_presented a) pc s0 t)
           = ax_pledger s0 n + surcharge (ax_view_presented a) s0 n /\
         (UniversalPBridge.M.cert (pu_host_at (ax_view_presented a) pc s0 t) = true <->
          bp_le P a (ax_rec A P X (ax_prun s0 n)))).
Proof.
  intros Hg a pc s0.
  destruct (presented_universal (ax_view_presented a) pc s0) as [Hh [Hp _]].
  split; [exact Hh |].
  intros n Hn.
  assert (Hn' : forall m, m < n -> pm_next (ax_view_presented a)
            (presented_run (ax_view_presented a) s0 m) <> None).
  { intros m Hm. rewrite ax_view_run. apply Hn. exact Hm. }
  destruct (Hp n Hn') as [t [Hd [Hmu Hc]]].
  exists t. rewrite ax_view_run in Hd. rewrite ax_view_ledger in Hmu.
  split; [exact Hd |]. split; [exact Hmu |].
  rewrite Hc. apply (ax_view_latch_iff Hg).
Qed.

End PresentedAxis.

Print Assumptions ax_view_run.
Print Assumptions ax_view_latch_iff.
Print Assumptions ax_latches_determine_record.
Print Assumptions ax_view_surcharge_le_two.
Print Assumptions ax_threshold_universal.

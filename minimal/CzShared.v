(** CzShared: a shared resource breaks the earned order.

    The product of two machines is Thiele-complete because the parts share
    nothing: a move of one part cannot change what a claim of the other part
    is about, so a chain CHECK, COMMIT, CERTIFY of one part survives any
    interleaving of the other part's moves.  This file shows what happens
    when the parts do share something.

    The small machine of EarnedCore.v is Thiele-complete
    ([Minimal.ThieleComplete.earned_core_thiele_complete]).  Its commit rule
    refuses a claim whose counter has been written since the check, because
    every ordinary write bumps the version.  Add one more party that writes
    the counter A without bumping its version, which is all that sharing the
    counter without sharing the discipline means.  The composite keeps its
    universal base and its exact toll, and the record can then be raised
    without an earned chain:

      cmpz_shared_base_toll    the base and toll clauses still hold;
      cmpz_shared_respect      a claim that held and whose object is unchanged
                               still holds (the checker clause);
      cmpz_shared_not_earned   the earned clause fails: the run
                               CHECK (A is 0), silent write, COMMIT,
                               CERTIFY raises the flag, and no
                               decomposition of it is an earned chain, since
                               the only candidate chain has the silent write
                               between its CHECK and its COMMIT.

    So the product law needs the parts to be disjoint, or at least needs
    every move of one part to leave unchanged whatever the other part's
    claims are about.  Disjointness is what [cmpz_iface] uses: a left claim is
    unchanged between two product states when it is unchanged between their
    left components, and a right move does not change the left component. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore.
Require Minimal.ThieleComplete.
Module E := Minimal.EarnedCore.
Module T := Minimal.ThieleComplete.

(** A write to counter A that does not bump its version. *)
Definition cmpz_silent (s : E.state) : E.state :=
  E.mkst
    (E.mkcore (S (E.ca (E.core_of s))) (E.cb (E.core_of s))
       (E.va (E.core_of s)) (E.vb (E.core_of s)) (E.pc (E.core_of s))
       (E.facts (E.core_of s)) (E.chan (E.core_of s)) (E.err (E.core_of s)))
    (E.mu s) (E.cert s).

(** The small machine and the party that shares its counter. *)
Definition cmpz_shared : T.machine :=
  T.mk_machine E.state (E.instr + unit)
    (fun s m => match m with inl i => E.exec s i | inr _ => cmpz_silent s end)
    (fun m => match m with inl i => E.cost i | inr _ => 0 end)
    E.cert.

Definition cmpz_shared_base : T.universal_base cmpz_shared :=
  T.mk_ub cmpz_shared (fun s => E.window (E.core_of s))
    (fun s => E.err (E.core_of s) = false)
    (fun i => inl (T.earned_compile i)) E.start
    (fun a b => eq_refl) (fun a b => eq_refl)
    (fun s i H => T.earned_sim s i H).

Definition cmpz_shared_interface : T.thiele_interface cmpz_shared :=
  T.mk_ti cmpz_shared cmpz_shared_base (E.prop * E.ctr)
    (fun m => match m with inl i => T.earned_kind i | inr _ => T.KBase end)
    (T.ti_meaning T.earned_interface) (T.ti_check T.earned_interface)
    (T.ti_same T.earned_interface) (T.ti_clean T.earned_interface)
    (T.ti_ledger T.earned_interface).

(** The universal base and the exact toll survive. *)
Theorem cmpz_shared_base_toll :
  T.universal_base_clause cmpz_shared_interface /\ T.exact_toll_clause cmpz_shared_interface.
Proof.
  split.
  - split; [intros [[|] | [|] j]; reflexivity |].
    split; [intros a b; apply E.start_clean |]. split.
    + intros s [m | u] Hk; simpl in Hk.
      * destruct m; simpl in Hk; try discriminate; simpl; apply orb_false_r.
      * reflexivity.
    + intros s [m | u] H; simpl in *.
      * apply E.cert_permanent, H.
      * exact H.
  - split; [intros [m | u]; [destruct m; reflexivity | reflexivity] |].
    intros s [m | u]; simpl.
    + apply E.mu_conservation.
    + lia.
Qed.

(** What a claim says is kept while its object is unchanged: the checker
    clause is still true. *)
Theorem cmpz_shared_respect :
  forall c s s', T.ti_same cmpz_shared_interface c s s' ->
    T.ti_meaning cmpz_shared_interface c s -> T.ti_meaning cmpz_shared_interface c s'.
Proof.
  intros [p c] s t [_ Hw] H. simpl in *. rewrite <- Hw. exact H.
Qed.

Definition cmpz_shared_trace : list (T.m_move cmpz_shared) :=
  [inl (E.CHECK E.PZero E.CA); inr tt; inl (E.COMMIT E.PZero E.CA); inl E.CERTIFY].

Lemma cmpz_shared_raises :
  T.m_record cmpz_shared (T.run cmpz_shared cmpz_shared_trace (E.start 0 0)) = true.
Proof. reflexivity. Qed.

(** The earned clause fails. *)
Theorem cmpz_shared_not_earned : ~ T.earned_record_clause cmpz_shared_interface.
Proof.
  intros [_ [Hch _]].
  assert (Hcl : T.ti_clean cmpz_shared_interface (E.start 0 0)) by apply E.start_clean.
  destruct (Hch (E.start 0 0) cmpz_shared_trace Hcl cmpz_shared_raises)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [K1 [K2 [K3 [Hck [Hsame _]]]]]]]]]]]]]].
  unfold cmpz_shared_trace in Htr.
  pose proof (f_equal (@length _) Htr) as Hlen.
  simpl in Hlen. repeat (rewrite app_length in Hlen; simpl in Hlen).
  destruct pre as [| p1 pre].
  - simpl in Htr. injection Htr as E1 Hrest.
    destruct mid1 as [| m1 mid1].
    + simpl in Hrest. injection Hrest as E2 _.
      rewrite <- E2 in K2. simpl in K2. discriminate K2.
    + simpl in Hrest. injection Hrest as E2 Hrest2.
      destruct mid1 as [| m2 mid1]; [| simpl in Hlen; lia ].
      simpl in Hrest2. injection Hrest2 as E3 Hrest3.
      subst chk m1. 
      specialize (Hsame [inr tt] []).
      assert (Hs : T.ti_same cmpz_shared_interface c
                (T.run cmpz_shared [] (E.start 0 0))
                (T.run cmpz_shared ([] ++ inl (E.CHECK E.PZero E.CA) :: [inr tt]) (E.start 0 0))).
      { apply Hsame. reflexivity. }
      simpl in K1. injection K1 as <-.
      destruct Hs as [_ Hv]. simpl in Hv. discriminate Hv.
  - simpl in Htr. injection Htr as E1 Hrest.
    destruct pre as [| p2 pre'].
    + simpl in Hrest. injection Hrest as E2 _.
      rewrite <- E2 in K1. simpl in K1. discriminate K1.
    + simpl in Hlen. lia.
Qed.

Print Assumptions cmpz_shared_base_toll.
Print Assumptions cmpz_shared_respect.
Print Assumptions cmpz_shared_not_earned.

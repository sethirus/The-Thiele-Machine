(** NecTGeneric.v: what the consequences of Thiele-complete need, and what the
    generic machine's hypotheses need.

    Results about every Thiele-complete machine (closed):

      [nec_t_a1_iff_free_given_toll]  given the cost half of the exact toll,
        "every compiled instruction is a base move" says exactly "every
        compiled instruction costs 0".
      [nec_t_clean_runs_need_three_moves]  from a clean state, every run of
        fewer than three moves leaves the record down. This strengthens
        one_move_record_excluded: it is enough for ONE move to raise the
        record from ONE clean state to exclude a machine, not from every
        state.
      [nec_t_costs_zero_and_one_attained]  both prices the toll allows, 0 and
        1, occur.

    Results about the generic machine of ThieleComplete.v read through its own
    interface (closed): each hypothesis of earned_generic_thiele_complete is
    needed by that interface.

      [nec_t_generic_needs_varying_property]  if every property that holds
        of one number holds of every number, the interface fails the
        non-vacuity clause.
      [nec_t_generic_needs_exact_eval]  if the checker says yes to a property
        that does not hold, the interface fails checker soundness.
      [nec_t_generic_needs_exact_eqb]  if the equality test on properties
        calls two different properties equal, the interface fails the earned
        chain: a CHECK of one property then a COMMIT of the other raises the
        record.
    These are statements about this interface. Whether some other interface
    could make such a machine Thiele-complete is not claimed. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Minimal.EarnedGeneric.
Module G := Minimal.EarnedGeneric.

(* ================================================================= *)
(* Consequences, for every Thiele-complete interface.                 *)
(* ================================================================= *)

Theorem nec_t_a1_iff_free_given_toll : forall M (I : thiele_interface M),
  (forall m, m_cost M m = record_move I m) ->
  ((forall i, ti_kind I (ub_compile (ti_base I) i) = KBase) <->
   (forall i, m_cost M (ub_compile (ti_base I) i) = 0)).
Proof.
  intros M I Hc. split.
  - intros Hk i. rewrite Hc. unfold record_move. rewrite (Hk i). reflexivity.
  - intros H0 i. specialize (H0 i). rewrite Hc in H0. unfold record_move in H0.
    destruct (ti_kind I (ub_compile (ti_base I) i)); [reflexivity | discriminate H0 ..].
Qed.

Theorem nec_t_clean_runs_need_three_moves : forall M (I : thiele_interface M),
  thiele_complete_with I ->
  forall s0 tr, ti_clean I s0 -> length tr < 3 -> m_record M (run M tr s0) = false.
Proof.
  intros M I HC s0 tr H0 Hlen.
  destruct (m_record M (run M tr s0)) eqn:E; [| reflexivity].
  exfalso. destruct (certificate_costs_three M I HC s0 tr H0 E) as [Hm _].
  assert (Hle : forall tr', record_moves I tr' <= length tr').
  { induction tr' as [| m tr' IH]; simpl; [lia |]. unfold record_move. destruct (ti_kind I m); lia. }
  specialize (Hle tr). lia.
Qed.

Theorem nec_t_costs_zero_and_one_attained : forall M,
  thiele_complete M ->
  (exists m : m_move M, m_cost M m = 0) /\ (exists m : m_move M, m_cost M m = 1) /\
  (forall m : m_move M, m_cost M m = 0 \/ m_cost M m = 1).
Proof.
  intros M HC. split; [apply complete_has_free_move, HC |]. split.
  - destruct HC as [I [_ [_ [[Hc _] [c [chk [cmt [crt [Hk1 _]]]]]]]]].
    exists chk. rewrite Hc. unfold record_move. rewrite Hk1. reflexivity.
  - intro m. pose proof (complete_costs_at_most_one M HC m). lia.
Qed.

(* ================================================================= *)
(* The generic machine's hypotheses.                                  *)
(* ================================================================= *)

Section GenericNeeds.

Context {prop : Type}.
Variable prop_eqb : prop -> prop -> bool.
Variable eval : prop -> nat -> bool.
Variable holds : prop -> nat -> Prop.

Theorem nec_t_generic_needs_varying_property :
  (forall p v w, holds p v -> holds p w) ->
  ~ thiele_complete_with (generic_interface prop_eqb eval holds).
Proof.
  intros Hconst [_ [_ [_ Hd]]].
  destruct Hd as [[p c] [chk [cmt [crt [_ [_ [_ [_ [[a [b Hyes]] [a' [b' Hno]]]]]]]]]]].
  apply Hno. unfold load in *. simpl in *.
  destruct c; simpl in *; eapply Hconst; exact Hyes.
Qed.

Theorem nec_t_generic_needs_exact_eval :
  (exists p v, eval p v = true /\ ~ holds p v) ->
  ~ thiele_complete_with (generic_interface prop_eqb eval holds).
Proof.
  intros [p [v [Hev Hnh]]] [_ [[_ [_ [Hsound _]]] _]].
  apply Hnh.
  specialize (Hsound (@G.start prop v 0) (p, G.CA)). simpl in Hsound.
  apply Hsound. unfold G.check_ok. simpl. rewrite Hev. reflexivity.
Qed.

Theorem nec_t_generic_needs_exact_eqb :
  (exists p q v, p <> q /\ prop_eqb q p = true /\ eval p v = true) ->
  ~ thiele_complete_with (generic_interface prop_eqb eval holds).
Proof.
  intros [p [q [v [Hne [Heq Hev]]]]] [_ [[_ [Hchain _]] _]].
  set (s0 := @G.start prop v 0).
  assert (Hrun : m_record (generic_machine prop_eqb eval)
                   (run (generic_machine prop_eqb eval)
                        [G.CHECK p G.CA; G.COMMIT q G.CA; G.CERTIFY] s0) = true).
  { rewrite (run_generic prop_eqb eval). simpl. unfold s0.
    unfold G.exec. simpl. unfold G.cexec. simpl.
    unfold G.check_ok. simpl. rewrite Hev. simpl.
    unfold G.commit_ok. simpl. unfold G.fact_eqb. simpl. rewrite Heq. simpl.
    unfold G.certify_ok. simpl. reflexivity. }
  destruct (Hchain s0 [G.CHECK p G.CA; G.COMMIT q G.CA; G.CERTIFY]
              (@G.generic_start_clean prop v 0) Hrun)
    as [pre [c [chk [mid1 [cmt [mid2 [crt [post [Htr [K1 [K2 _]]]]]]]]]]].
  assert (Hlen : @length (@G.instr prop) pre + @length (@G.instr prop) mid1 +
                 @length (@G.instr prop) mid2 + @length (@G.instr prop) post = 0).
  { apply (f_equal (@length (m_move (generic_machine prop_eqb eval)))) in Htr. simpl in Htr.
    autorewrite with list in Htr. simpl in Htr. autorewrite with list in Htr. simpl in Htr.
    autorewrite with list in Htr. simpl in Htr. lia. }
  destruct pre; [| simpl in Hlen; lia]. destruct mid1; [| simpl in Hlen; lia].
  destruct mid2; [| simpl in Hlen; lia]. destruct post; [| simpl in Hlen; lia].
  simpl in Htr. injection Htr as Hchk Hcmt _.
  subst chk cmt. unfold generic_interface in K1, K2. simpl in K1, K2.
  injection K1 as H1. injection K2 as H2. rewrite <- H1 in H2.
  injection H2 as Hpq. apply Hne. symmetry. exact Hpq.
Qed.

End GenericNeeds.

Print Assumptions nec_t_a1_iff_free_given_toll.
Print Assumptions nec_t_clean_runs_need_three_moves.
Print Assumptions nec_t_costs_zero_and_one_attained.
Print Assumptions nec_t_generic_needs_varying_property.
Print Assumptions nec_t_generic_needs_exact_eval.
Print Assumptions nec_t_generic_needs_exact_eqb.

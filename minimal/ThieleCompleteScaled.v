(** ThieleCompleteScaled.v: Thiele-complete at any unit price.

    Clause (c) of ThieleComplete.v fixes the unit: base moves cost 0 and
    each CHECK, COMMIT and CERTIFY costs exactly 1. Doubling every price of
    a Thiele-complete machine therefore takes it out of the class
    [doubled_earned_not_thiele_complete]. This file states the clause with
    the unit as a parameter: base moves cost 0 and every record move costs
    one fixed c, with c at least 1, and the ledger adds each move's cost.
    Everything else is the definition of ThieleComplete.v, clause for
    clause.

      thiele_complete_at_one     at c = 1 the new notion is the old one.
      scale_complete_at,         multiplying every price of a Thiele-complete
      unscale_complete           machine by c >= 1 gives a machine
                                 Thiele-complete at c, and dividing every
                                 price of a machine Thiele-complete at c by c
                                 gives a Thiele-complete machine with the
                                 same states, moves, step and record. So the
                                 class at unit c is the class at unit 1 with
                                 its prices multiplied by c, and nothing else.
      scaled_has_free_move,      at every unit a base move is free, so the
      clock_not_thiele_complete_at_any_unit
                                 clock, charging 1 per move with any reading,
                                 is Thiele-complete at no unit, and neither is
                                 any machine whose every move costs at least 1
                                 [paid_moves_not_thiele_complete_at_any_unit].
      scaled_certificate_costs_three_c
                                 a raised record from a clean start needs at
                                 least three record moves, and the ledger rises
                                 by at least 3c.
      scaled_committed_claim_holds, scaled_only_certify_raises
                                 the claim a raised record stands on held when
                                 it was checked and when it was committed, and
                                 the move that raises the record is a CERTIFY,
                                 at every unit.
      doubled_earned_scaled      the small machine with every price doubled is
                                 Thiele-complete at unit 2, and it is not
                                 Thiele-complete at unit 1
                                 [doubled_earned_not_thiele_complete].

    Dependencies: ThieleComplete.v. No axioms, no Admitted. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Import Minimal.ThieleComplete.

(* ================================================================= *)
(* The clause with the unit as a parameter.                           *)
(* ================================================================= *)

Section Scaled.

Variable M : machine.
Variable I : thiele_interface M.

(* (c) at unit c: base moves cost 0, every record move costs c, and the
   ledger adds each move's cost. *)
Definition scaled_toll_clause (c : nat) : Prop :=
  (forall m, m_cost M m = c * record_move I m) /\
  (forall s m, ti_ledger I (m_step M s m) = ti_ledger I s + m_cost M m).

Definition thiele_complete_at_with (c : nat) : Prop :=
  1 <= c /\ universal_base_clause I /\ earned_record_clause I /\
  scaled_toll_clause c /\ non_vacuity_clause I.

End Scaled.

Arguments scaled_toll_clause {M} I c.
Arguments thiele_complete_at_with {M} I c.

Definition thiele_complete_at (M : machine) (c : nat) : Prop :=
  exists I : thiele_interface M, thiele_complete_at_with I c.

(* Thiele-complete at some positive unit. *)
Definition thiele_complete_any_unit (M : machine) : Prop :=
  exists c, thiele_complete_at M c.

Theorem thiele_complete_at_one : forall M,
  thiele_complete_at M 1 <-> thiele_complete M.
Proof.
  intro M. split.
  - intros [I [_ [Ha [Hb [[Hc Hl] Hd]]]]]. exists I.
    split; [exact Ha |]. split; [exact Hb |]. split; [| exact Hd].
    split; [| exact Hl]. intro m. rewrite Hc. lia.
  - intros [I [Ha [Hb [[Hc Hl] Hd]]]]. exists I.
    split; [lia |]. split; [exact Ha |]. split; [exact Hb |]. split; [| exact Hd].
    split; [| exact Hl]. intro m. rewrite Hc. lia.
Qed.

Corollary thiele_complete_has_a_unit : forall M,
  thiele_complete M -> thiele_complete_any_unit M.
Proof. intros M H. exists 1. apply thiele_complete_at_one, H. Qed.

(* ================================================================= *)
(* Changing the unit.                                                  *)
(* ================================================================= *)

(* The same machine with every price multiplied by k. *)
Definition scale_machine (M : machine) (k : nat) : machine :=
  mk_machine (m_state M) (m_move M) (m_step M) (fun m => k * m_cost M m) (m_record M).

(* The same machine with every price divided by k. *)
Definition unscale_machine (M : machine) (k : nat) : machine :=
  mk_machine (m_state M) (m_move M) (m_step M) (fun m => m_cost M m / k) (m_record M).

Lemma run_scale : forall M k tr s, run (scale_machine M k) tr s = run M tr s.
Proof. intros M k tr. induction tr as [| m tr IH]; intro s; simpl; auto. Qed.

Lemma run_unscale : forall M k tr s, run (unscale_machine M k) tr s = run M tr s.
Proof. intros M k tr. induction tr as [| m tr IH]; intro s; simpl; auto. Qed.

(* An interface carried to a machine with the same states, moves, step and
   record; only the ledger is new. *)
Definition ub_scale {M} k (U : universal_base M) : universal_base (scale_machine M k) :=
  mk_ub (scale_machine M k) (ub_window U) (ub_live U) (ub_compile U) (ub_load U)
    (ub_load_window U) (ub_load_live U) (ub_sim U).

Definition ub_unscale {M} k (U : universal_base M) : universal_base (unscale_machine M k) :=
  mk_ub (unscale_machine M k) (ub_window U) (ub_live U) (ub_compile U) (ub_load U)
    (ub_load_window U) (ub_load_live U) (ub_sim U).

Definition ti_scale {M} k (I : thiele_interface M) : thiele_interface (scale_machine M k) :=
  mk_ti (scale_machine M k) (ub_scale k (ti_base I)) (ti_claim I) (ti_kind I)
    (ti_meaning I) (ti_check I) (ti_same I) (ti_clean I) (fun s => k * ti_ledger I s).

Definition ti_unscale {M} k (I : thiele_interface M) : thiele_interface (unscale_machine M k) :=
  mk_ti (unscale_machine M k) (ub_unscale k (ti_base I)) (ti_claim I) (ti_kind I)
    (ti_meaning I) (ti_check I) (ti_same I) (ti_clean I) (fun s => ti_ledger I s / k).

(* Clauses (a), (b) and (d) do not mention prices, so they carry over. *)
(* Definitional transports: scaling leaves these clauses unchanged. *)
Definition base_clause_scale : forall M k (I : thiele_interface M),
  universal_base_clause I -> universal_base_clause (ti_scale k I).
Proof. intros M k I H. exact H. Qed.

Definition base_clause_unscale : forall M k (I : thiele_interface M),
  universal_base_clause I -> universal_base_clause (ti_unscale k I).
Proof. intros M k I H. exact H. Qed.

Lemma earned_chain_scale : forall M k (I : thiele_interface M) s0 tr,
  earned_chain I s0 tr -> earned_chain (ti_scale k I) s0 tr.
Proof.
  intros M k I s0 tr [pre [c [chk [mid1 [cmt [mid2 [crt [post
                       [Htr [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, mid2, crt, post.
  repeat split; try assumption; simpl; rewrite ?run_scale; try assumption.
  intros t1 t2 E. rewrite !run_scale. exact (H5 t1 t2 E).
Qed.

Lemma earned_chain_unscale : forall M k (I : thiele_interface M) s0 tr,
  earned_chain I s0 tr -> earned_chain (ti_unscale k I) s0 tr.
Proof.
  intros M k I s0 tr [pre [c [chk [mid1 [cmt [mid2 [crt [post
                       [Htr [H1 [H2 [H3 [H4 [H5 [H6 H7]]]]]]]]]]]]]]].
  exists pre, c, chk, mid1, cmt, mid2, crt, post.
  repeat split; try assumption; simpl; rewrite ?run_unscale; try assumption.
  intros t1 t2 E. rewrite !run_unscale. exact (H5 t1 t2 E).
Qed.

Lemma record_clause_scale : forall M k (I : thiele_interface M),
  earned_record_clause I -> earned_record_clause (ti_scale k I).
Proof.
  intros M k I [H1 [H2 [H3 H4]]]. split; [exact H1 |]. split; [| split; assumption].
  intros s0 tr Hc Hr. apply earned_chain_scale. apply H2; [exact Hc |].
  rewrite run_scale in Hr. exact Hr.
Qed.

Lemma record_clause_unscale : forall M k (I : thiele_interface M),
  earned_record_clause I -> earned_record_clause (ti_unscale k I).
Proof.
  intros M k I [H1 [H2 [H3 H4]]]. split; [exact H1 |]. split; [| split; assumption].
  intros s0 tr Hc Hr. apply earned_chain_unscale. apply H2; [exact Hc |].
  rewrite run_unscale in Hr. exact Hr.
Qed.

Definition nonvac_clause_scale : forall M k (I : thiele_interface M),
  non_vacuity_clause I -> non_vacuity_clause (ti_scale k I).
Proof.
  intros M k I [c [chk [cmt [crt [H1 [H2 [H3 [H4 H5]]]]]]]].
  exists c, chk, cmt, crt. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  split; [| exact H5]. intros a b. rewrite run_scale. apply H4.
Qed.

Definition nonvac_clause_unscale : forall M k (I : thiele_interface M),
  non_vacuity_clause I -> non_vacuity_clause (ti_unscale k I).
Proof.
  intros M k I [c [chk [cmt [crt [H1 [H2 [H3 [H4 H5]]]]]]]].
  exists c, chk, cmt, crt. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
  split; [| exact H5]. intros a b. rewrite run_unscale. apply H4.
Qed.

(* Multiplying every price by c moves a machine from unit 1 to unit c. *)
Theorem scale_complete_at : forall M c,
  1 <= c -> thiele_complete M -> thiele_complete_at (scale_machine M c) c.
Proof.
  intros M c Hc [I [Ha [Hb [[Hcost Hled] Hd]]]]. exists (ti_scale c I).
  split; [exact Hc |].
  split; [apply base_clause_scale, Ha |].
  split; [apply record_clause_scale, Hb |].
  split; [| apply nonvac_clause_scale, Hd].
  split.
  - intro m. simpl. rewrite Hcost. reflexivity.
  - intros s m. simpl. rewrite Hled. lia.
Qed.

(* Dividing every price by c moves a machine from unit c to unit 1. *)
Theorem unscale_complete : forall M c,
  thiele_complete_at M c -> thiele_complete (unscale_machine M c).
Proof.
  intros M c [I [Hc [Ha [Hb [[Hcost Hled] Hd]]]]]. exists (ti_unscale c I).
  split; [apply base_clause_unscale, Ha |].
  split; [apply record_clause_unscale, Hb |].
  split; [| apply nonvac_clause_unscale, Hd].
  assert (Hdiv : forall m, m_cost M m / c = record_move I m).
  { intro m. rewrite Hcost, Nat.mul_comm. apply Nat.div_mul. lia. }
  split.
  - intro m. simpl. apply Hdiv.
  - intros s m. simpl. rewrite Hled, Hdiv, Hcost, Nat.mul_comm.
    apply Nat.div_add. lia.
Qed.

(* The divided machine is the original one with its prices divided: the
   same states, moves, step and record. *)
Lemma unscale_same_step : forall M c s m,
  m_step (unscale_machine M c) s m = m_step M s m /\
  m_record (unscale_machine M c) s = m_record M s.
Proof. intros. split; reflexivity. Qed.

(* ================================================================= *)
(* What every unit keeps.                                             *)
(* ================================================================= *)

Theorem scaled_has_free_move : forall M c,
  thiele_complete_at M c -> exists m : m_move M, m_cost M m = 0.
Proof.
  intros M c [I [_ [[Hk _] [_ [[Hcost _] _]]]]].
  exists (ub_compile (ti_base I) (CINC RA)). rewrite Hcost.
  unfold record_move. rewrite Hk. lia.
Qed.

(* No machine whose every move costs at least 1 is Thiele-complete at any
   unit. *)
Theorem paid_moves_not_thiele_complete_at_any_unit : forall M,
  (forall m : m_move M, m_cost M m >= 1) -> ~ thiele_complete_any_unit M.
Proof.
  intros M Hpaid [c Hc]. destruct (scaled_has_free_move M c Hc) as [m Hm].
  specialize (Hpaid m). lia.
Qed.

(* The clock fails at every unit. *)
Theorem clock_not_thiele_complete_at_any_unit : forall rd,
  ~ thiele_complete_any_unit (clock rd).
Proof.
  intro rd. apply paid_moves_not_thiele_complete_at_any_unit.
  intro m. simpl. lia.
Qed.

Theorem latch_clock_not_thiele_complete_at_any_unit : forall lt,
  ~ thiele_complete_any_unit (latch_clock lt).
Proof.
  intro lt. apply paid_moves_not_thiele_complete_at_any_unit.
  intro m. simpl. lia.
Qed.

Lemma scaled_ledger_counts : forall M (I : thiele_interface M) c,
  scaled_toll_clause I c ->
  forall tr s, ti_ledger I (run M tr s) = ti_ledger I s + c * record_moves I tr.
Proof.
  intros M I c [Hcost Hled] tr. induction tr as [| m tr IH]; intro s; simpl; [lia |].
  rewrite IH, Hled, Hcost. lia.
Qed.

Theorem scaled_certificate_costs_three_c : forall M (I : thiele_interface M) c,
  thiele_complete_at_with I c ->
  forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true ->
    record_moves I tr >= 3 /\ ti_ledger I (run M tr s0) >= ti_ledger I s0 + 3 * c.
Proof.
  intros M I c [Hc [_ [[_ [Hchain _]] [Htoll _]]]] s0 tr H0 H1.
  destruct (Hchain s0 tr H0 H1)
    as [pre [cl [chk [mid1 [cmt [mid2 [crt [post [Htr [Hk1 [Hk2 [Hk3 _]]]]]]]]]]]].
  assert (Hm : record_moves I tr >= 3).
  { rewrite Htr. repeat (rewrite record_moves_app; simpl).
    unfold record_move. rewrite Hk1, Hk2, Hk3. lia. }
  split; [exact Hm |]. rewrite (scaled_ledger_counts M I c Htoll).
  assert (c * record_moves I tr >= c * 3) by (apply Nat.mul_le_mono_l; lia). lia.
Qed.

(* The consequences that mention no price hold at every unit, read through
   the divided machine, which has the same runs. *)
Lemma unscale_with : forall M (I : thiele_interface M) c,
  thiele_complete_at_with I c -> thiele_complete_with (ti_unscale c I).
Proof.
  intros M I c [Hc [Ha [Hb [[Hcost Hled] Hd]]]].
  assert (Hdiv : forall m, m_cost M m / c = record_move I m).
  { intro m. rewrite Hcost, Nat.mul_comm. apply Nat.div_mul. lia. }
  split; [apply base_clause_unscale, Ha |].
  split; [apply record_clause_unscale, Hb |].
  split; [| apply nonvac_clause_unscale, Hd].
  split; [intro m; simpl; apply Hdiv |].
  intros s m. simpl. rewrite Hled, Hdiv, Hcost, Nat.mul_comm. apply Nat.div_add. lia.
Qed.

Theorem scaled_committed_claim_holds : forall M (I : thiele_interface M) c,
  thiele_complete_at_with I c ->
  forall s0 tr, ti_clean I s0 -> m_record M (run M tr s0) = true ->
  exists pre cl chk mid1 cmt rest,
    tr = pre ++ chk :: mid1 ++ cmt :: rest /\
    ti_kind I chk = KCheck cl /\ ti_kind I cmt = KCommit cl /\
    ti_meaning I cl (run M pre s0) /\ ti_meaning I cl (run M (pre ++ chk :: mid1) s0).
Proof.
  intros M I c HI s0 tr H0 H1.
  pose proof (unscale_with M I c HI) as HU.
  assert (H1' : m_record (unscale_machine M c) (run (unscale_machine M c) tr s0) = true)
    by (rewrite run_unscale; exact H1).
  destruct (committed_claim_holds _ _ HU s0 tr H0 H1')
    as [pre [cl [chk [mid1 [cmt [rest [Htr [Hk1 [Hk2 [Hm1 Hm2]]]]]]]]]].
  exists pre, cl, chk, mid1, cmt, rest. rewrite !run_unscale in *.
  repeat split; assumption.
Qed.

Theorem scaled_only_certify_raises : forall M (I : thiele_interface M) c,
  thiele_complete_at_with I c ->
  forall s0 tr m, ti_clean I s0 ->
    m_record M (run M tr s0) = false ->
    m_record M (m_step M (run M tr s0) m) = true ->
    ti_kind I m = KCertify.
Proof.
  intros M I c HI s0 tr m H0 Hdown Hup.
  pose proof (unscale_with M I c HI) as HU.
  apply (only_certify_raises _ _ HU s0 tr m H0); simpl; rewrite run_unscale; assumption.
Qed.

(* ================================================================= *)
(* The small machine with every price doubled.                        *)
(* ================================================================= *)

Definition doubled_earned : machine := scale_machine earned_machine 2.

Theorem doubled_earned_scaled : thiele_complete_at doubled_earned 2.
Proof. apply scale_complete_at; [lia | exact earned_core_thiele_complete]. Qed.

Theorem doubled_earned_not_thiele_complete : ~ thiele_complete doubled_earned.
Proof.
  intro H.
  destruct earned_core_thiele_complete as [I0 HI0].
  destruct (check_can_fail _ _ HI0) as [a [b [chk [c [Hk _]]]]].
  pose proof (complete_costs_at_most_one doubled_earned H chk) as Hle.
  destruct HI0 as [_ [_ [[Hcost _] _]]].
  simpl in Hle. rewrite Hcost in Hle. unfold record_move in Hle. rewrite Hk in Hle. lia.
Qed.

Print Assumptions thiele_complete_at_one.
Print Assumptions scale_complete_at.
Print Assumptions unscale_complete.
Print Assumptions scaled_has_free_move.
Print Assumptions paid_moves_not_thiele_complete_at_any_unit.
Print Assumptions clock_not_thiele_complete_at_any_unit.
Print Assumptions latch_clock_not_thiele_complete_at_any_unit.
Print Assumptions scaled_certificate_costs_three_c.
Print Assumptions scaled_committed_claim_holds.
Print Assumptions scaled_only_certify_raises.
Print Assumptions doubled_earned_scaled.
Print Assumptions doubled_earned_not_thiele_complete.

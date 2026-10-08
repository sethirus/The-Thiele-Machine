(** CzShadow: the shadow theorem for the product of two Thiele-complete
    machines.

    The shadow of an axis machine is the window of its universal base.  The
    four parts of the shadow theorem (AxComplete2) hold for every
    Thiele-complete machine, so they hold for the product, with the left
    window as the shadow ([cmpz_prod_shadow_theorem]).  The product has two
    windows, one per part, and the theorem holds for the pair as well: the
    record is not a function of the pair of shadows, the ledger is not, and
    every pair of shadow states is printed by a state at the floors of both
    parts.

      cmpz_prod_shadow_theorem          the four parts, for the product
      cmpz_pair_independence_left       the left record is not a function of
                                        the pair of windows
      cmpz_pair_independence_right      nor is the right record
      cmpz_pair_ledger_independence     nor is the ledger
      cmpz_pair_every_window_printed    every pair of shadow states is
                                        printed by a state at or below the
                                        floors of both parts, reached by two
                                        free moves from a clean start *)

From Coq Require Import List Bool Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import AxComplete2.
From Kernel Require Import CzProd CzProdTC.
Require Minimal.ThieleComplete.
Require Minimal.ThieleCompleteWindow.
Module T := Minimal.ThieleComplete.
Module W := Minimal.ThieleCompleteWindow.

Section ShadowProd.

Context {A B : Type} {P : BPre A} {Q : BPre B} {M : amachine A P} {N : amachine B Q}.
Variable I1 : ax_interface M.
Variable I2 : ax_interface N.
Hypothesis H1 : ax_tc_with I1.
Hypothesis H2 : ax_tc_with I2.

Local Notation I := (cmpz_iface I1 I2).

Definition cmpz_wpair (s : am_state (cmpz_prod M N)) : T.cm_conf * T.cm_conf :=
  (ax_window I1 (fst s), ax_window I2 (snd s)).

(** The four parts, for the product, with the left window as the shadow. *)
Theorem cmpz_prod_shadow_theorem :
  (~ exists f : T.cm_conf -> A * B, forall a b tr,
      am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr (ax_load I a b))
      = f (ax_window I (am_run (cmpz_prod M N) tr (ax_load I a b)))) /\
  (~ exists f : T.cm_conf -> nat, forall a b tr,
      axi_ledger I (am_run (cmpz_prod M N) tr (ax_load I a b))
      = f (ax_window I (am_run (cmpz_prod M N) tr (ax_load I a b)))) /\
  (forall is s, T.ub_live (axi_base I) s ->
     ax_window I (am_run (cmpz_prod M N) (map (T.ub_compile (axi_base I)) is) s)
       = W.cm_runl is (ax_window I s) /\
     T.ub_live (axi_base I) (am_run (cmpz_prod M N) (map (T.ub_compile (axi_base I)) is) s) /\
     am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) (map (T.ub_compile (axi_base I)) is) s)
       = am_rec (cmpz_prod M N) s /\
     axi_ledger I (am_run (cmpz_prod M N) (map (T.ub_compile (axi_base I)) is) s)
       = axi_ledger I s) /\
  (forall a, ~ bp_le (cmpz_pair_pre P Q) a (axi_floor I) ->
     forall s0 tr, axi_clean I s0 ->
       bp_le (cmpz_pair_pre P Q) a (am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr s0)) ->
       ax_record_moves I tr >= 3 /\
       axi_ledger I (am_run (cmpz_prod M N) tr s0) >= axi_ledger I s0 + 3).
Proof.
  pose proof (cmpz_prod_tc I1 I2 H1 H2) as HC.
  split; [exact (ax_tc_independence I HC) |].
  split; [exact (ax_tc_ledger_independence I HC) |].
  split; [exact (ax_tc_conservative I HC) |].
  exact (ax_tc_every_point_priced I HC).
Qed.

Theorem cmpz_pair_independence_left :
  ~ exists f : T.cm_conf * T.cm_conf -> A * B, forall a b c d tr,
      am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))
      = f (cmpz_wpair (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))).
Proof.
  intros [f Hf]. apply (ax_tc_independence I1 H1).
  exists (fun w => fst (f (w, ax_window I2 (ax_load I2 0 0)))).
  intros a b tr.
  specialize (Hf a b 0 0 (map inl tr)).
  rewrite cmpz_run_prod in Hf. unfold cmpz_wpair in Hf. cbn [fst snd] in Hf.
  rewrite (cmpz_lefts_map_inl (Y := am_move N)), (cmpz_rights_map_inl (Y := am_move N)) in Hf.
  exact (f_equal fst Hf).
Qed.

Theorem cmpz_pair_independence_right :
  ~ exists f : T.cm_conf * T.cm_conf -> A * B, forall a b c d tr,
      am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))
      = f (cmpz_wpair (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))).
Proof.
  intros [f Hf]. apply (ax_tc_independence I2 H2).
  exists (fun w => snd (f (ax_window I1 (ax_load I1 0 0), w))).
  intros c d tr.
  specialize (Hf 0 0 c d (map inr tr)).
  rewrite cmpz_run_prod in Hf. unfold cmpz_wpair in Hf. cbn [fst snd] in Hf.
  rewrite (cmpz_lefts_map_inr (X := am_move M)), (cmpz_rights_map_inr (X := am_move M)) in Hf.
  exact (f_equal snd Hf).
Qed.

Theorem cmpz_pair_ledger_independence :
  ~ exists f : T.cm_conf * T.cm_conf -> nat, forall a b c d tr,
      axi_ledger I (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))
      = f (cmpz_wpair (am_run (cmpz_prod M N) tr (ax_load I1 a b, ax_load I2 c d))).
Proof.
  intros [f Hf]. apply (ax_tc_ledger_independence I1 H1).
  exists (fun w => f (w, ax_window I2 (ax_load I2 0 0)) - axi_ledger I2 (ax_load I2 0 0)).
  intros a b tr.
  specialize (Hf a b 0 0 (map inl tr)).
  rewrite cmpz_run_prod in Hf. unfold cmpz_wpair in Hf. cbn [fst snd] in Hf.
  rewrite (cmpz_lefts_map_inl (Y := am_move N)), (cmpz_rights_map_inl (Y := am_move N)) in Hf.
  cbn in Hf. cbn. lia.
Qed.

(** Every pair of shadow states is printed by a state of the product at the
    floors of both parts, reached from a clean start by two moves that cost
    nothing. *)
Theorem cmpz_pair_every_window_printed : forall (s : am_state M) (t : am_state N),
  exists a b c d (m1 : am_move M) (m2 : am_move N),
    axi_clean I (ax_load I1 a b, ax_load I2 c d) /\
    axi_kind I1 m1 = T.KBase /\ axi_kind I2 m2 = T.KBase /\
    am_cost M m1 = 0 /\ am_cost N m2 = 0 /\
    cmpz_wpair (am_run (cmpz_prod M N) [inl m1; inr m2] (ax_load I1 a b, ax_load I2 c d))
      = (ax_window I1 s, ax_window I2 t) /\
    bp_le (cmpz_pair_pre P Q)
      (am_rec (cmpz_prod M N) (am_run (cmpz_prod M N) [inl m1; inr m2] (ax_load I1 a b, ax_load I2 c d)))
      (axi_floor I) /\
    axi_ledger I (am_run (cmpz_prod M N) [inl m1; inr m2] (ax_load I1 a b, ax_load I2 c d))
      = axi_ledger I (ax_load I1 a b, ax_load I2 c d).
Proof.
  intros s t.
  destruct (ax_tc_every_window_printed I1 H1 s) as [a [b [m1 [Hc1 [Hk1 [Hc01 [Hw1 [Hr1 Hl1]]]]]]]].
  destruct (ax_tc_every_window_printed I2 H2 t) as [c [d [m2 [Hc2 [Hk2 [Hc02 [Hw2 [Hr2 Hl2]]]]]]]].
  exists a, b, c, d, m1, m2.
  split; [split; assumption |]. split; [exact Hk1 |]. split; [exact Hk2 |].
  split; [exact Hc01 |]. split; [exact Hc02 |].
  split.
  - unfold cmpz_wpair. cbn. rewrite Hw1, Hw2. reflexivity.
  - split.
    + cbn. apply cmpz_pair_le. cbn. split; assumption.
    + cbn. lia.
Qed.

End ShadowProd.

Print Assumptions cmpz_prod_shadow_theorem.
Print Assumptions cmpz_pair_independence_left.
Print Assumptions cmpz_pair_independence_right.
Print Assumptions cmpz_pair_ledger_independence.
Print Assumptions cmpz_pair_every_window_printed.

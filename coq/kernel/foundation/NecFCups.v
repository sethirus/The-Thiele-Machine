(** NecFCups: the cups fix the place exactly when the order is partial.

    - In any preorder, two places each at or below the other leave the same
      cups up: for every a, [a <= x] = [a <= y] ([nec_f_same_rung_same_cups]).
    - So in every preorder that isn't partial, two different places leave the
      same cups up ([nec_f_non_partial_cups_fail]), and the cups fix the place
      if and only if the order is antisymmetric ([nec_f_cups_iff_partial]). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is order theory about the threshold readout of AxCore.v's preorders, the
   converse of [bp_thresholds_determine]. It touches no machine; AxCore.v is
   where the readout meets the record axis. *)

From Kernel Require Import AxCore.

Theorem nec_f_same_rung_same_cups : forall A (P : BPre A) x y,
  bp_le P x y -> bp_le P y x -> forall a, bp_leb A P a x = bp_leb A P a y.
Proof.
  intros A P x y Hxy Hyx a. unfold bp_le in *.
  destruct (bp_leb A P a x) eqn:Ex, (bp_leb A P a y) eqn:Ey; try reflexivity.
  - rewrite (bp_trans A P a x y Ex Hxy) in Ey. discriminate.
  - rewrite (bp_trans A P a y x Ey Hyx) in Ex. discriminate.
Qed.

Theorem nec_f_non_partial_cups_fail : forall A (P : BPre A),
  (exists x y, bp_le P x y /\ bp_le P y x /\ x <> y) ->
  exists x y, x <> y /\ forall a, bp_leb A P a x = bp_leb A P a y.
Proof.
  intros A P [x [y [Hxy [Hyx Hne]]]]. exists x, y.
  split; [exact Hne | exact (nec_f_same_rung_same_cups A P x y Hxy Hyx)].
Qed.

Theorem nec_f_cups_iff_partial : forall A (P : BPre A),
  (forall x y, (forall a, bp_leb A P a x = bp_leb A P a y) -> x = y) <->
  (forall u v, bp_le P u v -> bp_le P v u -> u = v).
Proof.
  intros A P. split.
  - intros Hcups u v Huv Hvu. apply Hcups. exact (nec_f_same_rung_same_cups A P u v Huv Hvu).
  - intros Hanti. exact (bp_thresholds_determine A P Hanti).
Qed.

Print Assumptions nec_f_same_rung_same_cups.
Print Assumptions nec_f_non_partial_cups_fail.
Print Assumptions nec_f_cups_iff_partial.

(** CrossCheck.v: not part of the deliverable. Compiled against the
    big build's VMStep.v, it confirms that the small machine's check is the
    big build's CHSH_LASSERT check, term for term. *)
From Kernel Require Import VMState VMStep.
Require Import ChshSmallX.SmallChshCheck.

Definition small_chsh_of_witness (wc : WitnessCounts) : small_chsh_tally :=
  small_chsh_mk wc.(wc_same_00) wc.(wc_diff_00) wc.(wc_same_01) wc.(wc_diff_01)
                wc.(wc_same_10) wc.(wc_diff_10) wc.(wc_same_11) wc.(wc_diff_11).

Theorem small_chsh_check_is_witness_check : forall wc,
  column_contractive_check_witness wc = small_chsh_check (small_chsh_of_witness wc).
Proof. intro wc. reflexivity. Qed.

Print Assumptions small_chsh_check_is_witness_check.

From Coq Require Import QArith Lia.

From ThieleMachine Require Import BellInequality.

Import QArith.
Open Scope Q_scope.

(** Bridge lemma: the concrete [TsirelsonApprox] box in [BellInequality]
    stays below the kernel’s rational Tsirelson threshold [5657/2000].

    This is an arithmetic consistency check between two layers’ constants:
    - ThieleMachine-level: [TsirelsonApprox] has CHSH = 4 * (7071/10000).
    - Kernel-level: [tsirelson_bound_q] is (5657/2000).
*)

Definition kernel_tsirelson_bound_q : Q := (5657#2000).

Lemma TsirelsonApprox_Qabs_le_kernel_bound :
  Qabs (S TsirelsonApprox) <= kernel_tsirelson_bound_q.
Proof.
  unfold kernel_tsirelson_bound_q.
  (* Reduce to a Z inequality via Qle’s cross-multiplication. *)
  setoid_replace (Qabs (S TsirelsonApprox)) with ((4#1) * tsirelson_gamma)
    by exact TsirelsonApprox_Qabs.
  unfold tsirelson_gamma.
  unfold Qle. simpl. lia.
Qed.

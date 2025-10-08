(* ================================================================= *)
(* Formal cost separation between blind Turing search and sighted     *)
(* Thiele Machine execution on Tseitin formulas over expander graphs. *)
(* ================================================================= *)
From Coq Require Import List Arith Lia Psatz Ring.

(* ----------------------------------------------------------------- *)
(* Problem family: Tseitin contradictions on degree-3 expanders.     *)
(* We model only the structural data that matters for cost analysis:  *)
(* the number of vertices (which coincides with the number of parity  *)
(* constraints) and an abstract charge function.                      *)
(* ----------------------------------------------------------------- *)

Record ExpanderGraph := {
  vertex_count : nat;
  degree : nat; (* kept symbolic; concrete instances fix this to 3 *)
}.

Record TseitinInstance := {
  exp_graph : ExpanderGraph;
  charge : nat -> bool;
}.

Definition instance_size (inst : TseitinInstance) : nat :=
  vertex_count (exp_graph inst).

(* Canonical family used for the separation theorem.  We work with a   *)
(* minimal degree-3 expander whose vertex count is [max 3 n]; the      *)
(* actual edge list and charge parity are abstracted because the       *)
(* complexity argument depends only on the asymptotic size.            *)
Definition canonical_charge (n : nat) : nat -> bool :=
  fun v => Nat.odd (v + n).

Definition tseitin_family (n : nat) : TseitinInstance :=
  {| exp_graph := {| vertex_count := Nat.max 3 n; degree := 3 |};
     charge := canonical_charge n |}.

(* ----------------------------------------------------------------- *)
(* Blind baseline: classical DPLL-style exploration.                   *)
(* ----------------------------------------------------------------- *)
Parameter turing_blind_steps : TseitinInstance -> nat.

(* The lower bound is postulated as an explicit axiom.  It captures the *)
(* widely believed exponential complexity of Tseitin formulas on       *)
(* expanders for any solver that cannot observe the global parity      *)
(* structure.                                                          *)
Axiom turing_tseitin_is_exponential :
  exists (N : nat), forall n, n >= N ->
    turing_blind_steps (tseitin_family n) >= Nat.pow 2 n.

Definition partitions_discovered (n : nat) : nat := 3 * n.
Definition partition_cost (n : nat) : nat := partitions_discovered n.

Definition mdlacc_cost (n : nat) : nat := 2 * n.

Definition local_assertions (n : nat) : nat := 4 * n.
Definition local_assert_cost (n : nat) : nat := 8 * n.

Definition gaussian_elimination_steps (n : nat) : nat := n * n * n.
Definition consistency_checks (n : nat) : nat := 2 * n * n.

Definition thiele_sighted_steps (inst : TseitinInstance) : nat :=
  let n := instance_size inst in
  partition_cost n
  + mdlacc_cost n
  + local_assert_cost n
  + gaussian_elimination_steps n
  + consistency_checks n.

Definition thiele_mu_cost (inst : TseitinInstance) : nat :=
  let n := instance_size inst in
  (mdlacc_cost n) + (2 * n * n).

Definition cubic (n : nat) : nat := (S n) * (S n) * (S n).
Definition quadratic (n : nat) : nat := (S n) * (S n).

(* Fixed numeric constants for the polynomial bounds. *)
Definition thiele_C : nat := 24.
Definition thiele_D : nat := 6.

Require Import ZArith.
Open Scope Z_scope.

Lemma thiele_sighted_steps_polynomial_forall_Z : forall (n : nat),
  Z.of_nat (thiele_sighted_steps (tseitin_family n)) <= Z.of_nat (thiele_C * cubic (instance_size (tseitin_family n))).
Proof.
  intros n.
  apply Nat2Z.inj_le.
  destruct (Nat.le_ge_cases 3 n) as [H|H].
  - (* n >= 3 : reduce to nat induction on n - 3 *)
    unfold thiele_sighted_steps, instance_size, partition_cost, mdlacc_cost, local_assert_cost, gaussian_elimination_steps, consistency_checks, cubic, thiele_C, tseitin_family.
    rewrite Nat.max_r by lia.
    rewrite <- (Nat.sub_add 3 n H).
    induction (Nat.sub n 3) as [|k IH]; simpl; lia.
  - (* n < 3 : instance_size = 3, numeric check *)
    unfold thiele_sighted_steps, instance_size, partition_cost, mdlacc_cost, local_assert_cost, gaussian_elimination_steps, consistency_checks, cubic, thiele_C, tseitin_family.
    rewrite Nat.max_l by lia.
    simpl; lia.
Qed.

Lemma thiele_mu_cost_quadratic_forall_Z : forall (n : nat),
  Z.of_nat (thiele_mu_cost (tseitin_family n)) <= Z.of_nat (thiele_D * quadratic (instance_size (tseitin_family n))).
Proof.
  intros n.
  apply Nat2Z.inj_le.
  destruct (Nat.le_ge_cases 3 n) as [H|H].
  - unfold thiele_mu_cost, instance_size, mdlacc_cost, quadratic, thiele_D, tseitin_family.
    rewrite Nat.max_r by lia.
    rewrite <- (Nat.sub_add 3 n H).
    induction (Nat.sub n 3) as [|k IH]; simpl; lia.
  - unfold thiele_mu_cost, instance_size, mdlacc_cost, quadratic, thiele_D, tseitin_family.
    rewrite Nat.max_l by lia.
    simpl; lia.
Qed.

(* Nat-level polynomial bounds (useful to avoid Z/nat conversion issues). *)
Lemma thiele_sighted_steps_polynomial_forall : forall (n : nat),
  (thiele_sighted_steps (tseitin_family n) <= thiele_C * cubic (instance_size (tseitin_family n)))%nat.
Proof.
  intros n.
  destruct (Nat.le_ge_cases 3 n) as [H|H].
  - unfold thiele_sighted_steps, instance_size, partition_cost, mdlacc_cost, local_assert_cost, gaussian_elimination_steps, consistency_checks, cubic, thiele_C, tseitin_family.
    rewrite Nat.max_r by lia.
    rewrite <- (Nat.sub_add 3 n H).
    induction (Nat.sub n 3) as [|k IH]; simpl; lia.
  - unfold thiele_sighted_steps, instance_size, partition_cost, mdlacc_cost, local_assert_cost, gaussian_elimination_steps, consistency_checks, cubic, thiele_C, tseitin_family.
    rewrite Nat.max_l by lia.
    simpl; lia.
Qed.

Lemma thiele_mu_cost_quadratic_forall : forall (n : nat),
  (thiele_mu_cost (tseitin_family n) <= thiele_D * quadratic (instance_size (tseitin_family n)))%nat.
Proof.
  intros n.
  destruct (Nat.le_ge_cases 3 n) as [H|H].
  - unfold thiele_mu_cost, instance_size, mdlacc_cost, quadratic, thiele_D, tseitin_family.
    rewrite Nat.max_r by lia.
    rewrite <- (Nat.sub_add 3 n H).
    induction (Nat.sub n 3) as [|k IH]; simpl; lia.
  - unfold thiele_mu_cost, instance_size, mdlacc_cost, quadratic, thiele_D, tseitin_family.
    rewrite Nat.max_l by lia.
    simpl; lia.
Qed.

Theorem thiele_exponential_separation :
  exists (N C D : nat), forall (n : nat), (n >= N)%nat ->
    (thiele_sighted_steps (tseitin_family n) <= C * cubic n)%nat /\
    (thiele_mu_cost (tseitin_family n) <= D * quadratic n)%nat /\
    (turing_blind_steps (tseitin_family n) >= Nat.pow 2 n)%nat.
Proof.
  destruct turing_tseitin_is_exponential as [N Hexp].
  set (N' := Nat.max N 3).
  exists N'; exists thiele_C; exists thiele_D.
  intros n Hn.
  repeat split.
  - (* sighted steps bound: case on Nat.max 3 n *)
    unfold instance_size, tseitin_family in *.
    destruct (Nat.le_ge_cases 3 n) as [H|H].
    + (* n >= 3 *)
      (* Reduce [instance_size] to [n], convert the goal to a Z-of-nat
         goal and apply the proved Z-lemma. *)
  pose proof (thiele_sighted_steps_polynomial_forall n) as Hs.
  unfold instance_size, tseitin_family in Hs.
  rewrite Nat.max_r in Hs by lia.
  rewrite Nat.max_r in * by lia.
  simpl in Hs.
  exact Hs.
    + (* n < 3, check numerically with instance_size = 3 *)
      rewrite Nat.max_l by lia.
      unfold thiele_sighted_steps, partition_cost, mdlacc_cost, local_assert_cost, gaussian_elimination_steps, consistency_checks; simpl; lia.
  - (* mu cost bound: same pattern *)
    unfold instance_size, tseitin_family in *.
    destruct (Nat.le_ge_cases 3 n) as [H|H].
    + (* n >= 3: reduce instance_size and apply the quadratic Z-lemma *)
      pose proof (thiele_mu_cost_quadratic_forall n) as Hm.
      unfold instance_size, tseitin_family in Hm.
      rewrite Nat.max_r in Hm by lia.
      rewrite Nat.max_r in * by lia.
      simpl in Hm.
      exact Hm.
    + rewrite Nat.max_l by lia.
      unfold thiele_mu_cost, mdlacc_cost; simpl; lia.
  - (* turing exponential axiom applied after strengthening N to N' *)
    apply Hexp; lia.
Qed.

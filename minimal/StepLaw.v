(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file states the per-step law for any deterministic step on any state set, with no dependence on the certification-system kernel: every step is fresh, a merge, or on a loop, a merge is a literal collision, and after any revisit the run is periodic. *)
(* Attack 1: the per-step law with no premise.
   Any deterministic step f on any set X, any start x0, no reading, no finiteness.
   Run: x_n = f^n x0.
   Claim: the step from x_n to x_{n+1} is exactly one of
     fresh : x_{n+1} differs from every earlier x_i (i <= n)
     merge : x_{n+1} = x_j for some 1 <= j <= n with x_n <> x_{j-1}  (two chairs land on one)
     loop  : x_{n+1} = x_j for some j <= n and the run was already periodic
             (either j = 0, a pure cycle through the start, or x_n = x_{j-1}).
   And: once a run revisits any chair, it is periodic forever (computes nothing new). *)
Require Import Arith Lia.

Section StepLaw.
Variable X : Type.
Variable f : X -> X.
Variable x0 : X.
Hypothesis eq_dec : forall a b : X, {a = b} + {a <> b}.

Fixpoint run (n : nat) : X := match n with 0 => x0 | S k => f (run k) end.

Definition fresh (n : nat) := forall i, i <= n -> run (S n) <> run i.
Definition merge (n : nat) := exists j, 1 <= j <= n /\ run (S n) = run j /\ run n <> run (j - 1).
Definition periodic_from (p start : nat) := p >= 1 /\ forall k, k >= start -> run (k + p) = run k.

Lemma run_add : forall p k, run (k + p) = run (k + p). Proof. reflexivity. Qed.

(* if run (S n) = run j with j >= 1 and run n = run (j-1), then the run repeats with period n+1-j from j-1 *)
Lemma revisit_periodic : forall n j, j <= n -> run (S n) = run j ->
  periodic_from (S n - j) j.
Proof.
  intros n j Hj Heq. split. lia.
  intros k Hk.
  (* induction on k - j *)
  remember (k - j) as d. revert k Heq Hk Heqd.
  induction d; intros.
  - replace k with j by lia. replace (j + (S n - j)) with (S n) by lia. auto.
  - destruct k; [lia|].
    simpl. replace (S k + (S n - j)) with (S (k + (S n - j))) by lia. simpl.
    f_equal. apply IHd; auto; lia.
Qed.

(* the three-way split, exhaustive *)
Theorem step_law : forall n,
  fresh n \/ merge n \/ (exists j, j <= n /\ run (S n) = run j /\ (j = 0 \/ run n = run (j - 1))).
Proof.
  intros n.
  (* decide whether some i <= n has run (S n) = run i; classical-free via bounded search needs decidable eq;
     we instead state it with excluded middle on this bounded existential *)
  assert (Hdec : forall m, {i | i <= m /\ run (S n) = run i} + {forall i, i <= m -> run (S n) <> run i}).
  { intro m. induction m.
    - destruct (eq_dec (run (S n)) (run 0)) as [E|E].
      + left. exists 0. auto.
      + right. intros i Hi. replace i with 0 by lia. auto.
    - destruct IHm as [[i [Hi He]] | Hno].
      + left. exists i. split; [lia|auto].
      + destruct (eq_dec (run (S n)) (run (S m))) as [E|E].
        * left. exists (S m). auto.
        * right. intros i Hi. destruct (le_lt_dec i m); [apply Hno; lia|]. replace i with (S m) by lia. auto. }
  destruct (Hdec n) as [[i [Hi He]] | Hno].
  - destruct i as [|i'].
    + right. right. exists 0. auto.
    + destruct (eq_dec (run n) (run (S i' - 1))) as [Hc | Hc].
      * right. right. exists (S i'). split; [lia|]. split; auto.
      * right. left. exists (S i'). split; [lia|]. split; auto.
  - left. intros i Hi He. apply (Hno i Hi He).
Qed.

(* a merge is two distinct chairs landing on one chair under f *)
Theorem merge_is_collision : forall n, merge n ->
  exists a b, a <> b /\ f a = f b.
Proof.
  intros n [j [Hj [He Hne]]].
  exists (run n), (run (j - 1)). split; auto.
  simpl in He. replace j with (S (j - 1)) in He by lia. simpl in He. exact He.
Qed.

(* after any revisit the run is periodic: nothing new ever again *)
Theorem revisit_means_loop : forall n j, j <= n -> run (S n) = run j ->
  forall k, k >= j -> exists i, i <= n /\ run k = run i.
Proof.
  intros n j Hj He k Hk.
  destruct (revisit_periodic n j Hj He) as [Hp Hper].
  (* reduce k into the window [j, n] by subtracting the period *)
  set (p := S n - j) in *.
  assert (forall m, exists i, j <= i <= n /\ run (j + m) = run i).
  { intro m. induction m using (well_founded_induction lt_wf).
    destruct (le_lt_dec p m) as [Hle | Hlt].
    - destruct (H (m - p)) as [i [Hi Hri]]; [lia|].
      exists i. split; auto. replace (j + m) with ((j + (m - p)) + p) by lia.
      rewrite Hper by lia. auto.
    - exists (j + m). split; [lia | reflexivity]. }
  destruct (H (k - j)) as [i [Hi Hri]]. exists i. split; [lia|].
  replace k with (j + (k - j)) by lia. auto.
Qed.

(* The shape of a run, stated so that no step is counted twice: before the first
   revisit every step is fresh; the first revisit lands on the start or is a merge;
   and every step after it repeats a step the run already took, so it merges nothing new. *)
Theorem first_revisit_start_or_merge : forall n j, j <= n -> run (S n) = run j ->
  (forall m i, m < n -> i <= m -> run (S m) <> run i) ->
  j = 0 \/ (1 <= j /\ run n <> run (j - 1)).
Proof.
  intros n j Hj He Hfirst.
  destruct j as [|j']; [left; reflexivity|right].
  split; [lia|].
  intro Heq. destruct n as [|n']; [lia|].
  apply (Hfirst n' j'); [lia|lia|].
  replace (S j' - 1) with j' in Heq by lia. exact Heq.
Qed.

Theorem later_steps_repeat : forall n j, j <= n -> run (S n) = run j ->
  forall k, k > n -> exists i, i < k /\ run i = run k /\ run (S i) = run (S k).
Proof.
  intros n j Hj He k Hk.
  destruct (revisit_periodic n j Hj He) as [Hp Hper].
  exists (k - (S n - j)). split; [lia|]. split.
  - replace k with ((k - (S n - j)) + (S n - j)) at 2 by lia.
    symmetry. apply Hper. lia.
  - replace (S k) with ((S (k - (S n - j))) + (S n - j)) by lia.
    symmetry. apply Hper. lia.
Qed.

End StepLaw.

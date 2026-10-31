(** CostFrameworks: the certification law against four cost frameworks.

    [CostSemanticsComparison] shows the ledger is a writer and A2 is a
    lower-bound potential argument. This file finishes the comparison with
    four frameworks, each stated as a theorem.

    - Graded monads. With costs indexed by instruction, a trace's run has
      its total cost as a grade in its type ([run_graded]): the ledger is a
      graded writer, with the grade known before the run.
    - Danner and Licata's cost semantics. Their translation of a step
      function pairs each result with its cost, which is the writer
      computation of [CostSemanticsComparison] ([run_writer_is_run_and_cost]).
      Their bounding relation and denotational models are not embedded.
    - Amortized resource analysis. AARA bounds cost from above: initial
      potential pays for cost plus final potential. A2 is the lower-bound
      direction. With the same certification potential, both at once hold
      exactly when every certification costs one, every other step costs
      zero, and nothing is ever uncertified ([a2_and_aara_iff_exact]). So
      the upper direction adds exact pricing and permanence to A2.
    - Linear resources. Under A2 the number of certifications along any
      trace is at most the trace's total cost ([flips_le_cost]): each
      certification consumes a unit, and a unit is spent once. *)

(* SCOPE NOTE: standalone proof scope. The comparison with the four
   frameworks is stated over any step function, cost, and reading, so it
   imports no machine semantics; [CostSemanticsComparison] connects the same
   reasoning to [CertificationSystem]. *)

From Coq Require Import List Arith.PeanoNat Lia Bool.
Import ListNotations.

(** * Graded monads *)

Section Graded.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.

(** A computation graded by its cost: the grade is in the type. *)
Definition GW (g : nat) (A : Type) : Type := A.

Definition gret {A} (a : A) : GW 0 A := a.

Definition gbind {A B g h} (m : GW g A) (k : A -> GW h B) : GW (g + h) B := k m.

Fixpoint total (t : list I) : nat :=
  match t with [] => 0 | i :: t' => cost i + total t' end.

(** Running a trace is a computation whose grade is the trace's total cost. *)
Fixpoint run_graded (t : list I) (s : S) : GW (total t) S :=
  match t as t0 return GW (total t0) S with
  | [] => gret s
  | i :: t' => gbind (g := cost i) (step s i : GW (cost i) S) (run_graded t')
  end.

Fixpoint run (t : list I) (s : S) : S :=
  match t with [] => s | i :: t' => run t' (step s i) end.

Theorem run_graded_is_run : forall t s, run_graded t s = run t s.
Proof. induction t as [| i t IH]; intro s; [reflexivity | exact (IH (step s i))]. Qed.

End Graded.

(** * Upper and lower potential arguments *)

Section Potential.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : S -> I -> nat.
Variable cert : S -> bool.

Definition flips (s : S) (i : I) : bool := negb (cert s) && cert (step s i).

(** One on uncertified states, zero on certified ones. *)
Definition phi (s : S) : nat := if cert s then 0 else 1.

(** A2, with state-dependent costs. *)
Definition a2 : Prop := forall s i, flips s i = true -> cost s i >= 1.

(** AARA's condition with the certification potential: the potential
    before a step pays for its cost and the potential after. *)
Definition aara_upper : Prop := forall s i, phi s >= cost s i + phi (step s i).

Definition exact_and_permanent : Prop :=
  (forall s i, flips s i = true -> cost s i = 1) /\
  (forall s i, flips s i = false -> cost s i = 0) /\
  (forall s i, cert s = true -> cert (step s i) = true).

Theorem a2_and_aara_iff_exact : a2 /\ aara_upper <-> exact_and_permanent.
Proof.
  unfold a2, aara_upper, exact_and_permanent, flips, phi. split.
  - intros [Ha2 Hup]. split; [| split].
    + intros s i Hf. specialize (Ha2 s i Hf). specialize (Hup s i).
      destruct (cert s), (cert (step s i)); simpl in *; try discriminate; lia.
    + intros s i Hf. specialize (Hup s i).
      destruct (cert s) eqn:Hc, (cert (step s i)) eqn:Hc'; simpl in *; try discriminate; lia.
    + intros s i Hc. specialize (Hup s i). rewrite Hc in Hup.
      destruct (cert (step s i)); [reflexivity | lia].
  - intros [Hexact [Hzero Hperm]]. split.
    + intros s i Hf. rewrite (Hexact s i Hf). lia.
    + intros s i. destruct (flips s i) eqn:Hf.
      * rewrite (Hexact s i Hf). unfold flips in Hf.
        destruct (cert s), (cert (step s i)); simpl in *; try discriminate; lia.
      * rewrite (Hzero s i Hf).
        destruct (cert s) eqn:Hc.
        -- rewrite (Hperm s i Hc). lia.
        -- unfold flips in Hf. rewrite Hc in Hf. simpl in Hf. rewrite Hf. lia.
Qed.

(** * Linear resources *)

Fixpoint run2 (t : list I) (s : S) : S :=
  match t with [] => s | i :: t' => run2 t' (step s i) end.

Fixpoint trace_cost (t : list I) (s : S) : nat :=
  match t with [] => 0 | i :: t' => cost s i + trace_cost t' (step s i) end.

Fixpoint flip_count (t : list I) (s : S) : nat :=
  match t with
  | [] => 0
  | i :: t' => (if flips s i then 1 else 0) + flip_count t' (step s i)
  end.

Theorem flips_le_cost : a2 -> forall t s, flip_count t s <= trace_cost t s.
Proof.
  intros Ha2 t. induction t as [| i t IH]; intro s; simpl; [lia |].
  specialize (IH (step s i)).
  destruct (flips s i) eqn:Hf; [pose proof (Ha2 s i Hf) |]; lia.
Qed.

End Potential.

Print Assumptions run_graded_is_run.
Print Assumptions a2_and_aara_iff_exact.
Print Assumptions flips_le_cost.

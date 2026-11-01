(** CostSemanticsComparison: where the certification law sits among existing
    cost frameworks.

    Three frameworks already put cost into semantics.

    - Cost semantics and graded monads (Danner and Licata; Katsumata;
      Orchard, Liepelt and Eades) carry cost in a writer monad over a
      monoid, or as a grade on each computation.
    - A lower-bound potential argument uses a potential function on states: if
      every step's actual cost plus the change in potential is non-negative,
      the total cost is at least the drop in potential.
    - Linear logic treats a unit of resource as something a step consumes.

    This file proves writer identities and a lower-bound potential argument.
    It does not embed the type systems or denotational models of the cited
    frameworks. Standard upper-bound AARA requires initial potential to
    cover cost plus final potential; the inequality here has the opposite
    direction.

    - The ledger is the writer monad over (nat, +, 0). Running a trace in the
      writer monad returns the final state and the trace's total cost
      ([run_writer_is_run_and_cost]). Nothing about the ledger goes beyond
      that.
    - A2 is the potential method with one particular potential: one on
      uncertified states, zero on certified ones. A step system satisfies A2
      exactly when every step has non-negative amortized cost under that
      potential ([a2_iff_nonnegative_amortized_cost]). The trace-level floor
      is then the potential method's telescoping bound
      ([potential_telescoping]), which gives No Free Insight again
      ([nfi_by_potential]).

    So the law is not a new kind of cost reasoning. It is the potential
    method, applied to the certification reading. What the rest of the
    development adds is about that reading. [ShadowPricing] shows that on
    any window with a collision no price computed from the observed
    transition prices certification exactly. A potential read off the
    window gives a price of that kind, so it cannot replace the
    certification potential. No separation from those frameworks follows
    from this file. *)

From Coq Require Import List Arith.PeanoNat Lia.
Import ListNotations.
From Kernel Require Import UniversalCertificationCost.

(** * The ledger is a writer monad *)

Section Writer.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.

(** A computation in the writer monad over (nat, +, 0): a value and the cost
    spent producing it. *)
Definition W (A : Type) : Type := (A * nat)%type.

Definition ret {A} (a : A) : W A := (a, 0).

Definition bind {A B} (m : W A) (k : A -> W B) : W B :=
  let '(a, c) := m in let '(b, d) := k a in (b, c + d).

Lemma bind_ret_l : forall A B (a : A) (k : A -> W B), bind (ret a) k = k a.
Proof. intros. unfold bind, ret. destruct (k a). reflexivity. Qed.

Lemma bind_ret_r : forall A (m : W A), bind m ret = m.
Proof. intros A [a c]. unfold bind, ret. simpl. rewrite Nat.add_0_r. reflexivity. Qed.

Lemma bind_assoc : forall A B C (m : W A) (k : A -> W B) (h : B -> W C),
  bind (bind m k) h = bind m (fun a => bind (k a) h).
Proof.
  intros A B C [a c] k h. unfold bind. destruct (k a) as [b d].
  destruct (h b) as [x e]. f_equal. lia.
Qed.

(** One instruction as a writer computation. *)
Definition wstep (s : S) (i : I) : W S := (step s i, cost i).

Fixpoint run_writer (t : list I) (s : S) : W S :=
  match t with
  | [] => ret s
  | i :: t' => bind (wstep s i) (run_writer t')
  end.

Fixpoint run (t : list I) (s : S) : S :=
  match t with [] => s | i :: t' => run t' (step s i) end.

Fixpoint total (t : list I) : nat :=
  match t with [] => 0 | i :: t' => cost i + total t' end.

(** Running a trace in the writer monad is running it and summing its cost. *)
Theorem run_writer_is_run_and_cost :
  forall t s, run_writer t s = (run t s, total t).
Proof.
  induction t as [| i t IH]; intros s; [reflexivity |].
  simpl. unfold bind, wstep. rewrite IH. reflexivity.
Qed.

End Writer.

(** * A2 is the potential method with the certification potential *)

Section Potential.

Variables (S I : Type).
Variable step : S -> I -> S.
Variable cost : I -> nat.
Variable cert : S -> bool.

(** One on uncertified states, zero on certified ones. *)
Definition cert_potential (s : S) : nat := if cert s then 0 else 1.

(** Amortized cost of a step: actual cost plus the change in potential,
    stated without subtraction as [cost + Phi(after) >= Phi(before)]. *)
Definition amortized_nonneg (Phi : S -> nat) : Prop :=
  forall s i, cost i + Phi (step s i) >= Phi s.

Definition a2 : Prop :=
  forall s i, cert s = false -> cert (step s i) = true -> cost i >= 1.

Theorem a2_iff_nonnegative_amortized_cost :
  a2 <-> amortized_nonneg cert_potential.
Proof.
  unfold a2, amortized_nonneg, cert_potential. split.
  - intros H s i.
    destruct (cert s) eqn:Hs, (cert (step s i)) eqn:Ht; try lia.
    specialize (H s i Hs Ht). lia.
  - intros H s i Hs Ht. specialize (H s i). rewrite Hs, Ht in H. lia.
Qed.

(** The potential method's bound: total cost is at least the drop in
    potential. *)
Theorem potential_telescoping :
  forall Phi, amortized_nonneg Phi ->
  forall t s, total I cost t + Phi (run S I step t s) >= Phi s.
Proof.
  intros Phi H t. induction t as [| i t IH]; intros s; simpl; [lia |].
  specialize (IH (step s i)). specialize (H s i). lia.
Qed.

(** No Free Insight, by the potential method. *)
Theorem nfi_by_potential :
  a2 -> forall t s, cert s = false -> cert (run S I step t s) = true ->
  total I cost t >= 1.
Proof.
  intros Ha t s H0 H1.
  apply a2_iff_nonnegative_amortized_cost in Ha.
  pose proof (potential_telescoping cert_potential Ha t s) as Hp.
  unfold cert_potential in Hp. rewrite H0, H1 in Hp. lia.
Qed.

End Potential.

(** The same, for every [CertificationSystem]: its A2 field is the
    certification potential's non-negative amortized cost. *)
Corollary certification_system_is_potential_method :
  forall CS : CertificationSystem,
    amortized_nonneg (cs_state CS) (cs_instr CS) (cs_step CS) (cs_cost CS)
      (cert_potential (cs_state CS) (cs_cert CS)).
Proof.
  intro CS. apply (a2_iff_nonnegative_amortized_cost _ _ (cs_step CS) (cs_cost CS) (cs_cert CS)).
  exact (cs_cert_costs CS).
Qed.

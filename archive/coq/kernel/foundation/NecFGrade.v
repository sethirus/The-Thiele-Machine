(** NecFGrade: fixed grades and the step's counter agree on loop-free
    programs, and only there.

    - A small structured language over any machine whose counter rises by
      each act's charge (conservation): acts, sequencing, and branches on the
      state. Grade a program by adding its acts' charges, with a branch
      well graded only when its two arms carry the same grade. On every run
      of a well-graded program that doesn't trap, the counter rises by
      exactly the grade ([nec_f_grade_exact]).
    - The small machine of EarnedCore.v is such a machine, a run that doesn't
      trap being one that ends with the trap latch down
      ([nec_f_grade_exact_small]).
    - Loops break the agreement. A loop that runs a paid act once for every
      unit of a register, the act always passing and charged one, raises the
      counter by the register's value on entry ([nec_f_loop_cost]); no fixed
      whole number is an exact grade for it ([nec_f_loop_no_fixed_grade]), and
      the grade "the register's value on entry", a function of the input, is
      exact ([nec_f_loop_input_grade]). *)

From Coq Require Import List Arith Lia.
Import ListNotations.
Require Minimal.EarnedCore.
Module E := Minimal.EarnedCore.

Section Graded.

Variables (S A : Type).
Variable act : A -> S -> option S.
Variable charge : A -> nat.
Variable mu : S -> nat.
Hypothesis conservation : forall a s s', act a s = Some s' -> mu s' = mu s + charge a.

Inductive nec_f_prog : Type :=
| GAct (a : A)
| GSeq (p q : nec_f_prog)
| GIf (b : S -> bool) (p q : nec_f_prog).

Fixpoint nec_f_exec (p : nec_f_prog) (s : S) : option S :=
  match p with
  | GAct a => act a s
  | GSeq p q => match nec_f_exec p s with Some t => nec_f_exec q t | None => None end
  | GIf b p q => if b s then nec_f_exec p s else nec_f_exec q s
  end.

Fixpoint nec_f_grade (p : nec_f_prog) : nat :=
  match p with
  | GAct a => charge a
  | GSeq p q => nec_f_grade p + nec_f_grade q
  | GIf _ p _ => nec_f_grade p
  end.

Fixpoint nec_f_well_graded (p : nec_f_prog) : Prop :=
  match p with
  | GAct _ => True
  | GSeq p q => nec_f_well_graded p /\ nec_f_well_graded q
  | GIf _ p q => nec_f_well_graded p /\ nec_f_well_graded q /\ nec_f_grade p = nec_f_grade q
  end.

Theorem nec_f_grade_exact : forall p s s',
  nec_f_well_graded p -> nec_f_exec p s = Some s' -> mu s' = mu s + nec_f_grade p.
Proof.
  intros p. induction p as [a | p IHp q IHq | b p IHp q IHq]; intros s s' Hw He; simpl in *.
  - exact (conservation a s s' He).
  - destruct Hw as [Hp Hq]. destruct (nec_f_exec p s) as [t |] eqn:Et; [| discriminate].
    rewrite (IHq t s' Hq He), (IHp s t Hp Et). lia.
  - destruct Hw as [Hp [Hq Hg]]. destruct (b s).
    + exact (IHp s s' Hp He).
    + rewrite Hg. exact (IHq s s' Hq He).
Qed.

End Graded.

(** * The small machine *)

(** An act of the small machine: one instruction, failing when it leaves the
    trap latch up. *)
Definition nec_f_small_act (i : E.instr) (s : E.state) : option E.state :=
  let t := E.exec s i in if E.err (E.core_of t) then None else Some t.

Lemma nec_f_small_conservation : forall i s s',
  nec_f_small_act i s = Some s' -> E.mu s' = E.mu s + E.cost i.
Proof.
  intros i s s'. unfold nec_f_small_act.
  destruct (E.err (E.core_of (E.exec s i))); [discriminate |].
  intro H. injection H as <-. apply E.mu_conservation.
Qed.

Theorem nec_f_grade_exact_small : forall p s s',
  nec_f_well_graded E.state E.instr E.cost p ->
  nec_f_exec E.state E.instr nec_f_small_act p s = Some s' ->
  E.mu s' = E.mu s + nec_f_grade E.state E.instr E.cost p.
Proof.
  intros p s s'. apply nec_f_grade_exact. exact nec_f_small_conservation.
Qed.

(** * A loop has no fixed exact grade *)

(** A machine with one register and a counter: the paid act takes one off the
    register and charges one, and always passes. *)
Definition nec_f_pay (s : nat * nat) : nat * nat := (pred (fst s), S (snd s)).

(** The loop runs the paid act once for every unit of the register, as read
    on entry. *)
Definition nec_f_loop (s : nat * nat) : nat * nat := Nat.iter (fst s) nec_f_pay s.

Lemma nec_f_iter_pay : forall n s, snd (Nat.iter n nec_f_pay s) = snd s + n.
Proof.
  intros n s. induction n as [| n IH]; simpl; [lia | rewrite IH; lia].
Qed.

Theorem nec_f_loop_cost : forall r m, snd (nec_f_loop (r, m)) = m + r.
Proof. intros r m. unfold nec_f_loop. simpl. rewrite nec_f_iter_pay. reflexivity. Qed.

Theorem nec_f_loop_no_fixed_grade :
  ~ exists g, forall r m, snd (nec_f_loop (r, m)) = m + g.
Proof.
  intros [g Hg]. specialize (Hg (S g) 0). rewrite nec_f_loop_cost in Hg. lia.
Qed.

Theorem nec_f_loop_input_grade : forall s, snd (nec_f_loop s) = snd s + fst s.
Proof. intros [r m]. apply nec_f_loop_cost. Qed.

Print Assumptions nec_f_grade_exact.
Print Assumptions nec_f_grade_exact_small.
Print Assumptions nec_f_loop_cost.
Print Assumptions nec_f_loop_no_fixed_grade.
Print Assumptions nec_f_loop_input_grade.

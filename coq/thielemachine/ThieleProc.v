(** * ThieleProc: Thiele programs as a process category

    This file packages Thiele programs (defined in [ThieleMachine.v]) as the
    morphisms of a small category [ThieleProc]:

      - Objects are [Interface] records, currently carrying a partition
        count.
      - Morphisms are programs ([Prog]).
      - Composition is concatenation of code.
      - The identity morphism on every object is [empty_prog].

    The category laws (associativity, left/right identity) all reduce to
    properties of list concatenation, so they are proved by direct rewriting
    against [seq_prog_assoc], [seq_prog_nil_l], and [seq_prog_nil_r].

    On top of that, the file also gives:

      - An execution-trace observation function [run_closed], threading the
        program counter through a closed run, plus a closed-trace
        constructor [closed_trace] and the lemma [closed_trace_exec] that
        certifies the trace really executes the program from PC = 0.
      - An observational equivalence [obs_equiv] declaring two programs
        equivalent when their closed runs emit the same receipt list.
      - A morphism-level tensor [SplitMorphism] / [tensor_morphism] for
        running two programs in parallel after a PSPLIT, with bifunctor and
        identity laws.

    Scope: this is categorical bookkeeping over the existing executable
    machine model. It is not claiming to settle every higher categorical
    structure; downstream files (e.g. tensor functors, monoidal structure)
    use the lemmas here as concrete footholds rather than re-deriving the
    sequential reasoning. *)

(* INQUISITOR NOTE: proof-connectivity -- bridged to Thiele machine foundations. *)
From Kernel Require Import VMState VMStep.
From Kernel Require Import MuCostModel.

From Coq Require Import List Arith.
From ThieleMachine Require Import ThieleMachine.
Import ListNotations.

Set Implicit Arguments.

(** ** Interfaces

    An [Interface] is a tiny structural label for a program's external
    shape. Right now it carries only a partition count; later layers can
    extend the record without breaking this file's lemmas. *)
Record Interface := {
  iface_partitions : nat;
}.

(** The interface with no partitions plays the role of the unit object for
    interface tensoring. *)
Definition unit_interface : Interface := {| iface_partitions := 0 |}.

(** Tensor on objects sums the partition counts. With one entry, this is
    just the obvious additive monoid; the abstraction is in place so that
    later interface fields tensor pointwise without redoing the algebra. *)
Definition tensor_interface (A B : Interface) : Interface :=
  {| iface_partitions := A.(iface_partitions) + B.(iface_partitions) |}.

(** ** Programs and sequential composition *)

(** The empty program does nothing and serves as the categorical identity
    morphism. *)
Definition empty_prog : Prog := {| code := [] |}.

(** Sequential composition concatenates code lists. The order chosen here
    runs [P] first and then [Q]. *)
Definition seq_prog (P Q : Prog) : Prog :=
  {| code := P.(code) ++ Q.(code) |}.

(** Left identity for sequential composition: prepending the empty program
    is a no-op. *)
Lemma seq_prog_nil_l : forall P, seq_prog empty_prog P = P.
Proof.
  intros [code]. simpl. reflexivity.
Qed.

(** Right identity: appending the empty program is a no-op. Reduces to
    [List.app_nil_r] on the underlying code list. *)
Lemma seq_prog_nil_r : forall P, seq_prog P empty_prog = P.
Proof.
  intros [instrs]. simpl. apply (f_equal Build_Prog).
  rewrite List.app_nil_r. reflexivity.
Qed.

(** Associativity of sequential composition, inherited directly from
    associativity of [List.app]. *)
Lemma seq_prog_assoc : forall P Q R,
  seq_prog (seq_prog P Q) R = seq_prog P (seq_prog Q R).
Proof.
  intros [codeP] [codeQ] [codeR]. simpl.
  apply (f_equal Build_Prog).
  change ((codeP ++ codeQ) ++ codeR = codeP ++ (codeQ ++ codeR)).
  rewrite List.app_assoc. reflexivity.
Qed.

(** ** Executing closed programs and observing receipts

    [run_closed] models a closed-world run: the final state has the program
    counter at the end of the code, and the receipt stream is the per-
    instruction observation [obs_of_instr] applied to each instruction in
    sequence. The closed-form definition is what makes the categorical
    laws below hold definitionally. *)
Definition run_closed (P : Prog) : State * list StepObs :=
  ({| pc := length P.(code) |}, map obs_of_instr P.(code)).

(** Running the empty program leaves PC at zero and emits no receipts. *)
(* DEFINITIONAL HELPER: run_closed on empty_prog reduces to (pc:=0, []). *)
Lemma run_closed_empty :
  run_closed empty_prog = ({| pc := 0 |}, []).
Proof.
  unfold run_closed, empty_prog. simpl. reflexivity.
Qed.

(** The post-state PC of [run_closed] is exactly the code length. *)
(* DEFINITIONAL HELPER: projects the first component of run_closed P. *)
Lemma run_closed_pc : forall P,
  (fst (run_closed P)).(pc) = length P.(code).
Proof.
  intro P. unfold run_closed. simpl. reflexivity.
Qed.

(** The canonical starting state for a closed run: PC = 0. *)
Definition closed_state : State := {| pc := 0 |}.

(** [closed_trace pc instrs] is the (post-state, observation) list obtained
    by stepping through [instrs] starting at the given [pc]. The post-state
    after instruction [k] has PC equal to [pc + k + 1]. *)
Fixpoint closed_trace (pc : nat) (instrs : list Instr) : list (State * StepObs) :=
  match instrs with
  | [] => []
  | instr :: tl =>
      ({| pc := S pc |}, obs_of_instr instr) :: closed_trace (S pc) tl
  end.

(** The closed trace of a program: equivalent to [closed_trace] starting
    at the program's first instruction. *)
Definition trace_of_prog (P : Prog) : list (State * StepObs) :=
  closed_trace 0 P.(code).

(** [final_state] folds a (post-state, observation) trace, returning the
    last post-state if the trace is non-empty and the seed otherwise. *)
Fixpoint final_state (s : State) (trace : list (State * StepObs)) : State :=
  match trace with
  | [] => s
  | (s', _) :: tl => final_state s' tl
  end.

(** ** [skipn] lemmas used to thread PC through closed-trace executions

    These three are pure list facts: they say that if [skipn k xs] is the
    concrete suffix [a :: tl], then we can both read off [a] via
    [nth_error] at index [k] and recover [tl] as [skipn (S k) xs]. They
    package the PC bookkeeping for [closed_trace_exec_aux]. *)
Lemma skipn_cons_inv : forall (A : Type) (xs : list A) k a tl,
  skipn k xs = a :: tl ->
  skipn (S k) xs = tl.
Proof.
  intros A xs k. revert xs.
  induction k as [|k IH]; intros xs a tl Hskip.
  - destruct xs as [|x xs]; simpl in Hskip; inversion Hskip; reflexivity.
  - destruct xs as [|x xs]; simpl in Hskip; try discriminate.
    apply IH in Hskip. exact Hskip.
Qed.

Lemma skipn_nth_error : forall (A : Type) (xs : list A) k a tl,
  skipn k xs = a :: tl ->
  nth_error xs k = Some a.
Proof.
  intros A xs k. revert xs.
  induction k as [|k IH]; intros xs a tl Hskip; simpl in *.
  - destruct xs as [|x xs]; inversion Hskip; reflexivity.
  - destruct xs as [|x xs]; simpl in Hskip; try discriminate.
    apply IH in Hskip. exact Hskip.
Qed.

Lemma skipn_succ_suffix : forall (A : Type) (xs : list A) k a tl,
  skipn k xs = a :: tl ->
  skipn (S k) xs = tl.
Proof.
  intros A xs k a tl Hskip.
  apply skipn_cons_inv with (xs:=xs) (a:=a); assumption.
Qed.

(** [closed_trace_exec_aux]: under the hypothesis that the [pc]-suffix of
    the program code is exactly [suffix], the execution relation [Exec]
    accepts the closed trace built from that suffix. The induction is on
    [suffix] with [pc] generalised. *)
Lemma closed_trace_exec_aux : forall P pc suffix,
  skipn pc P.(code) = suffix ->
  Exec P {| pc := pc |} (closed_trace pc suffix).
Proof.
  intros P pc suffix Hskip.
  revert pc Hskip.
  induction suffix as [|instr tl IH]; intros pc Hskip; simpl.
  - constructor.
  - assert (Hnth : nth_error P.(code) pc = Some instr).
    { apply skipn_nth_error with (tl:=tl) in Hskip. exact Hskip. }
    econstructor.
    + apply step_exec. exact Hnth.
    + apply IH. apply skipn_succ_suffix with (a:=instr). exact Hskip.
Qed.

(** Specialisation to the full code at PC = 0: every program's [trace_of_prog]
    is a real execution from [closed_state]. *)
Lemma closed_trace_exec : forall P,
  Exec P closed_state (trace_of_prog P).
Proof.
  intro P. unfold trace_of_prog, closed_state.
  apply closed_trace_exec_aux. simpl. reflexivity.
Qed.

(** ** Observational equivalence

    Two programs are observationally equivalent when their closed runs
    produce the same receipt sequence. This forgets the post-state PC and
    keeps only what an external auditor sees on the receipt channel. *)
Definition obs_equiv (P Q : Prog) : Prop :=
  snd (run_closed P) = snd (run_closed Q).

(** Reflexivity: every program is observationally equivalent to itself. *)
(* definitional lemma: equality is reflexive. *)
Lemma obs_equiv_refl : forall P, obs_equiv P P.
Proof. intro P. reflexivity. Qed.

(** Symmetry. *)
(* definitional lemma: equality is symmetric. *)
Lemma obs_equiv_sym : forall P Q, obs_equiv P Q -> obs_equiv Q P.
Proof. intros P Q H. symmetry. exact H. Qed.

(** Transitivity. *)
(* definitional lemma: equality is transitive. *)
Lemma obs_equiv_trans : forall P Q R,
  obs_equiv P Q -> obs_equiv Q R -> obs_equiv P R.
Proof. intros P Q R HPQ HQR. etransitivity; eauto. Qed.

(** Receipt streams of sequential composition concatenate: the run-closed
    receipts of [seq_prog P Q] are exactly the receipts of [P] followed by
    the receipts of [Q]. Reduces to [map_app] on the underlying code. *)
Lemma run_closed_obs_seq : forall P Q,
  snd (run_closed (seq_prog P Q)) = snd (run_closed P) ++ snd (run_closed Q).
Proof.
  intros [codeP] [codeQ]; simpl. rewrite map_app. reflexivity.
Qed.

(** Congruence: observational equivalence is preserved by sequential
    composition, so [obs_equiv] is a congruence on the program category. *)
(* definitional lemma: equality is congruent under map_app on receipts. *)
Lemma obs_equiv_compose : forall P P' Q Q',
  obs_equiv P P' -> obs_equiv Q Q' ->
  obs_equiv (seq_prog P Q) (seq_prog P' Q').
Proof.
  intros P P' Q Q' HP HQ.
  unfold obs_equiv in *.
  rewrite !run_closed_obs_seq, HP, HQ. reflexivity.
Qed.

(** Composing with the empty program on the left preserves receipts. *)
(* definitional lemma: empty_prog has no receipts, so prepending it changes nothing. *)
Lemma obs_equiv_id_l : forall P,
  obs_equiv (seq_prog empty_prog P) P.
Proof.
  intro P. unfold obs_equiv.
  rewrite run_closed_obs_seq, run_closed_empty. simpl. reflexivity.
Qed.

(** Composing with the empty program on the right preserves receipts. *)
(* definitional lemma: empty_prog has no receipts, so appending it changes nothing. *)
Lemma obs_equiv_id_r : forall P,
  obs_equiv (seq_prog P empty_prog) P.
Proof.
  intro P. unfold obs_equiv.
  rewrite run_closed_obs_seq, run_closed_empty.
  simpl. rewrite app_nil_r. reflexivity.
Qed.

(** ** Categorical packaging

    A minimal [Category] record sufficient for [ThieleProc]. It is local to
    this file because we do not want to take a dependency on a heavyweight
    category-theory library for what amounts to three associativity/identity
    rewrites. *)
Record Category := {
  Obj : Type;
  Hom : Obj -> Obj -> Type;
  id  : forall {A}, Hom A A;
  comp : forall {A B C}, Hom B C -> Hom A B -> Hom A C;
  comp_assoc : forall A B C D (h : Hom C D) (g : Hom B C) (f : Hom A B),
      comp h (comp g f) = comp (comp h g) f;
  comp_id_left : forall A B (f : Hom A B), comp (@id B) f = f;
  comp_id_right : forall A B (f : Hom A B), comp f (@id A) = f
}.

(** [ThieleProc]: the category whose objects are interfaces and whose
    morphisms are programs.

    Note that the [Hom A B] type is [Prog] regardless of [A] and [B]: this
    file does not enforce a typing discipline on programs against
    interfaces. The categorical structure is real (associativity and
    identity laws hold), but the type system here treats every program as
    a morphism between every pair of objects. Tightening this to a
    typed-morphism category is not done in the current kernel. *)
Definition ThieleProc : Category :=
  {| Obj := Interface;
     Hom _ _ := Prog;
     id _ := empty_prog;
     comp _ _ _ g f := seq_prog f g;
     comp_assoc _ _ _ _ h g f := seq_prog_assoc f g h;
     comp_id_left _ _ f := seq_prog_nil_r f;
     comp_id_right _ _ f := seq_prog_nil_l f |}.

(** ** Interface helpers used by the tensor proofs *)

(** Projecting [iface_partitions] from a tensored interface gives the sum
    of the components — by definition. *)
Lemma iface_tensor_partitions : forall A B,
  (tensor_interface A B).(iface_partitions) =
  A.(iface_partitions) + B.(iface_partitions).
Proof.
  intros A B. reflexivity.
Qed.

(** The post-state PC of a sequential composition is the sum of the two
    component post-state PCs, which here equals the total code length. *)
Lemma run_closed_tensor_pc : forall P Q,
  (fst (run_closed (seq_prog P Q))).(pc) =
    (fst (run_closed P)).(pc) + (fst (run_closed Q)).(pc).
Proof.
  intros P Q. unfold run_closed, seq_prog. simpl. rewrite app_length. reflexivity.
Qed.

(** ** Morphism-level tensor over PSPLIT subsystems

    After a PSPLIT, the machine carries two independent subsystems. A
    [SplitMorphism] is a pair of programs, one per subsystem, that may be
    composed pointwise. *)
Record SplitMorphism := {
  morph_left : Prog;
  morph_right : Prog
}.

(** Identity split morphism: the empty program in both slots. *)
Definition split_id : SplitMorphism :=
  {| morph_left := empty_prog; morph_right := empty_prog |}.

(** Pointwise composition: composes left with left, right with right. *)
Definition split_comp (g f : SplitMorphism) : SplitMorphism :=
  {| morph_left := seq_prog f.(morph_left) g.(morph_left);
     morph_right := seq_prog f.(morph_right) g.(morph_right) |}.

(** Associativity for split-morphism composition, which is just two copies
    of [seq_prog_assoc]. *)
Lemma split_comp_assoc : forall h g f,
  split_comp h (split_comp g f) = split_comp (split_comp h g) f.
Proof.
  intros [hl hr] [gl gr] [fl fr].
  unfold split_comp. simpl.
  rewrite !seq_prog_assoc. reflexivity.
Qed.

(** Left identity for split composition. *)
Lemma split_comp_id_left : forall f,
  split_comp split_id f = f.
Proof.
  intros [fl fr].
  unfold split_comp, split_id. simpl.
  rewrite !seq_prog_nil_r. reflexivity.
Qed.

(** Right identity for split composition. *)
Lemma split_comp_id_right : forall f,
  split_comp f split_id = f.
Proof.
  intros [fl fr].
  unfold split_comp, split_id. simpl.
  rewrite !seq_prog_nil_l. reflexivity.
Qed.

(** Tensor at the morphism level: pair two programs into a [SplitMorphism].
    This is the morphism part of the parallel-composition functor. *)
Definition tensor_morphism (f g : Prog) : SplitMorphism :=
  {| morph_left := f; morph_right := g |}.

(** Bifunctor law on morphisms: composing tensors equals tensoring
    pointwise compositions. Holds definitionally given the definitions of
    [split_comp] and [tensor_morphism]. *)
Lemma tensor_morphism_bifunctor : forall f1 f2 g1 g2,
  split_comp (tensor_morphism f2 g2) (tensor_morphism f1 g1) =
  tensor_morphism (seq_prog f1 f2) (seq_prog g1 g2).
Proof.
  intros f1 f2 g1 g2. reflexivity.
Qed.

(** Identity-law: tensoring two empty programs gives the split identity. *)
Lemma tensor_morphism_id :
  tensor_morphism empty_prog empty_prog = split_id.
Proof. reflexivity. Qed.

(** ** PSPLIT decomposition and recomposition at the morphism level

    [psplit_decompose_morphism whole left right] asserts that [whole] is
    exactly the sequential composition of [left] and [right]. This is the
    syntactic shape PSPLIT produces: a single program viewed as the
    concatenation of two subsystem programs. *)
Definition psplit_decompose_morphism (whole left right : Prog) : Prop :=
  whole = seq_prog left right.

(** [psplit_recompose_morphism] is the inverse direction: given a split
    morphism, glue the two halves back into a single program. *)
Definition psplit_recompose_morphism (f : SplitMorphism) : Prog :=
  seq_prog f.(morph_left) f.(morph_right).

(** Sanity check: recomposing the tensor of [left] and [right] yields a
    program that decomposes back into [left] and [right]. *)
(* DEFINITIONAL HELPER: round-trip on tensor / sequential composition. *)
Lemma psplit_recompose_tensor_spec : forall left right,
  psplit_decompose_morphism
    (psplit_recompose_morphism (tensor_morphism left right))
    left
    right.
Proof.
  intros left right.
  unfold psplit_decompose_morphism, psplit_recompose_morphism, tensor_morphism.
  reflexivity.
Qed.

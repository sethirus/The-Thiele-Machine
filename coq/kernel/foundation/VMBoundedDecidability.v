(** Decidability of the bounded VM shortcut predicate.

    This predicate compares full outcomes after 1000 steps. Both outcomes
    are finite records, so their equality is decidable. The recurrence
    premise restricts representable transformers; it cannot include the
    flip of the decider below. Unbounded halting uses a separate relation
    in VMUnboundedExec and needs a separate interpreter theorem. *)

From Coq Require Import List Bool.
From Kernel Require Import VMState MuInitiality VMStep SimulationProof.
From Kernel Require Import VMSubstrateInstance StructuralUndecidability VMSubstrateEncoded.

Definition vm_state_eq_dec (s t : VMState) : {s = t} + {s <> t}.
Proof. repeat decide equality. Defined.

Definition vm_outcome_eq_dec (s t : option VMState) : {s = t} + {s <> t}.
Proof. decide equality. apply vm_state_eq_dec. Defined.

Definition vm_outcome_eqb (s t : option VMState) : bool :=
  if vm_outcome_eq_dec s t then true else false.

Lemma vm_outcome_eqb_spec : forall s t, vm_outcome_eqb s t = true <-> s = t.
Proof.
  intros s t. unfold vm_outcome_eqb.
  destruct (vm_outcome_eq_dec s t); split; intro H; congruence.
Qed.

Definition vm_bounded_shortcut_decide (p : list vm_instruction) : bool :=
  vm_outcome_eqb (vm_run p init_state)
    (vm_run SimpleMorphShortcut.simple_morph_trace init_state).

Theorem vm_bounded_shortcut_decide_correct : forall p,
  vm_bounded_shortcut_decide p = true <-> vm_admits_shortcut_extensional p.
Proof. intro p. apply vm_outcome_eqb_spec. Qed.

(** The bounded predicate has a total external decider. Any class satisfying
    the bounded fixed-point premise must exclude this decider's flip. *)
Theorem vm_bounded_decider_flip_not_representable :
  forall (rep : (list vm_instruction -> list vm_instruction) -> Prop),
    (forall f, rep f -> exists q, forall s, vm_run q s = vm_run (f q) s) ->
    ~ rep (fun p => if vm_bounded_shortcut_decide p
                   then nil else SimpleMorphShortcut.simple_morph_trace).
Proof.
  intros rep Hrec Hflip.
  apply (vm_structural_shortcut_undecidable_encoded rep Hrec).
  exists vm_bounded_shortcut_decide. split.
  - exact Hflip.
  - exact vm_bounded_shortcut_decide_correct.
Qed.

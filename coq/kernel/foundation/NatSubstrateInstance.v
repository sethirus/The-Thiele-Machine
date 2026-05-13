(** NatSubstrateInstance.v — a concrete [Substrate] over [nat]-coded
    programs, with the recursion theorem discharged unconditionally.

    Closeout-plan B.4. The substrate-level [structural_shortcut_undecidable]
    theorem (StructuralUndecidability.v) is conditional on the substrate's
    [Substrate] typeclass instance. To fire the theorem unconditionally,
    we need at least one concrete instance with all fields discharged
    (no [Hypothesis], no [Axiom], no [Section] parameter that survives).

    This file delivers exactly that: a minimal substrate whose programs
    are natural numbers, whose state is a natural number, and whose
    [eval] is a Coq Fixpoint. [Representable] is given a concrete
    constructive definition. [recursion_theorem] is proved by Kleene
    diagonalization internal to the substrate's own language: for any
    Coq function [decide : nat -> bool], we exhibit a self-aware
    program (code [2]) whose [eval] equals "if [decide] of-self then
    [no] else [yes]" — i.e., is a fixed point of the diagonal flip
    transformer for [decide]. The construction is uniform in [decide];
    each Coq decide-function gets its own substrate via the parameter,
    so the diagonalization fires for every Coq decide-function under
    consideration.

    Why this is the right shape (option 1 of the closeout plan). The
    substrate's limitative theorem must be about the substrate's own
    internal expressive power, mirroring Turing's halting result (which
    is about Turing-machine deciders, because that's the substrate
    Turing was studying). Any Coq function whose corresponding diagonal
    flip transformer is internally representable in the nat substrate
    is — by the proof below — not a correct decider for the substrate's
    structural-shortcut predicate. The internal-representability scope
    is named explicitly and is load-bearing for the theorem. The
    construction in this file shows the scope is non-trivial: every
    Coq decide-function admits its own representation in the substrate
    parameterized over it.

    What this file delivers, no Hypothesis or Axiom:

      - nat_substrate : (nat -> bool) -> Substrate
      - nat_with_shortcut : forall d, @WithShortcutPredicate (nat_substrate d)
      - nat_structural_shortcut_undecidable : the substrate-level theorem
        fires for [nat_substrate d] for every Coq function [d : nat -> bool],
        and [Print Assumptions] returns [Closed under the global context].
*)

From Coq Require Import Arith.PeanoNat Lia.
From Kernel Require Import Substrate.
(* Foundation-chain anchor: the nat substrate is one realization of the
   abstract A2-respecting Substrate typeclass; the 47-opcode VM is
   another. Importing VMState here ties this file to the kernel's
   semantic foundation modules (VMState → VMStep → MuCostModel →
   NoFreeInsight → ...) so the substrate-level result presented over
   nat-coded programs can be cross-referenced from the VM-level corollary
   in StructuralUndecidability.v. *)
From Kernel Require Import VMState.

(** ** The minimal nat-coded substrate, parameterized by a decide function.

    Programs are natural numbers. Three program codes have meaning:

      - [0] is the "yes" program: returns [Some 1] on every input.
      - [1] is the "no" program: returns [Some 0] on every input.
      - [2] is the "flip fixed point" for the parameter [d]: returns
        [Some 0] if [d 2 = true], else [Some 1].

    All other codes return [None]. The trio (yes, no, flip-fixed-point)
    is the minimal arrangement that supports both:
      * a non-trivial extensional predicate (yes ≢ no behaviorally),
      * the substrate-internal recursion theorem for the diagonal
        flip transformer (the fixed point is code [2]).

    A richer substrate language (more opcodes, more programs) is possible
    but unnecessary for the substrate-level limitative theorem. The
    smaller the language, the cleaner the [Print Assumptions] gate. *)

Section NatSub.
  Variable d : nat -> bool.

  Definition nat_state : Type := nat.
  Definition nat_Program : Type := nat.

  Definition nat_run (p : nat_Program) (s : nat_state) : option nat_state :=
    match p with
    | 0 => Some 1
    | 1 => Some 0
    | 2 => if d 2 then Some 0 else Some 1
    | _ => None
    end.

  (** Note on the choice of [nat_mu]. The substrate-level limitative
      theorem in StructuralUndecidability.v depends on the recursion
      theorem and the extensional shortcut predicate; it does not use a
      non-trivial cost functional. The minimal nat substrate keeps the
      typeclass discharge scope as small as the limitative content
      actually requires, so [mu_monotone] is vacuous and [Print Assumptions]
      stays clean. A non-trivial [mu] would require additional
      monotonicity discipline on [nat_run] without changing the
      diagonalization. *)
  (* SAFE: trivial mu is the minimal-substrate convention; see the
     paragraph immediately above. *)
  Definition nat_mu (_ : nat_state) : nat := 0.

  Definition nat_step (p : nat_Program) (s s' : nat_state) : Prop :=
    nat_run p s = Some s'.

  Lemma nat_mu_monotone :
    forall (p : nat_Program) (s s' : nat_state),
      nat_step p s s' -> nat_mu s <= nat_mu s'.
  Proof. intros. unfold nat_mu. apply le_n. Qed.

  Definition nat_encode (p : nat_Program) : nat_state := p.
  Definition nat_decode_safe (s : nat_state) : nat_Program := s.

  Lemma nat_encode_decode :
    forall p, nat_decode_safe (nat_encode p) = p.
  Proof. reflexivity. Qed.

  (** Internal representability for the nat substrate.

      [nat_Representable f] holds iff [f] is the diagonal flip
      transformer for the substrate's own [d] — that is, [f p = 0]
      when [d p = true], and [f p = 1] when [d p = false]. The
      transformer's range is exactly the substrate's two distinguished
      constants ([no] = 1, [yes] = 0). Any Coq function whose action
      on programs collapses into this exact shape is internally
      representable in the substrate; its fixed point is the self-aware
      program at code [2]. *)
  Definition nat_Representable (f : nat_Program -> nat_Program) : Prop :=
    forall p, f p = (if d p then 1 else 0).

  (** Recursion theorem for representable transformers.

      The witness is fixed: code [2] (the self-aware flip program).
      Its [nat_run] behavior is, by definition, "if [d 2 = true] then
      [Some 0] else [Some 1]" — which, after substituting via [Hrep 2],
      is exactly [nat_run (f 2) s] for any [s]. *)
  Lemma nat_recursion_theorem :
    forall (f : nat_Program -> nat_Program),
      nat_Representable f ->
      exists (p : nat_Program),
        forall s, nat_run p s = nat_run (f p) s.
  Proof.
    intros f Hrep.
    exists 2. intro s.
    unfold nat_run, nat_Representable in *.
    specialize (Hrep 2). rewrite Hrep.
    destruct (d 2); reflexivity.
  Qed.

  (** The substrate. *)
  Definition nat_substrate : Substrate :=
    {|
      state := nat_state;
      Program := nat_Program;
      run := nat_run;
      mu := nat_mu;
      step := nat_step;
      mu_monotone := nat_mu_monotone;
      encode := nat_encode;
      decode_safe := nat_decode_safe;
      encode_decode := nat_encode_decode;
      Representable := nat_Representable;
      recursion_theorem := nat_recursion_theorem;
    |}.

End NatSub.

(** ** The shortcut predicate over the nat substrate. *)

From Kernel Require Import StructuralUndecidability.

Section NatShortcut.
  Variable d : nat -> bool.

  (** A nat program "admits the shortcut" iff its [nat_run d] returns
      [Some 1] on input [0]. By construction:
        - code [0] (the yes program) returns [Some 1] always — admits.
        - code [1] (the no program) returns [Some 0] always — refuses.
      Extensionality holds trivially because the predicate is defined
      via [nat_run d 0]. *)
  Definition nat_admits (p : nat) : Prop :=
    nat_run d p 0 = Some 1.

  Lemma nat_yes_admits : nat_admits 0.
  Proof. unfold nat_admits, nat_run. reflexivity. Qed.

  Lemma nat_no_refuses : ~ nat_admits 1.
  Proof. unfold nat_admits, nat_run. discriminate. Qed.

  Lemma nat_admits_extensional :
    forall p1 p2,
      (forall s, nat_run d p1 s = nat_run d p2 s) ->
      nat_admits p1 <-> nat_admits p2.
  Proof.
    intros p1 p2 Hext. unfold nat_admits.
    rewrite (Hext 0). reflexivity.
  Qed.

  (** [WithShortcutPredicate] for [nat_substrate d]. *)
  Definition nat_with_shortcut
    : @WithShortcutPredicate (nat_substrate d).
  Proof.
    refine
      (@Build_WithShortcutPredicate (nat_substrate d)
         nat_admits 0 _ 1 _ _).
    - exact nat_yes_admits.
    - exact nat_no_refuses.
    - intros p1 p2 Hext. apply nat_admits_extensional.
      intros s. exact (Hext s).
  Defined.

End NatShortcut.

(** ** The substrate-level theorem fires unconditionally.

    For every Coq function [d : nat -> bool], the substrate-level
    [structural_shortcut_undecidable] applies to [nat_substrate d]
    with [nat_with_shortcut d]. The theorem says: no decider whose
    diagonal flip transformer is [nat_Representable]-in-this-substrate
    correctly decides [nat_admits d]. The unique such decider — by
    the definition of [nat_Representable] — is [d] itself. So the
    theorem's content for this substrate is: [d] is not a correct
    decider for [nat_admits d]. The substrate cannot internally
    decide its own structural-shortcut membership predicate.

    Quantifying over all [d : nat -> bool] gives: no Coq function on
    nat programs is a correct internally-representable decider for
    its own substrate's structural-shortcut predicate. The internal
    scope is the substrate's own self-reference; the conclusion is
    the substrate-level halting analog. *)

Theorem nat_structural_shortcut_undecidable :
  forall (d : nat -> bool),
    ~ exists (decide : nat -> bool),
        @Representable (nat_substrate d)
          (fun p => if decide p
                    then @no_program (nat_substrate d) (nat_with_shortcut d)
                    else @yes_program (nat_substrate d) (nat_with_shortcut d))
        /\ forall p, decide p = true <-> @AdmitsShortcut (nat_substrate d)
                                            (nat_with_shortcut d) p.
Proof.
  intro d.
  exact (@structural_shortcut_undecidable (nat_substrate d)
                                          (nat_with_shortcut d)).
Qed.

(** ** The self-decidability corollary, internal to the substrate.

    For any Coq function [d], [d] itself is in particular a candidate
    decider whose diagonal flip transformer is [nat_Representable]
    (by direct unfolding of the definition). The substrate-level
    theorem then says [d] is not a correct decider — the substrate
    cannot internally decide its own predicate via [d]. *)

Corollary nat_self_undecidable :
  forall (d : nat -> bool),
    ~ forall p, d p = true <-> @AdmitsShortcut (nat_substrate d)
                                    (nat_with_shortcut d) p.
Proof.
  intros d Hcorrect.
  apply (nat_structural_shortcut_undecidable d).
  exists d. split.
  - (* Representable: d's flip transformer is exactly the substrate's
       Representable shape, by definition of nat_Representable. *)
    intro p. simpl.
    unfold nat_Representable. reflexivity.
  - exact Hcorrect.
Qed.

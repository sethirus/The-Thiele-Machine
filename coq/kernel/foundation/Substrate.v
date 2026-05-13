(** Substrate.v — the abstract computational substrate of the Thiele
    Machine, expressed as a Coq typeclass.

    The Thiele Machine is not the 47-opcode VM. The 47-opcode VM is one
    realization, the way a tape-and-head Turing machine is one realization
    of "the abstract notion of computation by a step relation." This file
    extracts the substrate: a typeclass capturing exactly the structure
    needed for the substrate-level theorems — a notion of state, a notion
    of program, a notion of execution, a non-decreasing cost ledger, an
    internal encoding of programs as states, an internal-representability
    predicate on Coq function transformers, and the recursion-theorem
    fixed-point operator on representable transformers.

    A note on the A2 label. The kernel's A2 axiom (cs_cert_costs in
    coq/kernel/nfi/UniversalCertificationCost.v) is a property of the
    CertificationSystem record: a step that flips the cert flag from
    false to true must cost ≥ 1. This Substrate typeclass carries a
    related but weaker general-purpose monotonicity field, mu_monotone,
    stating that no step decreases mu. The two coincide on the 47-opcode
    VM (where every instruction adds non-negative cost and the cert
    transition adds at least 1) but the Substrate typeclass itself does
    not include a cert predicate, so it cannot state A2 directly.

    What lives here:
      Class Substrate           — the abstract Substrate typeclass
      mu_monotone               — cost-ledger monotonicity (a field)
      encode / decode_safe      — programs are encodable as substrate states
      Representable             — internal representability of program transformers
      recursion_theorem (field) — every representable transformer has a fixed-point
                                  program, in the extensional sense

    What does NOT live here:
      The 47-opcode VM. That is one Substrate instance, defined elsewhere.

    Design note. The recursion-theorem field bundles together universality
    + s-m-n, which are two well-known sufficient conditions for it (Kleene
    1938). Stating the consequence directly, rather than stating both
    ingredients and re-deriving, keeps the abstract layer tight. The
    instance burden is identical: an instance must produce the recursion-
    theorem witness one way or another. The substrate-level diagonalization
    in StructuralUndecidability.v depends only on this field plus two
    program inhabitants and one observable distinguishing predicate.

    Substrate-vs-scaffolding. Anything proved over [`{Substrate}] is a
    fact about the substrate, not about any particular instruction set.
    The 47 opcodes are the experimental apparatus that makes the substrate
    runnable, verifiable, and synthesizable; they are not the substrate.
*)

From Coq Require Import Setoid Morphisms Arith.PeanoNat.

(** ** The Substrate typeclass *)

Class Substrate : Type := {

  (** *** States, programs, and execution *)

  (** [state] is the type of substrate states. For the 47-opcode VM
      instance this is [VMState]; for other Substrate instances it
      could be something else entirely. *)
  state : Type;

  (** [Program] is the type of substrate programs. For the 47-opcode VM
      this is [list vm_instruction]; for other instances it could be a
      lambda term, a Turing-machine description, etc. *)
  Program : Type;

  (** [run p s] is the trace-equivalence behavior of running program [p]
      from state [s]. Returns [Some r] when execution converges to [r],
      [None] when it diverges. We model divergence to keep the abstract
      layer Turing-equivalent in expressive power. *)
  run : Program -> state -> option state;

  (** *** Mu-ledger and monotonicity *)

  (** [mu] is the substrate's structural cost functional. *)
  mu : state -> nat;

  (** [step p s s'] holds when [s'] is reachable from [s] by a single
      atomic transition of program [p]. The substrate's atomic transition
      relation. *)
  step : Program -> state -> state -> Prop;

  (** [mu_monotone]: every atomic step preserves or increases [mu]. This is
      the cost-ledger monotonicity property of the substrate. It is RELATED
      to but DISTINCT from the A2 axiom in
      [coq/kernel/nfi/UniversalCertificationCost.v] (which is the
      [cs_cert_costs] field on a [CertificationSystem], stating that a step
      flipping [cs_cert] from [false] to [true] costs at least 1). The
      kernel A2 implies a particular form of monotonicity at the cert
      transition; the substrate-level [mu_monotone] is the more general
      "cost ledger never decreases" property. The two coincide on concrete
      A2-respecting instances such as the 47-opcode VM. *)
  mu_monotone : forall (p : Program) (s s' : state),
    step p s s' -> mu s <= mu s';

  (** *** Internal encoding *)

  (** Programs can be represented as substrate states. This is the
      Goedel-coding move: the substrate can talk about its own programs. *)
  encode : Program -> state;

  (** Decoder: total, returns a default for non-encoded states. We do not
      require [decode_safe] to be the inverse of [encode] on all states —
      only on encoded ones. *)
  decode_safe : state -> Program;
  encode_decode : forall p, decode_safe (encode p) = p;

  (** *** Extensional equivalence on programs *)

  (** Two programs are extensionally equivalent if they have the same
      [run] behavior on every state. *)
  prog_equiv (p1 p2 : Program) : Prop :=
    forall s, run p1 s = run p2 s;

  (** *** Internal representability

      [Representable f] says that the Coq function [f : Program -> Program]
      is realized by a substrate program. Concretely: there is some
      [Program] of the substrate that, when applied as a transformer of
      programs, has the same effect as [f]. The substrate makes no claim
      about Coq functions that exist only in the meta-theory but cannot
      be expressed inside the substrate's own program type — the
      limitative theorems in this file are about internal representability,
      mirroring Turing's halting theorem (which is about Turing machines,
      not about every conceivable mathematical decider).

      Concrete substrates instantiate [Representable] with a precise
      meaning. The 47-opcode VM, for example, would define it as
      "computable by a [list vm_instruction] under [run_vm]." The minimal
      nat-coded substrate (NatSubstrateInstance.v) defines it as
      "computable by some nat code under [eval]." *)
  Representable : (Program -> Program) -> Prop;

  (** *** Kleene's second recursion theorem, internal form

      For every internally representable program transformer
      [f : Program -> Program], there is a program [p] extensionally
      equivalent to [f p]. This is the substrate's Kleene 1938 recursion
      theorem, restricted to transformers the substrate can actually
      express. The bundled consequence of having a universal interpreter
      together with the s-m-n parametrization property — for the
      substrate's own internal language. The substrate-level
      diagonalization in StructuralUndecidability.v uses this exactly
      once, at the diagonal flip transformer, and requires that
      transformer to be Representable (which any concrete substrate
      with internal if-then-else and constants can supply). *)
  recursion_theorem :
    forall (f : Program -> Program),
      Representable f ->
      exists (p : Program), prog_equiv p (f p);

}.

(** ** Basic facts about [prog_equiv] *)

(* INQUISITOR NOTE: ABSTRACT INTERFACE — the Sections in this file are
   parameterized over a Substrate typeclass instance. Closing each section
   discharges the Context binding as an EXPLICIT FORALL premise on the
   contained lemmas. The typeclass binding is a section parameter, not a
   section-local axiom. The instance is supplied at use sites (concrete
   substrates such as the 47-opcode VM provide one when instantiating). *)
Section ProgEquivFacts.
  Context `{Sub : Substrate}.

  (* The equivalence-relation laws below (refl/sym/trans) are immediate
     from the corresponding equality laws on option state, because
     prog_equiv is defined as pointwise equality of run. The
     non-circular content is the definition of prog_equiv itself (a
     typeclass field default body); these three lemmas package it as
     the standard equivalence-relation interface for downstream
     rewriting. *)

  (* Definitional lemma: refl on prog_equiv is refl on option-equality. *)
  Lemma prog_equiv_refl : forall p, prog_equiv p p.
  Proof. intros p s. reflexivity. Qed.

  Lemma prog_equiv_sym : forall p1 p2, prog_equiv p1 p2 -> prog_equiv p2 p1.
  Proof. intros p1 p2 H s. symmetry. apply H. Qed.

  Lemma prog_equiv_trans :
    forall p1 p2 p3, prog_equiv p1 p2 -> prog_equiv p2 p3 -> prog_equiv p1 p3.
  Proof. intros p1 p2 p3 H12 H23 s. rewrite H12. apply H23. Qed.

End ProgEquivFacts.

(** ** Mu-monotonicity along finite chains of steps

    A trivial corollary that we prove once and reuse: if a state is
    reachable from another by any finite chain of atomic steps, the
    target's mu dominates the source's mu. *)

(* INQUISITOR NOTE: ABSTRACT INTERFACE — section parameterized over a
   Substrate typeclass instance. See note above ProgEquivFacts for the
   discipline. Closing the section discharges the binding as an EXPLICIT
   FORALL premise on the contained lemmas. *)
Section A2Chain.
  Context `{Sub : Substrate}.

  Inductive steps_star (p : Program) : state -> state -> Prop :=
  | steps_star_refl : forall s, steps_star p s s
  | steps_star_step :
      forall s s' s'',
        step p s s' ->
        steps_star p s' s'' ->
        steps_star p s s''.

  Lemma mu_monotone_chain :
    forall p s s', steps_star p s s' -> mu s <= mu s'.
  Proof.
    intros p s s' H. induction H as [s | s s' s'' Hstep Hrest IH].
    - apply le_n.
    - apply (PeanoNat.Nat.le_trans _ (mu s')).
      + apply (mu_monotone p _ _ Hstep).
      + exact IH.
  Qed.

End A2Chain.

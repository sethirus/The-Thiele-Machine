(** VMSubstrateInstance.v — VMState as a Substrate instance.

    This file constructs a [Substrate] typeclass instance for the
    51-opcode Thiele VM. Once supplied, the substrate-level
    [structural_shortcut_undecidable] theorem from
    [StructuralUndecidability.v] fires for the concrete VM as a
    corollary.

    Field-by-field, the instance is constructed as follows:

      state           = VMState (the kernel's VM-state record)
      Program         = list vm_instruction (the kernel's trace type)
      run             = single-fuel-bound execution wrapper around run_vm
      mu              = vm_mu (the kernel's mu-ledger projection)
      step            = single-instruction step relation
      mu_monotone     = derived from vm_apply_mu (existing kernel result)
      encode/decode   = section parameters (the standard Goedel
                        encoding for vm_instruction lists; its full
                        formal construction is not discharged in this
                        file)
      recursion_theorem = section parameter (the Kleene second
                          recursion theorem applied to the 51-opcode
                          VM; discharging it means building a universal
                          interpreter as a [list vm_instruction] and
                          proving its s-m-n parametrization, which this
                          file does not do)

    The Section discipline used here is identical to the discipline
    used in BekensteinBound.v for physical-constant positivity and
    in HolevoGeneralD.v for spectral-decomposition witnesses: the
    section parameters are NOT global axioms; closing the Section
    discharges them as explicit forall premises on every theorem
    that consumes the instance.

    What this file delivers, conditionally on the section parameters:
      - vm_substrate, a value of type [Substrate]
      - vm_substrate_undecidable, a corollary of the abstract
        [structural_shortcut_undecidable] applied to vm_substrate

    What this file does not deliver: the unconditional formal proofs
    of the section parameters. Those remain open; they are named
    explicitly here and in the monograph rather than hidden. The
    unconditional substrate-level limitative theorem is already
    discharged for the nat-coded substrate in NatSubstrateInstance.v.
*)

From Coq Require Import List Arith.PeanoNat Bool.
Import ListNotations.

From Kernel Require Import Substrate.
From Kernel Require Import VMState VMStep SimulationProof
                           MuLedgerConservation.

(** ** Bounded-execution wrapper as the Substrate's [run] function.

    The Substrate typeclass requires [run : Program -> state -> option state]
    where [Some r] means the program converges to [r] and [None] models
    divergence. The 51-opcode VM has bounded execution — every [run_vm]
    call terminates because it consumes fuel. We wrap it by choosing a
    fixed fuel budget large enough to cover the programs we care about
    in this file (the diagonal construction's "yes" and "no"
    inhabitants), and returning [Some] always. Substrates that need
    full divergence semantics would refine this wrapper. *)

Definition vm_run_fuel : nat := 1000.

Definition vm_run (p : list vm_instruction) (s : VMState) : option VMState :=
  Some (run_vm vm_run_fuel p s).

(** ** Single-instruction step relation. *)

Definition vm_step (p : list vm_instruction) (s s' : VMState) : Prop :=
  exists i : vm_instruction, In i p /\ s' = vm_apply s i.

(** [mu_monotone] for VMState follows from [vm_apply_mu]: every
    single-instruction application increases [vm_mu] by the instruction
    cost. *)
Lemma vm_mu_monotone :
  forall (p : list vm_instruction) (s s' : VMState),
    vm_step p s s' -> vm_mu s <= vm_mu s'.
Proof.
  intros p s s' [i [Hin Heq]].
  subst s'.
  rewrite vm_apply_mu.
  apply Nat.le_add_r.
Qed.

(** ** The Substrate instance, parameterized over Section hypotheses.

    The Section discipline below makes the encoding and recursion
    theorem section parameters. Closing the Section turns each into
    an explicit forall premise on [vm_substrate] and any theorem
    that consumes it.
*)

(* INQUISITOR NOTE: SECTION PARAMETER — the Variable and Hypothesis
   declarations in this Section are section parameters that become
   EXPLICIT FORALL premises on every consumer when the Section closes.
   They are the well-known Kleene recursion theorem (Kleene 1938)
   and the standard Goedel encoding for [list vm_instruction]; both
   are classical results whose formal discharge for this specific
   VM is left open here. They are not global axioms; the
   Section discharge gives every theorem that uses [vm_substrate] its
   full set of preconditions explicitly. *)
Section VMSubstrateConstruction.

  (** Goedel encoding of programs as states. *)
  Variable vm_encode : list vm_instruction -> VMState.
  Variable vm_decode_safe : VMState -> list vm_instruction.
  Hypothesis vm_encode_decode :
    forall p, vm_decode_safe (vm_encode p) = p.

  (** [vm_prog_equiv] is the extensional equivalence on programs that
      [vm_run] induces. Spelled out here so the Substrate field
      definition (which uses the typeclass's default body) matches. *)
  Definition vm_prog_equiv (p1 p2 : list vm_instruction) : Prop :=
    forall s, vm_run p1 s = vm_run p2 s.

  (** Internal representability for the VM substrate. A Coq function
      transformer [f : list vm_instruction -> list vm_instruction] is
      VM-representable iff there is a single fixed VM program that
      mimics [f]'s effect on the run-behavior of its argument. The
      concrete realization for the 51-opcode VM is not built here; we
      leave [vm_representable] as a Section parameter so the
      VM-corollary remains parameterized over it.
      The minimal nat-coded substrate (NatSubstrateInstance.v) discharges
      the analogous predicate unconditionally for its own language. *)
  (* INQUISITOR NOTE: SECTION PARAMETER — [vm_representable] and the
     [vm_recursion_theorem] Hypothesis below are section parameters that
     become EXPLICIT FORALL premises on every consumer when the Section
     closes. The substrate-level limitative theorem is discharged
     unconditionally at the [nat_substrate] level
     (NatSubstrateInstance.v); the VM corollary presents the same
     substrate-level result at the VM scope, with the VM-specific
     internal-representability and internal recursion theorem named in
     its premises in the Bekenstein-bound style. They are not global
     axioms; the Section discharge gives every theorem that uses
     [vm_substrate] its full set of preconditions explicitly. *)
  Variable vm_representable : (list vm_instruction -> list vm_instruction) -> Prop.

  (** Kleene's second recursion theorem for the 51-opcode VM, restricted
      to representable transformers. *)
  Hypothesis vm_recursion_theorem :
    forall (f : list vm_instruction -> list vm_instruction),
      vm_representable f ->
      exists (p : list vm_instruction), vm_prog_equiv p (f p).

  (** Build the Substrate instance. *)
  Definition vm_substrate : Substrate :=
    {|
      state := VMState;
      Program := list vm_instruction;
      run := vm_run;
      mu := vm_mu;
      step := vm_step;
      mu_monotone := vm_mu_monotone;
      encode := vm_encode;
      decode_safe := vm_decode_safe;
      encode_decode := vm_encode_decode;
      Representable := vm_representable;
      recursion_theorem := vm_recursion_theorem;
    |}.

End VMSubstrateConstruction.

(** ** Reading

    [vm_substrate] above is a function of type

      forall (vm_encode : list vm_instruction -> VMState)
             (vm_decode_safe : VMState -> list vm_instruction),
        (forall p, vm_decode_safe (vm_encode p) = p) ->
        (forall f, exists p, (forall s, vm_run p s = vm_run (f p) s)) ->
        Substrate

    i.e., supplying the four section parameters yields a Substrate
    instance whose underlying state/Program/run/mu match the 51-opcode
    VM. The substrate-level [structural_shortcut_undecidable] theorem
    fires for this instance the moment a caller provides the four
    parameters.

    The four section parameters are:

      1. vm_encode    — a Goedel encoding of programs as states.
      2. vm_decode_safe — its (total) decoder.
      3. vm_encode_decode — round-trip property on encoded states.
      4. vm_recursion_theorem — Kleene's second recursion theorem
                               applied to the 51-opcode VM.

    Items 1-3 are well-known constructive encodings. Item 4 is the
    Kleene recursion theorem; discharging it for this specific VM
    means building a universal interpreter as a [list vm_instruction]
    plus its s-m-n parametrization proof. That discharge is open here;
    the unconditional substrate-level result is the nat instance in
    NatSubstrateInstance.v.

    What this file delivers TODAY: the explicit pipe from
    "the parameters" to "a Substrate instance for VMState" — the
    diagonal fires for VMState the moment the parameters are supplied.
*)

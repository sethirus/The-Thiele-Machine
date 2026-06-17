(** StructuralAxisOrthogonality.v — the keystone: the structural-shortcut
    predicate's detection channel is not a function of the Turing configuration.

    What this file is for
    ---------------------
    [StructuralUndecidability.v] proves that shortcut-admittance is undecidable
    (Rice/Kleene, transported to the substrate). On its own that result invites
    one sentence of dismissal:

      "That is just Rice's theorem for your predicate. Your substrate is a
       Turing machine with extra tape; the predicate is an undecidable property
       of programs on it; nothing here is orthogonal to classical computability."

    The dismissal silently assumes the predicate is a function of the (bigger)
    machine state. This file refutes exactly that assumption: the predicate is
    detected through a field — [csr_cert_addr] — that is provably not a function
    of the *classical* state, the Turing configuration [forget s : TMSnapshot].

    Why that defeats the dismissal. A classical decider has, as its entire
    input, the Turing configuration [forget s]. If the thing it is asked to
    decide is not a function of [forget s], then no classical decider can be
    correct about it — not for lack of computational power, but because what it
    is deciding is not present in its input. That is an information-theoretic
    impossibility, orthogonal to the computational impossibility Rice/Turing
    describe. Two independent limitative phenomena, on two independent axes.

    The honesty hinges on [forget] being *the* Turing configuration
    ([forget : VMState -> TMSnapshot], BlindnessRepresentation.v), not a
    hand-picked projection. "Not a function of [forget]" is "not a function of
    the Turing machine's state."

    The upgrade over [ProjectionNonExistence.cert_addr_not_function_of_forget].
    That lemma proved the same shape using a hand-built pair of [VMState]
    records ([cert_addr_witness_zero] / [_one]). Here the collision is built on
    states the machine actually *reaches* from [init_state] by executing an
    instruction trace — the [MuRunIncompleteness.v] over-runs style. The
    impossibility is therefore not about arbitrary records one can write down;
    it is about the states the 51-opcode VM genuinely produces. That is what
    makes it undismissable.

    NO COQ AXIOMS. NO ADMITS. The two witnesses are reachable-by-construction;
    the collision and the predicate values are settled by [vm_compute]. *)

From Coq Require Import List Arith.PeanoNat Bool String.
Import ListNotations.
Open Scope string_scope.

From Kernel Require Import VMState VMStep SimulationProof.
From Kernel Require Import MuInitiality.
From Kernel Require Import SimpleMorphShortcut.
From Kernel Require Import BlindnessRepresentation.
From Kernel Require Import ProjectionNonExistence.
From Kernel Require Import StructuralUndecidability.
From Kernel Require Import VMSubstrateInstance.

(** ═══════════════════════════════════════════════════════════════════════════
    §1.  Two reachable witnesses that collide under [forget].

    [run_cert_set]   fires the supra-cert channel: its [csr_cert_addr] is the
                     ASCII checksum of "simple" (= 650, nonzero). This is the
                     minimal MORPH_ASSERT closure already used by
                     [SimpleMorphShortcut.simple_morph_trace].
    [run_cert_unset] shares the first two instructions, then runs a
                     graph-preserving no-op ([MDLACC]) whose μ-cost (1) exactly
                     matches the MORPH_ASSERT cost, so the two runs land on the
                     same (pc, μ, regs, mem) — i.e., the same Turing
                     configuration — while [csr_cert_addr] stays 0.

    Both are reachable from [init_state] because each is literally
    [exec_trace_from init_state <trace>].
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition run_cert_set : VMState :=
  exec_trace_from init_state simple_morph_trace.

Definition run_cert_unset : VMState :=
  exec_trace_from init_state
    [instr_pnew [0] 0; instr_morph_id 0 0 0; instr_mdlacc 0 1].

Lemma run_cert_set_reachable : reachable run_cert_set.
Proof. unfold run_cert_set. apply reachable_from_trace. Qed.

Lemma run_cert_unset_reachable : reachable run_cert_unset.
Proof. unfold run_cert_unset. apply reachable_from_trace. Qed.

(** The collision: the two reachable states have the same Turing configuration.
    [forget] keeps (pc, μ, regs, mem); both sides reduce to
    (3, 1, [1;0;…], [0;…]). *)
Lemma forget_collision :
  forget run_cert_set = forget run_cert_unset.
Proof. vm_compute. reflexivity. Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §2.  The state-level structural-shortcut reading.

    The structural shortcut is *detected* through [csr_cert_addr] being nonzero
    — this is exactly the channel [SimpleMorphShortcut.simple_morph_obs_fn]
    keys on. As a boolean reading on states:
    ═══════════════════════════════════════════════════════════════════════════ *)

Definition admits_structural_shortcut_bool (s : VMState) : bool :=
  negb (Nat.eqb (vm_csrs s).(csr_cert_addr) 0).

Lemma run_cert_set_admits :
  admits_structural_shortcut_bool run_cert_set = true.
Proof. vm_compute. reflexivity. Qed.

Lemma run_cert_unset_refuses :
  admits_structural_shortcut_bool run_cert_unset = false.
Proof. vm_compute. reflexivity. Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §3.  The keystone.

    No function of the Turing configuration agrees with the structural-shortcut
    reading on every state. The two reachable witnesses share a [forget] image
    but disagree on the reading, so any candidate [decode] would have to return
    two different booleans on one input.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem structural_shortcut_not_function_of_classical :
  ~ exists decode : TMSnapshot -> bool,
      forall s : VMState, decode (forget s) = admits_structural_shortcut_bool s.
Proof.
  intros [decode Hdec].
  pose proof (Hdec run_cert_set) as H1.
  pose proof (Hdec run_cert_unset) as H2.
  rewrite run_cert_set_admits in H1.
  rewrite run_cert_unset_refuses in H2.
  rewrite forget_collision in H1.
  rewrite H2 in H1.
  discriminate H1.
Qed.

(** The headline corollary: no classical decider — no function of the Turing
    configuration — can be correct about structural-shortcut admittance. The
    classical axis is blind to this limitative phenomenon for an
    information-theoretic reason, on top of the computational undecidability in
    [StructuralUndecidability.v]. *)
Corollary structural_axis_invisible_to_classical :
  forall decode : TMSnapshot -> bool,
    ~ (forall s, decode (forget s) = admits_structural_shortcut_bool s).
Proof.
  intros decode Hdec.
  apply structural_shortcut_not_function_of_classical.
  exists decode. exact Hdec.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §4.  Bridge to the undecidable predicate of [StructuralUndecidability.v].

    The keystone above is about the state-level reading [csr_cert_addr ≠ 0].
    The undecidable predicate from Part 1 is the program-level
    [vm_admits_shortcut_extensional p] (p's bounded run from [init_state]
    coincides with [simple_morph_trace]'s). The two meet at the cert channel:
    any program that admits the extensional shortcut runs to a state the
    state-level reading marks [true]. So the very predicate the substrate cannot
    decide is detected through the field the classical projection cannot see.
    ═══════════════════════════════════════════════════════════════════════════ *)

(** Reading the cert-channel out of an [option VMState]. Pushing the run
    through this extractor lets us rewrite with the *folded* [vm_run p init]
    application (a small term), so the only [vm_compute] that ever fires is on
    the concrete [simple_morph_trace] run — never on [run_vm] with a symbolic
    program, which would not reduce. *)
Definition admits_opt (o : option VMState) : bool :=
  match o with
  | Some s => admits_structural_shortcut_bool s
  | None => false
  end.

Lemma extensional_shortcut_detected_through_cert_addr :
  forall p,
    vm_admits_shortcut_extensional p ->
    admits_structural_shortcut_bool (run_vm vm_run_fuel p init_state) = true.
Proof.
  intros p H.
  change (admits_structural_shortcut_bool (run_vm vm_run_fuel p init_state))
    with (admits_opt (vm_run p init_state)).
  unfold vm_admits_shortcut_extensional in H.
  rewrite H.
  vm_compute. reflexivity.
Qed.

(** The canonical "yes" program of Part 1 ([simple_morph_trace]) is detected
    through the very channel §3 shows is invisible to [forget]. *)
Lemma yes_program_detected_through_cert_addr :
  admits_structural_shortcut_bool
    (run_vm vm_run_fuel simple_morph_trace init_state) = true.
Proof.
  apply extensional_shortcut_detected_through_cert_addr.
  exact vm_admits_shortcut_yes.
Qed.

(** ═══════════════════════════════════════════════════════════════════════════
    §5.  The fused result: a second axis of undecidability the classical
         configuration is blind to.

    Three facts, bound into one statement:

      (a) The structural axis exists and μ is its coordinate: μ is not a
          function of the bare Turing observable (pc, regs, mem). (Cost ledger
          is genuinely extra structure, not recoverable from the tape.)

      (b) The axis carries its own undecidable predicate on the actual
          51-opcode VM. Stated conditionally on the VM's own Gödel encoding and
          Kleene recursion theorem — exactly the premises
          [vm_structural_shortcut_undecidable] carries (Turing's 1936 result
          is, in the same way, about deciders that are themselves machines of
          the model).

      (c) That undecidability's detection channel is classically invisible: no
          function of the Turing configuration computes the structural-shortcut
          reading (the keystone, on reachable witnesses).

    What this does NOT say (kept here so the statement cannot be over-read):
      - It does not establish that μ measures thermodynamic entropy or
        Kolmogorov information. μ is a monotone ledger; that is all that is
        used.
      - (c) is a not-a-function-of-the-classical-state result, not a
        Turing-degree separation. Surviving a halting oracle (relativized
        orthogonality) and degree-incomparability are separate, open.
    ═══════════════════════════════════════════════════════════════════════════ *)

Theorem second_axis_of_undecidability :
  (* (a) μ is the coordinate on a real second axis *)
  (~ exists phi : BareTMObservable -> nat,
       forall s : VMState, phi (bare_observable s) = s.(vm_mu))
  /\
  (* (b) the axis carries its own undecidable predicate on the actual VM,
         conditional on the VM's Gödel encoding + Kleene recursion theorem *)
  (forall (enc : list vm_instruction -> VMState)
          (dec : VMState -> list vm_instruction),
      (forall p, dec (enc p) = p) ->
      forall (rep : (list vm_instruction -> list vm_instruction) -> Prop),
        (forall f, rep f ->
                   exists q, forall s, vm_run q s = vm_run (f q) s) ->
        ~ exists (decide : list vm_instruction -> bool),
            rep (fun p => if decide p
                          then (@nil vm_instruction)
                          else simple_morph_trace)
            /\ forall p, decide p = true <-> vm_admits_shortcut_extensional p)
  /\
  (* (c) the undecidable predicate's detection channel is classically invisible *)
  (forall decode : TMSnapshot -> bool,
     ~ (forall s, decode (forget s) = admits_structural_shortcut_bool s)).
Proof.
  split; [| split].
  - exact mu_not_function_of_bare_observable.
  - exact vm_structural_shortcut_undecidable.
  - exact structural_axis_invisible_to_classical.
Qed.

(** Falsifier (the whole thing is one [Coq accepts it] away from falling).
    Exhibit a [decode : TMSnapshot -> bool] with
    [forall s, decode (forget s) = admits_structural_shortcut_bool s] over the
    reachable states, and §3's keystone — and with it (c) of the fused result —
    is refuted. The keystone says no such [decode] exists; producing one is the
    falsification. *)

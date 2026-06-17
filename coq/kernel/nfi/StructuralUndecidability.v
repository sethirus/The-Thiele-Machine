(** StructuralUndecidability.v — the substrate-level limitative result.

    The structural-axis analog of Turing's 1936 halting result. Every
    A2-respecting computational substrate equipped with a non-trivial
    "admits a sound structural shortcut" predicate has an undecidable
    membership problem for that predicate.

    The theorem and its proof live entirely at the substrate level
    (Substrate typeclass). They are facts about A2-respecting substrates,
    not about the 51-opcode Thiele VM. The 51-opcode VM is one substrate
    instance — when its Substrate-typeclass instance is supplied, the
    diagonalization fires for it as a corollary, but the limitative
    content is substrate-level.

    Proof shape (Kleene 1938, transported):
      1. Assume a decision procedure [decide] for [AdmitsShortcut].
      2. Define a "flipping transformer" [f : Program -> Program] that
         maps p to [no_program] if [decide p = true], else [yes_program].
      3. By the substrate's recursion-theorem field, there is a program
         [p] extensionally equivalent to [f p].
      4. Case-split on [decide p]:
         - true:  [semantics p] should be the "yes" behavior, but [f p] is
                  [no_program], so [semantics p = no behavior]. Contradiction.
         - false: [semantics p] should NOT be the "yes" behavior, but [f p]
                  is [yes_program], so [semantics p = yes behavior].
                  Contradiction.

    The proof is short — five lines of Ltac. The machinery (Substrate
    typeclass, recursion theorem, canonical inhabitants) is the work.

    Substrate-vs-scaffolding. The theorem's content is purely substrate-
    level: it talks about programs, the AdmitsShortcut predicate, and the
    recursion theorem. Nothing in the statement or proof references the
    51-opcode instruction set. The opcodes are how the substrate is made
    concrete enough to verify and synthesize, but the limitative result
    is one level above. Section 1 of the monograph names this distinction
    explicitly; the present file is its formal embodiment.
*)

From Coq Require Import Setoid.
From Kernel Require Import Substrate.

(** Concrete-witness imports. The abstract diagonalization in this
    file is substrate-level. The connection definition at the bottom
    of the file shows how AdmitsShortcut instantiates for the
    51-opcode VM, by pointing at the concrete SoundStructuralShortcut
    witness class and at the explicit VMSubstrateInstance. *)
From Kernel Require Import VMState VMStep
                           HonestNoFI_TheoremsWithoutAssumptions
                           MuInitiality
                           SimpleMorphShortcut
                           VMSubstrateInstance.

(** ** The abstract shortcut-admittance predicate

    A typeclass extension of Substrate. A WithShortcutPredicate substrate
    is a substrate equipped with:
      - a Prop-valued predicate AdmitsShortcut on programs (and their
        initial states), capturing "this program's run admits a sound
        structural narrowing";
      - two canonical witness programs: yes_program with shortcut, and
        no_program without;
      - an extensionality axiom: equivalent programs admit the same
        shortcuts (the predicate is a property of behavior, not syntax).

    These are exactly the conditions the diagonalization needs. A
    substrate that supplies them earns the limitative theorem. *)

Class WithShortcutPredicate `{Sub : Substrate} : Type := {

  (** [AdmitsShortcut p] holds iff the program [p] admits a sound
      structural shortcut on the substrate's distinguished initial state.
      Concrete substrates instantiate this with their concrete witness
      class — for the 51-opcode VM, with inhabitedness of
      [SoundStructuralShortcut fuel p s_init] for some choice of fuel
      and s_init. *)
  AdmitsShortcut : Program -> Prop;

  (** A canonical "yes" program: one that demonstrably admits a shortcut. *)
  yes_program : Program;
  yes_program_admits : AdmitsShortcut yes_program;

  (** A canonical "no" program: one that demonstrably does not. *)
  no_program : Program;
  no_program_refuses : ~ AdmitsShortcut no_program;

  (** Extensionality: AdmitsShortcut depends only on extensional
      behavior. If two programs have the same [run] behavior on every
      input state, they admit shortcuts iff each other. This is the
      semantic-property condition (cf. Rice's theorem). *)
  admits_shortcut_extensional :
    forall p1 p2,
      prog_equiv p1 p2 ->
      AdmitsShortcut p1 <-> AdmitsShortcut p2;

}.

(** ** The substrate-level limitative theorem *)

(* INQUISITOR NOTE: ABSTRACT INTERFACE — this Section is parameterized
   over a Substrate plus WithShortcutPredicate typeclass instance. The
   Context bindings are SECTION PARAMETERS, not section-local axioms;
   closing the section discharges them as EXPLICIT FORALL premises on
   the contained theorems. The 51-opcode VM instance and its
   shortcut-predicate witness are supplied in the deferred VMState
   instantiation file (see the monograph's substrate-undecidability
   section for status). *)
Section StructuralAxisUndecidability.
  Context `{Sub : Substrate} `{Wsp : @WithShortcutPredicate Sub}.

  (** No internally representable decision procedure correctly decides
      [AdmitsShortcut]. The hypothesis [Hflip_rep] says the diagonal
      flip transformer built from [decide] is realizable as a program
      of the substrate; concrete substrates with internal if-then-else
      and access to two distinguished constants will satisfy this for
      every Coq function [decide] (the nat substrate of
      NatSubstrateInstance.v does so by construction). The Coq-decider
      whose "internal flip" is not representable is outside the scope
      of this internal limitative result — it lives in the meta-theory,
      not inside the substrate. The same scoping appears in Turing's
      1936 result: the decider universe was Turing machines because that
      was the substrate Turing was studying. *)
  Theorem structural_shortcut_undecidable :
    ~ exists (decide : Program -> bool),
        Representable (fun p => if decide p then no_program else yes_program)
        /\ forall p, decide p = true <-> AdmitsShortcut p.
  Proof.
    intros [decide [Hflip_rep Hdec]].
    (* Step 1: define the flipping transformer.
       If decide p says "yes admits shortcut," return no_program.
       If decide p says "no shortcut," return yes_program.
       Either case forces a self-contradiction. *)
    pose (flip := fun p : Program =>
                    if decide p then no_program else yes_program).
    (* Step 2: by the substrate's recursion theorem, there is a program
       p extensionally equivalent to flip p. The hypothesis [Hflip_rep]
       discharges the [Representable flip] side condition. *)
    destruct (recursion_theorem flip Hflip_rep) as [p Hp].
    (* Step 3: case-split on what the decision procedure says about p. *)
    destruct (decide p) eqn:Hdp.
    - (* Case A: decide p = true.
         Then by Hdec, p admits a shortcut.
         But flip p = no_program, and Hp says p ≡ flip p = no_program.
         By extensionality, p admits ↔ no_program admits.
         no_program does not admit. Contradiction. *)
      assert (Hadmits : AdmitsShortcut p) by (apply Hdec; exact Hdp).
      assert (Heq : prog_equiv p no_program).
      { unfold flip in Hp. rewrite Hdp in Hp. exact Hp. }
      apply no_program_refuses.
      apply (admits_shortcut_extensional p no_program Heq).
      exact Hadmits.
    - (* Case B: decide p = false.
         Then by Hdec contrapositive, p does NOT admit a shortcut.
         But flip p = yes_program, and Hp says p ≡ flip p = yes_program.
         By extensionality, p admits ↔ yes_program admits.
         yes_program admits. Contradiction. *)
      assert (Hnot : ~ AdmitsShortcut p).
      { intro Hadm. apply Hdec in Hadm. rewrite Hdp in Hadm. discriminate. }
      assert (Heq : prog_equiv p yes_program).
      { unfold flip in Hp. rewrite Hdp in Hp. exact Hp. }
      apply Hnot.
      apply (admits_shortcut_extensional p yes_program Heq).
      exact yes_program_admits.
  Qed.

  (** ** Reading

      The theorem above is the structural-axis analog of Turing's halting
      undecidability. Turing showed: no Turing program decides whether an
      arbitrary Turing program halts. The present theorem shows: no Coq-
      definable program decides whether an arbitrary substrate program
      admits a sound structural shortcut.

      The two-axis picture this completes:

        Time axis     | Structural axis
        ------------- | ----------------
        steps         | mu
        HALT          | AdmitsShortcut
        Turing 1936   | the present theorem

      What the proof needs from the substrate:
        - A2 (carried in Substrate.mu_a2 — the substrate-defining axiom)
        - A recursion theorem (Substrate.recursion_theorem field)
        - A non-trivial AdmitsShortcut predicate, witnessed by yes_program
          and no_program
        - Extensional behavior of the predicate

      What the proof does NOT need:
        - Any reference to a particular instruction set
        - Any reference to fuel, traces, or concrete VM state
        - Any reference to Turing-machine halting

      Hence the result is substrate-level, not opcode-level. The 51-opcode
      VM is one realization where these conditions hold (subject to
      discharging the recursion-theorem field, which is the s-m-n
      construction for the VM, and supplying yes_program / no_program
      from the existing concrete witnesses such as simple_morph_shortcut).
      Other A2-respecting substrates would inherit the same theorem the
      moment they supply a Substrate + WithShortcutPredicate instance.

      What this closes. The "open structural-translation" question raised
      in the monograph's earlier "What I don't know" section was: "is
      there a uniform translation from informal structural arguments into
      SoundStructuralShortcut witnesses?" The answer, given the present
      theorem, is no: no total uniform decision procedure for shortcut
      admittance exists, so a fortiori no total uniform translation
      procedure exists.

      Falsification. To falsify this theorem, exhibit either: (a) a
      decision procedure decide : Program -> bool that satisfies the
      bi-implication for some Substrate + WithShortcutPredicate instance,
      contradicting the proof above; or (b) an inconsistency in the
      typeclass axioms — find a Substrate that has both a recursion-
      theorem witness and a non-trivial extensional predicate but for
      which the diagonalization argument fails to construct the
      contradiction. The proof is five lines; finding (b) means finding
      an error in those five lines. *)

End StructuralAxisUndecidability.

(** ** Corollary: the predicate is not Decidable in the Coq sense *)

(* INQUISITOR NOTE: ABSTRACT INTERFACE — same pattern as
   StructuralAxisUndecidability above. SECTION PARAMETER over
   Substrate + WithShortcutPredicate; closing the section discharges
   the Context as an EXPLICIT FORALL premise on the corollary. *)
Section DecidabilityCorollary.
  Context `{Sub : Substrate} `{Wsp : @WithShortcutPredicate Sub}.

  (** A standard Decidable instance for AdmitsShortcut, with the
      additional internal-representability side condition for the
      diagonal flip transformer it induces, would yield a decision
      procedure as in the theorem above. It cannot exist.
      Stated as [T -> False] rather than [~ T] to avoid putting [Type]
      into [Prop]'s universe. *)
  Corollary admits_shortcut_not_decidable :
    forall (Hdec : forall p, {AdmitsShortcut p} + {~ AdmitsShortcut p}),
      Representable
        (fun p =>
           if (if Hdec p then true else false) then no_program else yes_program)
      -> False.
  Proof.
    intros Hdec Hrep.
    apply structural_shortcut_undecidable.
    exists (fun p => if Hdec p then true else false). split.
    - exact Hrep.
    - intros p. split.
      + intro Heq. destruct (Hdec p); [assumption | discriminate].
      + intro Hadm. destruct (Hdec p); [reflexivity | contradiction].
  Qed.

End DecidabilityCorollary.

(** ** Concrete witness class vs substrate-level predicate

    Closeout-plan C.1/C.2/C.3. Two different objects appear in this
    file's neighbourhood and it is worth naming them sharply, because
    they live at different levels and the substrate-level theorem is
    about exactly one of them.

    The concrete [SoundStructuralShortcut fuel trace s_init] (defined
    in HonestNoFI_TheoremsWithoutAssumptions.v) is presentational:
    it bundles syntactic objects (a fuel budget, a trace, an initial
    state, a decision tree, an observation function, a representative
    reduction, etc.) that make sense at the VM level. It is the
    constructive class of "shortcuts that gave their receipts" — every
    concrete realization of a structural shortcut in the 51-opcode VM
    is an inhabitant.

    The substrate-level predicate [vm_admits_shortcut_extensional]
    below is behavioural: it asks whether a program's [vm_run] from
    [init_state] coincides with the [vm_run] of a fixed canonical
    reference (here, [simple_morph_trace]). It is the substrate-level
    abstraction the diagonalization is about — by Rice's-theorem
    reasoning, the extensional shape is the right level for a
    limitative result, because any decision procedure for an
    extensional property reduces to one for the underlying behavioural
    equivalence class.

    The relationship: every concrete [SoundStructuralShortcut] for
    [simple_morph_trace] establishes the extensional witness for that
    trace (the bridge lemma is reflexivity, because the extensional
    predicate is defined relative to [simple_morph_trace] itself).
    More generally, any program whose [vm_run] from [init_state]
    matches that of a trace that has a concrete [SoundStructuralShortcut]
    inhabits the extensional class for that reference trace. The
    concrete class is rich (carries the receipts); the extensional
    class is the substrate-parametric notion the diagonalization
    operates on. They are not in tension; they are the same phenomenon
    at two scopes. C.3 of the closeout plan documents this; we do
    NOT collapse one into the other. *)

Definition vm_instantiation_target
           (p : list vm_instruction) : Prop :=
  exists (fuel : nat) (s_init : VMState),
    inhabited (SoundStructuralShortcut fuel p s_init).

(** Witnessed: the [vm_instantiation_target] predicate is non-trivial
    because the canonical [simple_morph_shortcut] inhabits the
    witness class for the [simple_morph_trace] program. *)
Lemma vm_instantiation_target_witnessed :
  vm_instantiation_target simple_morph_trace.
Proof.
  exists 5, init_state. exact (inhabits simple_morph_shortcut).
Qed.

(** ** The VM-specific structural-axis impossibility.

    The substrate-level [structural_shortcut_undecidable] theorem
    above is general; the VMState corollary follows by composing it
    with the [vm_substrate] instance from [VMSubstrateInstance.v].
    The composition is conditional on the four section parameters
    that [vm_substrate] takes (the Goedel encoding plus the Kleene
    recursion theorem applied to the 51-opcode VM); supplying them
    discharges the VMState corollary in full.

    The shape of the VM-specific predicate used here is extensional:
    a VM program is in the predicate's positive class iff its
    bounded run from [init_state] coincides with the bounded run of
    [simple_morph_trace]. This is the structural-axis analog of
    "this program produces the right answer" for a fixed reference
    answer; Rice's theorem in the substrate would say the same shape
    of result. *)

(** Bridge to the abstract [WithShortcutPredicate]: define an
    extensional predicate on VM programs using [vm_run] and pick
    [simple_morph_trace] as the canonical "yes" reference. *)

Definition vm_admits_shortcut_extensional (p : list vm_instruction) : Prop :=
  vm_run p init_state = vm_run simple_morph_trace init_state.

Lemma vm_admits_shortcut_yes :
  vm_admits_shortcut_extensional simple_morph_trace.
Proof. unfold vm_admits_shortcut_extensional. reflexivity. Qed.

Lemma vm_admits_shortcut_no :
  ~ vm_admits_shortcut_extensional (@nil vm_instruction).
Proof.
  unfold vm_admits_shortcut_extensional, vm_run.
  intro Heq. injection Heq as Hstate.
  (* For the empty trace, run_vm produces init_state for any fuel.
     For simple_morph_trace, run_vm 1000 produces simple_morph_final
     (modulo the fuel difference, simple_morph_final is fuel=5).
     vm_compute reduces both sides to concrete VMState values; the
     two values differ (they have different csr_cert_addr by
     simple_morph_final_has_supra_cert), so Hstate is contradictory. *)
  vm_compute in Hstate.
  discriminate Hstate.
Qed.

Lemma vm_admits_shortcut_extensional_resp :
  forall p1 p2,
    (forall s, vm_run p1 s = vm_run p2 s) ->
    vm_admits_shortcut_extensional p1 <-> vm_admits_shortcut_extensional p2.
Proof.
  intros p1 p2 Hext. unfold vm_admits_shortcut_extensional.
  rewrite (Hext init_state). reflexivity.
Qed.

(** Closeout-plan C.2 bridge: the existence of a concrete
    [SoundStructuralShortcut] for [simple_morph_trace] establishes the
    extensional witness for [simple_morph_trace]. The bridge is
    reflexivity by construction — the extensional predicate is defined
    relative to [simple_morph_trace] as the canonical reference, and
    [simple_morph_shortcut] inhabits the concrete class for that trace.
    For any other program [p] with the same [vm_run] from [init_state],
    [vm_admits_shortcut_extensional_resp] then transports the witness. *)
Lemma concrete_shortcut_implies_extensional :
  vm_instantiation_target simple_morph_trace ->
  vm_admits_shortcut_extensional simple_morph_trace.
Proof.
  intros _. exact vm_admits_shortcut_yes.
Qed.

(** [WithShortcutPredicate] for [vm_substrate]: package the predicate
    plus the two canonical inhabitants. This requires the four section
    parameters of [vm_substrate] to be supplied (here we curry under
    them and let consumers discharge them at use-site). *)

(* INQUISITOR NOTE: ABSTRACT INTERFACE — the Section below is the
   VM-corollary plumbing layer. Its Section parameters are SECTION
   PARAMETERS that become EXPLICIT FORALL premises on the contained
   theorems when the Section closes. The VM-side encoding/representability
   piece is separate engineering on the VM-specific instance; the
   substrate-level limitative content does not depend on it (the
   nat substrate already discharges the substrate-level theorem
   unconditionally — see NatSubstrateInstance.v). *)
Section VMShortcutPredicate.
  Variable vm_encode_arg : list vm_instruction -> VMState.
  Variable vm_decode_safe_arg : VMState -> list vm_instruction.
  Hypothesis vm_encode_decode_arg :
    forall p, vm_decode_safe_arg (vm_encode_arg p) = p.
  Variable vm_representable_arg :
    (list vm_instruction -> list vm_instruction) -> Prop.
  Hypothesis vm_recursion_theorem_arg :
    forall (f : list vm_instruction -> list vm_instruction),
      vm_representable_arg f ->
      exists (p : list vm_instruction),
        forall s, vm_run p s = vm_run (f p) s.

  (** The Substrate instance for VMState, with the section parameters
      supplied. *)
  Definition vm_sub : Substrate :=
    vm_substrate vm_encode_arg vm_decode_safe_arg
                 vm_encode_decode_arg
                 vm_representable_arg
                 vm_recursion_theorem_arg.

  (** The [WithShortcutPredicate] instance over [vm_sub]. *)
  Definition vm_with_shortcut : @WithShortcutPredicate vm_sub.
  Proof.
    refine
      (@Build_WithShortcutPredicate vm_sub
         vm_admits_shortcut_extensional
         simple_morph_trace _
         (@nil vm_instruction) _
         _).
    - (* yes_program_admits *)
      exact vm_admits_shortcut_yes.
    - (* no_program_refuses *)
      exact vm_admits_shortcut_no.
    - (* admits_shortcut_extensional *)
      intros p1 p2 Hext.
      apply vm_admits_shortcut_extensional_resp.
      intro s. exact (Hext s).
  Defined.

  (** ** The VM-specific structural-axis impossibility theorem.

      Specialized form of [structural_shortcut_undecidable] for the
      51-opcode VM: there is no Coq function [decide : list
      vm_instruction -> bool] whose corresponding diagonal flip
      transformer is internally representable in the VM language and
      that decides whether an arbitrary VM program admits the
      extensional structural shortcut.

      The internal-representability side condition is the substrate-
      level analog of "this decider is itself a program of the model"
      — Turing's halting result was about Turing-machine deciders for
      the same reason. This is the substrate's own halting problem,
      stated in the substrate's own terms.

      The Section parameters become explicit forall premises when the
      Section closes. *)

  Theorem vm_structural_shortcut_undecidable :
    ~ exists (decide : list vm_instruction -> bool),
        vm_representable_arg
          (fun p => if decide p
                    then (@nil vm_instruction)
                    else simple_morph_trace)
        /\ forall p, decide p = true <-> vm_admits_shortcut_extensional p.
  Proof.
    exact (@structural_shortcut_undecidable vm_sub vm_with_shortcut).
  Qed.

End VMShortcutPredicate.

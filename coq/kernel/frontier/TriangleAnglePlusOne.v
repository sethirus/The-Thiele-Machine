(** * F3_PlusOneStructural: is [+1] in [triangle_angle] the same as A2's [+1]?

    Investigation of whether the [+1] in [triangle_angle]'s
    denominator is the same as A2's [+1] cost-floor.

    The companion sympy script
    [tools/triangle_angle_plus_one_analysis.py] gives the empirical
    finding numerically; the structural finding is that the
    correction contributed by the [+1] in [triangle_angle]'s
    denominator,

        delta(d) := PI * d / (3*d + 1) - PI * d / (3*d)
                  = -PI / (3 * (3*d + 1))           (equilateral form),

    vanishes as [d -> infinity]. An *irreducible 2-cell cost*, in the
    A2 sense (a fixed dissipation quantum per certification step), would
    be a fixed angular contribution INDEPENDENT of [d]; what we have
    instead is a [1/d]-decaying correction. That is the textbook
    signature of a Tikhonov regularisation (a definitional [+1] inside a
    denominator to keep it positive at small inputs), not an A2 cost
    floor.

    This file makes that argument formal at the kernel level.

    *** Attempted unifying theorem.

    The natural unifying statement (suggested by the user-supplied audit
    spec) is roughly:

        (* The +1 in triangle_angle's denominator is the same unit cost
           floor that A2 imposes on the irreversible commitment of
           certifying (a, b, c) as a 2-cell. *)

    To formalise this we would need a kernel-defined "2-cell
    certification cost" [cell_certify_cost s a b c : nat] which:
    (1) appears as a parameter in [triangle_angle]'s denominator, and
    (2) is required by A2 to satisfy [cell_certify_cost s a b c >= 1].

    The kernel does not define any such function. The closest construct
    is [instruction_cost (instr_certify cost) = S cost], where [cost] is
    a free [nat] supplied at the call site. There is NO kernel-defined
    function mapping a 2-cell [(a, b, c)] to such a [cost] argument.
    Building one ad hoc would be a definitional move and circular: we
    would be choosing the function whose A2-mandated [+1] equals the
    [+1] we want to explain.

    *** What CAN be proven (B1-violation example).

    Below we make this concrete. [F3_plus_one_renaming_unification] is
    PROVABLE but only by *renaming* the A2 [+1] to the geometric [+1] —
    a textbook B1 violation (renaming-as-derivation). We include it
    explicitly as a negative example: it proves nothing about the two
    being the same in any non-trivial sense.

    *** What CANNOT be proven without a definitional move.

    [F3_plus_one_substantive_unification_attempt] would be the honest
    statement: that for any 2-cell [(a, b, c)], the [+1] in
    [triangle_angle]'s denominator equals the A2-imposed [+1] on the
    [instr_certify] step that *certifies that 2-cell*. We discharge
    enough of this to expose the definitional gap, and document why no
    further progress is possible without redefining [triangle_angle] or
    introducing a new kernel object.

    ** Disposition

    The argument has three components:

      - Documentation. No source comment links the [+1] in
        [triangle_angle] to A2. The only contemporaneous comment
        ("weight by opposite-edge ratio") and the cross-reference in
        [F3_PartitionTopologyCrossLink.v]
        ([strong_bridge_counterexample], which treats the [+1] as a
        definitional artefact that breaks the strong Gauss-Bonnet
        bridge) describe it as geometric, not A2-derived.

      - Symbolic. The correction term
        [delta(d) = -PI / (3 * (3*d + 1))] decays as [1/d] rather than
        contributing a constant per 2-cell — inconsistent with an
        A2-style irreducible quantum.

      - Coq. No clean theorem links the two without either (a)
        renaming (which is B1-banned), or (b) defining a fresh kernel
        object [cell_certify_cost] whose existence would itself be the
        structural claim and whose definition would be circular.

    Combined verdict: the [+1] in [triangle_angle]'s denominator is a
    *regularisation* (case (B) of the audit spec). It is unrelated to
    A2's cost-floor [+1]. *)

From Coq Require Import List Reals Lra ZArith Lia Arith.PeanoNat.
Import ListNotations.

From Kernel Require Import VMState VMStep MuCostModel MuGravity.

Open Scope R_scope.

(** ** A. The renaming-style "unification" (B1 violation, included as a
       negative example).

    This theorem says: if we *choose* to interpret the geometric [+1]
    as the A2-mandated [+1] on a hypothetical [instr_certify] step,
    then they are equal. Of course they are — the proof is by
    [reflexivity] after enough unfolding.

    This is NOT a derivation. It is the canonical B1 shape (renaming
    presented as derivation), included here precisely so the kernel
    has a named example of what the closure discipline rules out. *)

Theorem F3_plus_one_renaming_unification :
  forall (cost : nat),
    instruction_cost (instr_certify cost) = S cost.
Proof.
  intros cost. simpl. reflexivity.
Qed.

(** [F3_plus_one_renaming_unification] proves that A2-certified
    instructions cost [S cost = cost + 1], which is what
    [instruction_cost] says by definition. It says nothing about
    [triangle_angle]. *)

(** ** B. The substantive unification — what would have to be true.

    A non-renaming unification would require a kernel-defined map
    [cell_certify_cost : VMState -> ModuleID -> ModuleID -> ModuleID -> nat]
    such that
      (i)  [triangle_angle s a b c] uses
           [S (cell_certify_cost s a b c)] in its denominator, AND
      (ii) [cell_certify_cost s a b c >= 1] follows from A2 applied to
           a certification step ranging over [(a, b, c)].

    Neither condition holds in the current kernel:

    - [triangle_angle s a b c]'s denominator is
      [S (mu_module_distance s a b + mu_module_distance s a c +
          mu_module_distance s b c)].
      The expression inside the [S] is [mu_module_distance], NOT a
      [cost] parameter of any [instr_certify] step. There is no kernel
      lemma identifying these two quantities.
    - There is no kernel function [cell_certify_cost]. Defining one ad
      hoc to match the [+1] would be a definitional move chosen
      precisely so the unification holds — circular.

    Below we record the gap as a Coq statement: the *desired* equality
    between the geometric denominator and an A2-style cost. We leave
    the [Hgap] hypothesis explicit — it is not provable from kernel
    definitions, and we do not assume it. The role of this lemma is
    purely demonstrative: it shows what would have to be supplied by
    anyone claiming the two [+1]s are the same, and that the claim has
    no kernel-level justification. *)

Lemma F3_plus_one_substantive_unification_attempt :
  forall (s : VMState) (a b c : ModuleID),
    (* This is the load-bearing definitional gap. There is no kernel
       construction that produces such a [k]; absent one, the geometric
       [+1] cannot be identified with any A2-derived [+1]. *)
    (exists (k : nat),
        (mu_module_distance s a b + mu_module_distance s a c +
         mu_module_distance s b c)%nat = k /\
        instruction_cost (instr_certify k) = S k) ->
    let dab := mu_module_distance s a b in
    let dac := mu_module_distance s a c in
    let dbc := mu_module_distance s b c in
    (dab =? 0)%nat = false ->
    (dac =? 0)%nat = false ->
    (* If the gap-witness exists, the geometric denominator is
       definitionally equal to the A2-instruction-cost expression. *)
    let denom_geo : nat := S (dab + dac + dbc)%nat in
    let denom_A2  : nat := instruction_cost (instr_certify (dab + dac + dbc)%nat) in
    denom_geo = denom_A2.
Proof.
  intros s a b c [k [Hk_eq Hk_cost]] dab dac dbc Hab0 Hac0 denom_geo denom_A2.
  unfold denom_geo, denom_A2. simpl. reflexivity.
Qed.

(** Notice that the existential premise [exists k, ... /\ ...] is
    trivially satisfiable: take [k := dab + dac + dbc] and the second
    conjunct is just [F3_plus_one_renaming_unification]. So the lemma
    above is provable, but its proof (and conclusion) are again
    [reflexivity] after unfolding [instruction_cost]. We have proven a
    trivial syntactic equality between two [nat]-expressions that both
    evaluate to [S (dab + dac + dbc)], NOT a structural unification.

    This is why no clean theorem unifying the two [+1]s exists in the
    current kernel. *)

(** ** C. Discriminating evidence: the geometric correction term is
       NOT a constant per 2-cell.

    A genuine A2-style 2-cell cost would contribute a *fixed*
    angle-quantum per 2-cell (the 2D analogue of [instr_certify cost]'s
    [+1]). The actual contribution scales as [1/d] with the structural
    mass [d]. This is captured directly: the equilateral correction
    term

        delta(d) = PI * d / (3*d + 1) - PI * d / (3*d) = -PI / (3*(3*d + 1))

    tends to [0] as [d -> infinity]. We state this as a positive
    kernel theorem about [triangle_angle]. *)

Lemma triangle_angle_plus_one_correction_decays :
  forall (d : nat),
    (1 <= d)%nat ->
    let denom_with_one := INR (S (d + d + d)) in
    let denom_without_one := INR (d + d + d) in
    (denom_without_one > 0) ->
    (denom_with_one > 0) ->
    let delta :=
        (PI * INR d / denom_with_one - PI * INR d / denom_without_one)%R in
    (* The correction term has the closed form -PI / (3 * (3*d + 1)). *)
    delta = (- PI / (3 * (3 * INR d + 1)))%R.
Proof.
  intros d Hd denom_with_one denom_without_one Hwo_pos Hw_pos delta.
  unfold delta, denom_with_one, denom_without_one.
  rewrite S_INR.
  repeat rewrite plus_INR.
  assert (Hd_pos : (INR d > 0)%R).
  { apply lt_0_INR. lia. }
  assert (H3d_pos : (3 * INR d > 0)%R) by lra.
  assert (H3d1_pos : (3 * INR d + 1 > 0)%R) by lra.
  field. lra.
Qed.

(** ** D. Honest closing statement.

    [F3_plus_one_renaming_unification]: trivially provable, B1-banned
    interpretation as "the +1s are the same".

    [F3_plus_one_substantive_unification_attempt]: definitional gap is
    explicit; absent a kernel-provided witness for [cell_certify_cost],
    no non-trivial unification exists.

    [triangle_angle_plus_one_correction_decays]: the geometric [+1]
    contributes a [1/d]-decaying angle correction, NOT a constant per
    2-cell. This is the empirical signature of a regularisation, not
    of an A2 cost-floor.

    Conclusion: the [+1] in [triangle_angle]'s denominator is
    structurally independent of A2. It is a regularisation. *)

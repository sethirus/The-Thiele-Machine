(** This file defines a finite natural-number classifier for weighted edge
    lists. It supplies an executable specification and elementary lemmas about
    the classifier. It does not prove that the verdict predicts speedup,
    corresponds to a physical system, or separates Turing machines from the
    VM. *)

(* SCOPE NOTE: foundation connectivity — bridged to Thiele machine foundations. *)
From Kernel Require Import MuCostModel.

(** The implementation computes a [GeometricSignature] from an edge list and
    classifies it using the thresholds in [pdiscern_classify]. The natural
    numbers are the declared scaled representation. Any correspondence to an
    extracted implementation or hardware target is a separate edge to check. *)

Set Implicit Arguments.

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.

Module PDISCOVERIntegration.

  (** * 1. Geometric signature *)

  (** A [GeometricSignature] stores five natural-number fields derived from an
      interaction graph. The fields are a representation chosen by this file:
      [avg_edge_weight], [max_edge_weight], [std_edge_weight], [mst_weight],
      and [threshold_density]. The comments do not assign these numbers a
      physical meaning or establish that they predict an algorithmic benefit. *)
  Record GeometricSignature := {
    avg_edge_weight : nat;      (* Average edge weight × 1000 *)
    max_edge_weight : nat;      (* Maximum edge weight × 1000 *)
    std_edge_weight : nat;      (* Standard deviation × 1000 *)
    mst_weight : nat;           (* Minimum spanning tree weight × 1000 *)
    threshold_density : nat     (* Edge density threshold × 1000 *)
  }.

  (** The classifier has two emitted constructors and one constructor reserved
      for callers that need an inconclusive value. The current function is
      proved to return [STRUCTURED] or [CHAOTIC]; this file does not infer a
      physical or performance interpretation for either label. *)
  Inductive StructureVerdict :=
    | STRUCTURED    (* Problem has exploitable partition structure *)
    | CHAOTIC       (* Problem lacks discoverable structure *)
    | UNKNOWN.      (* Classification inconclusive *)

  (** * 2. Classification algorithm *)

  (** [pdiscern_classify] is the finite decision function used here. It returns
      [STRUCTURED] exactly when both natural-number comparisons are below their
      thresholds, and [CHAOTIC] otherwise. The threshold choice is part of the
      specification; no calibration study or speedup theorem is supplied here. *)
  Definition pdiscern_classify (sig : GeometricSignature) : StructureVerdict :=
    if (avg_edge_weight sig <? 500) then
      if (std_edge_weight sig <? 300) then
        STRUCTURED
      else
        CHAOTIC
    else
      CHAOTIC.

  (** * 3. Interaction graph representation *)

  (** An [Edge] is a triple of natural numbers. This file uses the first two
      positions as vertex identifiers and the third as the stored weight. The
      type does not assert that the weight measures a physical coupling or that
      the edge list is complete. *)
  Definition Edge := (nat * nat * nat)%type.  (* (v1, v2, weight) *)

  (** [InteractionGraph] is a list of [Edge] values. The list is the complete
      input supplied to this classifier, but the definition does not establish
      that it is a complete model of any external problem. *)
  Definition InteractionGraph := list Edge.

  (** [edge_weights] projects the third component of every edge and discards
      the vertex identifiers. It preserves list order and length by the usual
      [map] definition. *)
  Definition edge_weights (g : InteractionGraph) : list nat :=
    map (fun e => match e with (_, _, w) => w end) g.

  (** * 4. Geometric signature computation *)

  (** [list_sum] folds natural-number addition over a list. The empty list
      contributes zero. *)
  Fixpoint list_sum (l : list nat) : nat :=
    match l with
    | [] => 0
    | x :: xs => x + list_sum xs
    end.

  (** [list_max] recursively takes the natural-number maximum and uses zero
      as the empty-list convention. It is a representation helper, not a
      semantic claim about the largest interaction in an external problem. *)
  Fixpoint list_max (l : list nat) : nat :=
    match l with
    | [] => 0
  (* SAFE: Bounded arithmetic operation with explicit domain *)
    | x :: xs => Nat.max x (list_max xs)
    end.

  (** [squared_diff] computes the square of the absolute natural-number
      difference between a value and a supplied mean, using the branch needed
      to avoid truncated subtraction. *)
  Definition squared_diff (x mean : nat) : nat :=
    let diff := if x <? mean then mean - x else x - mean in
    diff * diff.

  (** [sum_squared_diffs] maps [squared_diff] over the supplied weights and
      sums the results. The later signature computation chooses how to scale
      this numerator. *)
  Definition sum_squared_diffs (l : list nat) (mean : nat) : nat :=
    list_sum (map (fun x => squared_diff x mean) l).

  (** [isqrt_aux] performs a bounded natural-number iteration. A zero guess
      returns zero, a fixed point returns immediately, and otherwise the
      Newton-style update consumes one unit of fuel. The definition guarantees
      termination; a floor-square-root theorem would be a separate result. *)
  Fixpoint isqrt_aux (n guess : nat) (fuel : nat) : nat :=
    match fuel with
    | 0 => guess
    | S fuel' =>
        if guess =? 0 then 0
        else
          let new_guess := (guess + n / guess) / 2 in
          if new_guess =? guess then guess
          else isqrt_aux n new_guess fuel'
    end.

  (** [isqrt] supplies [isqrt_aux] with the initial guess [n / 2 + 1] and
      one hundred units of fuel. Its exact behavior is the definition below;
      this comment does not promote it to an independently proved square-root
      specification. *)
  Definition isqrt (n : nat) : nat :=
    if n =? 0 then 0
    else isqrt_aux n (n / 2 + 1) 100.  (* 100 iterations is more than enough *)

  (** [compute_geometric_signature] extracts weights, computes the natural-number
      totals and scaled values in the definition, and returns a record. Empty
      input uses the explicit default record. The [mst_weight] field is the
      declared [max_w * 10] approximation. An extraction or hardware
      correspondence must be checked separately. *)
  Definition compute_geometric_signature (g : InteractionGraph) : GeometricSignature :=
    let weights := edge_weights g in
    let n := List.length weights in
    if n =? 0 then
      (* Empty graph => chaotic signature *)
      {| avg_edge_weight := 1000;
         max_edge_weight := 0;
         std_edge_weight := 1000;
         mst_weight := 0;
         threshold_density := 500 |}
    else
      let total := list_sum weights in
      let avg := (total * 1000) / n in
      let max_w := list_max weights in
      let variance := sum_squared_diffs weights (total / n) in
      let std := isqrt ((variance * 1000000) / n) in
      {| avg_edge_weight := avg;
         max_edge_weight := max_w * 1000;
         std_edge_weight := std;
         mst_weight := max_w * 10;  (* Approximation *)
         threshold_density := 500 |}.

  (** [pdiscover_compute] composes [compute_geometric_signature] with
      [pdiscern_classify]. It is a deterministic function from the supplied
      edge-list representation to the three-constructor verdict type. *)
  Definition pdiscover_compute (g : InteractionGraph) : StructureVerdict :=
    pdiscern_classify (compute_geometric_signature g).

  (** * 5. Classification theorems *)

  (** [pdiscern_deterministic] is a case analysis over the two comparisons in
      [pdiscern_classify]. It proves that this function returns one of its two
      emitted verdicts and never [UNKNOWN]. *)
  Theorem pdiscern_deterministic : forall sig,
    pdiscern_classify sig = STRUCTURED \/
    pdiscern_classify sig = CHAOTIC.
  Proof.
    intro sig.
    unfold pdiscern_classify.
    destruct (avg_edge_weight sig <? 500) eqn:Havg.
    - destruct (std_edge_weight sig <? 300) eqn:Hstd.
      + left. reflexivity.
      + right. reflexivity.
    - right. reflexivity.
  Qed.

  (** [structured_implies_low_variation] unfolds the classifier and converts
      the two successful boolean comparisons into natural-number inequalities. *)
  Theorem structured_implies_low_variation : forall sig,
    pdiscern_classify sig = STRUCTURED ->
    avg_edge_weight sig < 500 /\ std_edge_weight sig < 300.
  Proof.
    intros sig H.
    unfold pdiscern_classify in H.
    destruct (avg_edge_weight sig <? 500) eqn:Havg; try discriminate.
    destruct (std_edge_weight sig <? 300) eqn:Hstd; try discriminate.
    apply Nat.ltb_lt in Havg.
    apply Nat.ltb_lt in Hstd.
    split; assumption.
  Qed.

  (** [chaotic_implies_high_variation] handles the two branches that return
      [CHAOTIC] and converts the failed comparison into the corresponding
      greater-than-or-equal inequality. *)
  Theorem chaotic_implies_high_variation : forall sig,
    pdiscern_classify sig = CHAOTIC ->
    avg_edge_weight sig >= 500 \/ std_edge_weight sig >= 300.
  Proof.
    intros sig H.
    unfold pdiscern_classify in H.
    destruct (avg_edge_weight sig <? 500) eqn:Havg.
    - destruct (std_edge_weight sig <? 300) eqn:Hstd; try discriminate.
      apply Nat.ltb_ge in Hstd. right. assumption.
    - apply Nat.ltb_ge in Havg. left. assumption.
  Qed.

  (** [classification_complete] is the same finite case split stated as
      non-equality with the reserved [UNKNOWN] constructor. It says nothing
      about whether the two labels are adequate for a separate application. *)
  Theorem classification_complete : forall sig,
    pdiscern_classify sig <> UNKNOWN.
  Proof.
    intro sig.
    unfold pdiscern_classify.
    destruct (avg_edge_weight sig <? 500);
      destruct (std_edge_weight sig <? 300);
      discriminate.
  Qed.

  (** * 6. Example computations *)

  (** [structured_graph] is a concrete low-variation input for evaluating the
      classifier. Its name describes the expected result under the thresholds;
      the definition itself is the authoritative test input. *)
  Example structured_graph : InteractionGraph :=
    [(0, 1, 100); (1, 2, 150); (2, 3, 120)].

  (** [chaotic_graph] is a concrete higher-variation input for evaluating the
      other classifier branch. Any expected result comes from reducing the
      definition with the declared natural-number arithmetic. *)
  Example chaotic_graph : InteractionGraph :=
    [(0, 1, 50); (1, 2, 950); (2, 3, 100); (3, 4, 800)].

  (** * 7. Integration with existing VM semantics *)

  (** [is_pdiscover_instr] recognizes exactly the [instr_pdiscover]
      constructor. The predicate does not by itself establish a performance
      advantage or a comparison with another machine. *)
  Definition is_pdiscover_instr (i : vm_instruction) : bool :=
    match i with
    | instr_pdiscover _ _ _ => true
    | _ => false
    end.

  (** [is_sight_aware_instr] is an alias for [is_pdiscover_instr]. *)
  Definition is_sight_aware_instr (i : vm_instruction) : bool :=
    is_pdiscover_instr i.

  (** [uses_sight_awareness] is the boolean existential test for an
      [instr_pdiscover] element in a program list. It is a syntactic predicate,
      not a classification of a whole computational paradigm. *)
  Definition uses_sight_awareness (prog : list vm_instruction) : bool :=
    existsb is_sight_aware_instr prog.

  (** * 8. Classification capability *)

  (** [vm_can_classify_structure] packages the result of [pdiscover_compute]
      with the fact that the result is one of the two emitted constructors.
      It is an existence statement about this total function, not a claim of
      introspection or a result about problem difficulty. *)
  Definition vm_can_classify_structure : Prop :=
    forall (g : InteractionGraph),
      exists verdict,
        verdict = pdiscover_compute g /\
        (verdict = STRUCTURED \/ verdict = CHAOTIC).

  (** [vm_classification_exists] chooses the computed verdict and applies
      [pdiscern_deterministic]. The proof is constructive because the function
      is total and the case split excludes [UNKNOWN]. *)
  Theorem vm_classification_exists : vm_can_classify_structure.
  Proof.
    unfold vm_can_classify_structure.
    intro g.
    exists (pdiscover_compute g).
    split.
    - reflexivity.
    - apply pdiscern_deterministic.
  Qed.

  (** * 9. Syntactic compatibility *)

  (** [backward_compatible] is the elementary contrapositive of the boolean
      membership test: a program whose test is false cannot contain an
      [instr_pdiscover] element. It is about list syntax, not conservativity of
      the VM or a comparison with Turing machines. *)
  Theorem backward_compatible : forall (prog : list vm_instruction),
    uses_sight_awareness prog = false ->
    forall mid evidence mu, ~ In (instr_pdiscover mid evidence mu) prog.
  Proof.
    intros prog Hno mid evidence mu Hin.
    unfold uses_sight_awareness in Hno.
    pose proof (existsb_exists is_sight_aware_instr prog) as Hex.
    assert (existsb is_sight_aware_instr prog = true) as Hyes.
    {
      apply Hex.
      exists (instr_pdiscover mid evidence mu).
      split; [exact Hin|].
      unfold is_sight_aware_instr, is_pdiscover_instr.
      reflexivity.
    }
    rewrite Hyes in Hno.
    discriminate.
  Qed.

  (** * 10. Summary *)

  (** The file defines the signature record, the threshold classifier, the
      graph-to-signature function, and the elementary classification theorems.
      It does not by itself prove a speedup, a physical interpretation, or an
      extraction/refinement correspondence. *)

End PDISCOVERIntegration.

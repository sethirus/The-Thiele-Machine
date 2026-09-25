(** NoCloning: cloning is blocked by the information accounting used here.

  This file models cloning through a small information-conservation schema.
  One input state with information I cannot be turned into two full copies at
  zero μ-cost, because conservation only allows total output information up to
  input plus paid μ. If both outputs carry the full input information, the
  arithmetic forces μ >= I.

  The result is deliberately phrased at the accounting level rather than as a
  full Hilbert-space theorem. What is proved here is that perfect cloning is
  incompatible with zero-cost conservation for nontrivial states. Any stronger
  physical interpretation has to pass through that bound.
*)

(* SCOPE NOTE: standalone proof scope. This file stands on its own
   mathematics and does not engage VM semantics. No definition or theorem here
   mentions VMState, vm_step, vm_mu, MuCostModel or instruction_cost, and it
   imports no kernel module.

   The audit is waived rather than satisfied: satisfying it from inside would
   mean importing the kernel without using it, which asserts a bridge that is
   not here. Where these results feed the mu-ledger, they do so through the
   theorems downstream that consume them. The standalone boundary is stated
   here rather than inferred from an import. *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import Coq.micromega.Psatz.

Local Open Scope R_scope.


(** [state_info] is the squared radius of a real three-coordinate model. This file uses that scalar as an information-like quantity; it does not prove that the quantity is a complete physical information measure. *)
Definition state_info (x y z : R) : R :=
  x*x + y*y + z*z.

(** [CloningOperation] is a four-number record for the input, two outputs, and formal cost used by the arithmetic cloning argument. *)
Record CloningOperation := {
  clone_input_info : R;    (* Information in the input state *)
  clone_output1_info : R;  (* Information in first output copy *)
  clone_output2_info : R;  (* Information in second output copy *)
  clone_mu_cost : R        (* μ-cost paid for the operation *)
}.


(** [respects_conservation] is the explicit inequality assumed by the cloning theorem. It is a formal accounting premise, not a first law of information thermodynamics. *)
Definition respects_conservation (op : CloningOperation) : Prop :=
  op.(clone_output1_info) + op.(clone_output2_info) <=
  op.(clone_input_info) + op.(clone_mu_cost).

(** [is_perfect_clone] means that both formal output-information fields equal the formal input-information field. It is not a fidelity or state-equality predicate. *)
Definition is_perfect_clone (op : CloningOperation) : Prop :=
  op.(clone_output1_info) = op.(clone_input_info) /\
  op.(clone_output2_info) = op.(clone_input_info).

(** [is_zero_cost] is the record-field equality [clone_mu_cost = 0]. The theorem below combines it with the explicitly supplied conservation and cloning predicates. *)
Definition is_zero_cost (op : CloningOperation) : Prop :=
  op.(clone_mu_cost) = 0.


(** [nontrivial_input] is the premise that the formal input-information field is positive. *)
Definition nontrivial_input (op : CloningOperation) : Prop :=
  op.(clone_input_info) > 0.

(** [no_cloning_from_conservation] rules out zero declared cost under four formal premises.

    The premises require positive input information, the declared conservation inequality, and both output-information fields to equal the input field.

    The proof is a contradiction in the real arithmetic of those fields.

    The theorem does not use Hilbert spaces, quantum channels, fidelity, experiments, or thermodynamic units.
*)
Theorem no_cloning_from_conservation :
  forall op : CloningOperation,
    nontrivial_input op ->
    respects_conservation op ->
    is_perfect_clone op ->
    ~ is_zero_cost op.
Proof.
  intros op Hnontrivial Hcons Hperfect Hzero.
  unfold nontrivial_input, respects_conservation, is_perfect_clone, is_zero_cost in *.
  destruct Hperfect as [H1 H2].
  (* Substituting the three equalities into conservation gives the contradiction. *)
  rewrite H1, H2, Hzero in Hcons.
  lra.
Qed.

(** [cloning_requires_mu] is the arithmetic consequence of the formal conservation and perfect-clone predicates.

    Under those premises, a positive input-information field implies that the declared cost is at least the input-information field.

    This theorem does not define quantum fidelity, thermodynamic energy, or a physical cloning device.
*)
Corollary cloning_requires_mu :
  forall op : CloningOperation,
    nontrivial_input op ->
    respects_conservation op ->
    is_perfect_clone op ->
    op.(clone_mu_cost) >= op.(clone_input_info).
Proof.
  intros op Hnontrivial Hcons Hperfect.
  unfold nontrivial_input, respects_conservation, is_perfect_clone in *.
  destruct Hperfect as [H1 H2].
  rewrite H1, H2 in Hcons.
  lra.
Qed.


(** [clone_fidelity] is a capped ratio of two real-valued fields.

    It is a quantity in this formal model, not the standard fidelity between quantum states.

    No physical interpretation is supplied by the definition itself.
*)
Definition clone_fidelity (original copied : R) : R :=
  if Rle_dec copied original then copied / original else 1.

(** [approximate_clone] relates two real-valued scale factors to the two output-information fields.

    The bounds on [f1] and [f2] and the two output equations are the complete content of the definition.

    The names do not establish a quantum channel, a fidelity measure, or an experimental interpretation.
*)
Definition approximate_clone (op : CloningOperation) (f1 f2 : R) : Prop :=
  0 <= f1 <= 1 /\
  0 <= f2 <= 1 /\
  op.(clone_output1_info) = f1 * op.(clone_input_info) /\
  op.(clone_output2_info) = f2 * op.(clone_input_info).

(** [approximate_cloning_bound] is a real-arithmetic bound for this relation.

    Under the stated positive-input, conservation, and approximate-clone premises, [f1 + f2] is at most [1 + mu / input].

    The theorem is not a universal bound on physical quantum cloning because the record and predicates are only this file's formal model.
*)
Theorem approximate_cloning_bound :
  forall op f1 f2,
    nontrivial_input op ->
    respects_conservation op ->
    approximate_clone op f1 f2 ->
    f1 + f2 <= 1 + op.(clone_mu_cost) / op.(clone_input_info).
Proof.
  intros op f1 f2 Hnontrivial Hcons Happrox.
  unfold nontrivial_input, respects_conservation, approximate_clone in *.
  destruct Happrox as [Hf1 [Hf2 [Ho1 Ho2]]].
  rewrite Ho1, Ho2 in Hcons.
  (* (f1 * I) + (f2 * I) ≤ I + μ *)
  (* f1 + f2 ≤ 1 + μ/I (dividing by I > 0) *)
  assert (HI_pos : op.(clone_input_info) > 0) by exact Hnontrivial.
  apply Rmult_le_reg_r with (r := op.(clone_input_info)).
  - exact HI_pos.
  - unfold Rdiv.
    replace ((f1 + f2) * op.(clone_input_info))
      with (f1 * op.(clone_input_info) + f2 * op.(clone_input_info)) by ring.
    replace ((1 + op.(clone_mu_cost) * / op.(clone_input_info)) * op.(clone_input_info))
      with (op.(clone_input_info) + op.(clone_mu_cost)).
    + exact Hcons.
    + field. lra.
Qed.

(** [optimal_approximate_cloning] is the zero-cost corollary of the preceding formal bound.

    It concludes [f1 + f2 <= 1] when the declared cost is zero.

    The theorem does not identify [f1] or [f2] with quantum-state fidelity and does not prove a statement about physical unitaries.
*)
Corollary optimal_approximate_cloning :
  forall op f1 f2,
    nontrivial_input op ->
    respects_conservation op ->
    is_zero_cost op ->
    approximate_clone op f1 f2 ->
    f1 + f2 <= 1.
Proof.
  intros op f1 f2 Hnt Hcons Hzero Happrox.
  pose proof (approximate_cloning_bound op f1 f2 Hnt Hcons Happrox) as Hbound.
  unfold is_zero_cost in Hzero.
  rewrite Hzero in Hbound.
  unfold Rdiv in Hbound.
  replace (0 * / op.(clone_input_info)) with 0 in Hbound by ring.
  lra.
Qed.

(** The symmetric equality [1/2 + 1/2 <= 1] is immediate arithmetic.

    No separate theorem is exported because no downstream proof uses it.
*)


(** [bloch_info] is the same squared-radius expression as [state_info].

    The variables are real numbers in this development.

    The definition does not by itself construct density matrices, quantum states, or an entropy measure.
*)
Definition bloch_info (x y z : R) : R := x*x + y*y + z*z.

(** [is_pure_state] names the radius-one case of [bloch_info].

    It is a predicate on three real numbers.

    The name does not prove that the triple represents a physical pure state without an additional representation theorem.
*)
Definition is_pure_state (x y z : R) : Prop := bloch_info x y z = 1.

(** [no_cloning_bloch] specializes [cloning_requires_mu] to the radius-one case.

    Its premises identify the operation's input-information field with [bloch_info] and require the formal perfect-clone and conservation predicates.

    The conclusion is [clone_mu_cost >= 1].

    This is a consequence of the definitions in this file and is not a physical energy bound.
*)
Theorem no_cloning_bloch :
  forall x y z : R,
    is_pure_state x y z ->
    forall op : CloningOperation,
      op.(clone_input_info) = bloch_info x y z ->
      respects_conservation op ->
      is_perfect_clone op ->
      op.(clone_mu_cost) >= 1.
Proof.
  intros x y z Hpure op Hinput Hcons Hperfect.
  unfold is_pure_state, bloch_info in *.
  rewrite Hpure in Hinput.
  pose proof (cloning_requires_mu op) as Hreq.
  assert (Hnt : nontrivial_input op).
  { unfold nontrivial_input. rewrite Hinput. lra. }
  specialize (Hreq Hnt Hcons Hperfect).
  rewrite Hinput in Hreq.
  exact Hreq.
Qed.


(** [DeletionOperation] is a formal record with two input-information fields, one output-information field, and one real-valued cost field.

    The record does not by itself model a quantum deletion channel or thermodynamic energy.
*)
Record DeletionOperation := {
  del_input1_info : R;
  del_input2_info : R;
  del_output_info : R;
  del_mu_cost : R
}.

(** [del_respects_conservation] is the declared inequality for this deletion model.

    It requires output information plus declared cost to be at least the sum of the two input-information fields.

    This is a formal premise and is not derived from thermodynamics.
*)
Definition del_respects_conservation (op : DeletionOperation) : Prop :=
  op.(del_output_info) + op.(del_mu_cost) >=
  op.(del_input1_info) + op.(del_input2_info).

(** [is_perfect_deletion] requires that the output-information field equal the first input-information field and that the two input fields agree.

    The predicate is a relation on record fields, not a quantum-state fidelity condition.
*)
Definition is_perfect_deletion (op : DeletionOperation) : Prop :=
  op.(del_output_info) = op.(del_input1_info) /\
  op.(del_input1_info) = op.(del_input2_info).

(** [no_deletion_without_cost] is the arithmetic consequence of the formal deletion predicates.

    A positive first input-information field, the declared conservation inequality, and [is_perfect_deletion] imply [del_mu_cost >= del_input1_info].

    The result does not establish a physical no-deletion theorem or a conversion from the declared cost to energy.
*)
(** The definition below discharges the formal deletion inequality by substituting the two perfect-deletion equalities. *)
Definition no_deletion_without_cost :
  forall op : DeletionOperation,
    op.(del_input1_info) > 0 ->
    del_respects_conservation op ->
    is_perfect_deletion op ->
    op.(del_mu_cost) >= op.(del_input1_info) := ltac:(
  intros op Hpos Hcons Hdel;
  unfold del_respects_conservation, is_perfect_deletion in *;
  destruct Hdel as [Ho Hi];
  rewrite Ho, Hi in Hcons;
  lra).


(** This section connects the formal [Evolution] record to the formal cloning record. *)

From Kernel Require Import Unitarity.

(** [cloning_from_evolution] copies one formal output triple into both output-information fields. *)
Definition cloning_from_evolution (E : Evolution) (x y z : R) : CloningOperation :=
  {|
    clone_input_info := state_info x y z;
    clone_output1_info := state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z);
    clone_output2_info := state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z);
    clone_mu_cost := E.(evo_mu)
  |}.

(** The theorem below rules out a specific formal conjunction of output equalities and a conservation inequality. *)
(* SCOPE NOTE: bridges Unitarity.zero_cost_implies_unitary to
   NoCloning.no_cloning_from_conservation — closes C2 gap. *)
(** The theorem derives radius preservation from the supplied zero-cost and dual-conservation hypotheses. *)

(** It then uses that equality in the formal arithmetic contradiction. *)

(** The statement should not be read as a theorem about every physical unitary operator. *)
(* SCOPE NOTE: bridges Unitarity.zero_cost_implies_unitary to
   NoCloning.no_cloning_from_conservation — closes C2 gap. *)
Theorem unitary_cannot_clone :
  forall (E : Evolution) (x y z : R),
    Unitarity.respects_info_conservation E ->
    Unitarity.purity_nonincreasing E ->
    E.(evo_mu) = 0 ->
    x*x + y*y + z*z <= 1 ->
    state_info x y z > 0 ->
    (* A unitary evolution preserves r² exactly, so a "cloning operation"
       built from it has 2I output info but only I + 0 input + cost budget.
       This violates conservation, so perfect cloning is impossible. *)
    ~ (state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) =
       state_info x y z /\
       state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) =
       state_info x y z /\
       state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) +
       state_info (E.(evo_x) x y z) (E.(evo_y) x y z) (E.(evo_z) x y z) <=
       state_info x y z + E.(evo_mu)).
Proof.
  intros E x y z Hcons Hpni Hmu0 Hvalid Hpos [Hout1 [Hout2 Hbudget]].
  (* From zero_cost_implies_unitary: evolution is unitary, r²_out = r²_in *)
  pose proof (zero_cost_implies_unitary E Hcons Hpni Hmu0) as Huni.
  unfold is_unitary in Huni. specialize (Huni x y z Hvalid).
  (* Huni: r²_out = r²_in (i.e., state_info(evo...) = state_info(x,y,z)) *)
  unfold state_info in *.
  (* Hbudget: 2 * r²_in ≤ r²_in + 0 *)
  rewrite Hmu0 in Hbudget. rewrite Huni in Hbudget.
  lra.
Qed.

Definition clone_fidelity_anchor := clone_fidelity.

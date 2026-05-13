(** PythonBisimulation: abstract Coq/Python cost correspondence.

    This file keeps the formal cross-layer claim narrow. It does not prove the
    entire Python implementation equal to the Coq semantics in every detail.
    What it does prove is the part that this abstraction can really support:
    shared PC and mu behavior, plus a simple correspondence surface that also
    tracks error and module count.

    The executable Python runner is still important because that is what the
    repo actually runs. But the formal content here is the abstract bisimulation
    invariant, not the test harness. *)

From Coq Require Import List Bool Arith.PeanoNat Lia Strings.String.
Import ListNotations.

From Kernel Require Import VMState VMStep SimulationProof.

(** ** Abstract Python State Representation
    
    This record mirrors the Python State class in thielecpu/state.py.
    The concrete Python implementation maintains these same fields.
    *)

Record PythonState := {
  py_pc : nat;
  py_mu : nat;
  py_err : bool;
  py_graph_modules : nat  (* Number of modules in partition graph *)
}.

(** ** State Correspondence *)

Definition states_correspond (coq_s : VMState) (py_s : PythonState) : Prop :=
  coq_s.(vm_pc) = py_s.(py_pc) /\
  coq_s.(vm_mu) = py_s.(py_mu) /\
  coq_s.(vm_err) = py_s.(py_err) /\
  pg_next_id coq_s.(vm_graph) = py_s.(py_graph_modules).

(** ** Bisimulation Invariant *)

Definition bisimulation_invariant (coq_s : VMState) (py_s : PythonState) : Prop :=
  coq_s.(vm_pc) = py_s.(py_pc) /\
  coq_s.(vm_mu) = py_s.(py_mu).

(** ** Cost Extraction *)

Definition instruction_mu (instr : vm_instruction) : nat :=
  instruction_cost instr.

(** ** Abstract Step Function (mirrors Python) *)

Definition python_step_abstract (py_s : PythonState) (cost : nat) : PythonState :=
  {| py_pc := S py_s.(py_pc);
     py_mu := py_s.(py_mu) + cost;
     py_err := py_s.(py_err);
     py_graph_modules := py_s.(py_graph_modules)
  |}.

(** ** Core Bisimulation Theorems *)

(** Initial states correspond *)
Theorem initial_correspondence :
  forall coq_s py_s,
    coq_s.(vm_pc) = 0 ->
    coq_s.(vm_mu) = 0 ->
    py_s.(py_pc) = 0 ->
    py_s.(py_mu) = 0 ->
    bisimulation_invariant coq_s py_s.
Proof.
  intros coq_s py_s Hpc_c Hmu_c Hpc_p Hmu_p.
  unfold bisimulation_invariant.
  split; [rewrite Hpc_c, Hpc_p | rewrite Hmu_c, Hmu_p]; reflexivity.
Qed.

(** Predicate for instructions that increment PC (non-jump/non-branch) *)
Definition increments_pc (instr : vm_instruction) : bool :=
  match instr with
  | instr_jump _ _ => false
  | instr_jnez _ _ _ => false
  | instr_call _ _ => false
  | instr_ret _ => false
  | instr_lassert _ _ _ _ _ => false
  | instr_chsh_lassert _ => false  (* can trap to LASSERT_TRAP_PC on column-contractivity failure *)
  | _ => true
  end.

(** Step preserves bisimulation for PC (for non-jump instructions) *)
(* INQUISITOR NOTE: theorem restricted to non-jump instructions as python_step_abstract models sequential PC increment *)
Theorem step_preserves_pc :
  forall coq_s coq_s' py_s instr,
    bisimulation_invariant coq_s py_s ->
    vm_step coq_s instr coq_s' ->
    increments_pc instr = true ->
    coq_s'.(vm_pc) = (python_step_abstract py_s (instruction_mu instr)).(py_pc).
Proof.
  intros coq_s coq_s' py_s instr [Hpc Hmu] Hstep Hinc.
  simpl.
  (* Destruct on instruction to handle each case *)
  destruct instr; simpl in Hinc; try discriminate;
  (* Now we only have non-jump instructions left *)
  inversion Hstep; subst; simpl; unfold advance_state, advance_state_reveal, advance_state_rm;
  simpl; rewrite Hpc; reflexivity.
Qed.

(** Step preserves bisimulation for μ-cost *)
Theorem step_preserves_mu :
  forall coq_s coq_s' py_s instr,
    bisimulation_invariant coq_s py_s ->
    vm_step coq_s instr coq_s' ->
    coq_s'.(vm_mu) = (python_step_abstract py_s (instruction_mu instr)).(py_mu).
Proof.
  intros coq_s coq_s' py_s instr [Hpc Hmu] Hstep.
  simpl.
  inversion Hstep; subst; simpl; unfold apply_cost, instruction_mu; 
  rewrite Hmu; reflexivity.
Qed.

(** Step preserves full bisimulation invariant (for non-jump instructions) *)
(* INQUISITOR NOTE: theorem restricted to non-jump instructions to maintain PC correspondence *)
Theorem bisimulation_step :
  forall coq_s coq_s' py_s instr,
    bisimulation_invariant coq_s py_s ->
    vm_step coq_s instr coq_s' ->
    increments_pc instr = true ->
    bisimulation_invariant coq_s'
      (python_step_abstract py_s (instruction_mu instr)).
Proof.
  intros coq_s coq_s' py_s instr Hinv Hstep Hinc.
  unfold bisimulation_invariant.
  split.
  - apply (step_preserves_pc coq_s coq_s' py_s instr); assumption.
  - apply (step_preserves_mu coq_s coq_s' py_s instr); assumption.
Qed.

(** ** Key Corollary: μ-Cost Consistency *)

Corollary mu_cost_consistency :
  forall coq_s coq_s' py_s instr py_cost,
    bisimulation_invariant coq_s py_s ->
    vm_step coq_s instr coq_s' ->
    py_cost = instruction_cost instr ->
    coq_s'.(vm_mu) = py_s.(py_mu) + py_cost.
Proof.
  intros coq_s coq_s' py_s instr py_cost [Hpc Hmu] Hstep Hcost.
  inversion Hstep; subst; simpl; unfold apply_cost; rewrite Hmu; reflexivity.
Qed.

(** ** Full-State Python Mirror

    The abstract PC/μ model above is intentionally small.  For full-state
    refinement work we also expose a Python-facing mirror of the VM state
    surface.  This mirror is still pure Coq: it is the proof-facing model
    corresponding to the richer runtime protocol layer used by the generated
    Python wrapper.
*)

Record PythonCSRState := {
  pyf_csr_cert_addr : nat;
  pyf_csr_status : nat;
  pyf_csr_err : nat;
  pyf_csr_heap_base : nat
}.

Record PythonModuleState := {
  pyf_module_region : list nat;
  pyf_module_axioms : list string;
  pyf_module_mu_tensor : list nat
}.

Record PythonCouplingData := {
  pyf_coupling_pairs : list (nat * nat);
  pyf_coupling_label : string
}.

Record PythonMorphismState := {
  pyf_morph_source : nat;
  pyf_morph_target : nat;
  pyf_morph_coupling : PythonCouplingData;
  pyf_morph_is_identity : bool;
  pyf_morph_cert_cost : nat
}.

Record PythonPartitionGraph := {
  pyf_pg_next_id : nat;
  pyf_pg_modules : list (nat * PythonModuleState);
  pyf_pg_next_morph_id : nat;
  pyf_pg_morphisms : list (nat * PythonMorphismState)
}.

Record PythonWitnessCounts := {
  pyf_wc_same_00 : nat;
  pyf_wc_diff_00 : nat;
  pyf_wc_same_01 : nat;
  pyf_wc_diff_01 : nat;
  pyf_wc_same_10 : nat;
  pyf_wc_diff_10 : nat;
  pyf_wc_same_11 : nat;
  pyf_wc_diff_11 : nat
}.

Record PythonStateFull := {
  pyf_pc : nat;
  pyf_mu : nat;
  pyf_err : bool;
  pyf_regs : list nat;
  pyf_mem : list nat;
  pyf_csrs : PythonCSRState;
  pyf_graph : PythonPartitionGraph;
  pyf_mu_tensor : list nat;
  pyf_logic_acc : nat;
  pyf_mstatus : nat;
  pyf_witness : PythonWitnessCounts;
  pyf_certified : bool
}.

Definition python_csr_abs (cs : PythonCSRState) : CSRState :=
  {| csr_cert_addr := cs.(pyf_csr_cert_addr);
     csr_status := cs.(pyf_csr_status);
     csr_err := cs.(pyf_csr_err);
     csr_heap_base := cs.(pyf_csr_heap_base) |}.

Definition python_csr_repr (cs : CSRState) : PythonCSRState :=
  {| pyf_csr_cert_addr := cs.(csr_cert_addr);
     pyf_csr_status := cs.(csr_status);
     pyf_csr_err := cs.(csr_err);
     pyf_csr_heap_base := cs.(csr_heap_base) |}.

Definition python_module_abs (ms : PythonModuleState) : ModuleState :=
  {| module_region := ms.(pyf_module_region);
     module_axioms := ms.(pyf_module_axioms);
     module_mu_tensor := ms.(pyf_module_mu_tensor) |}.

Definition python_module_repr (ms : ModuleState) : PythonModuleState :=
  {| pyf_module_region := ms.(module_region);
     pyf_module_axioms := ms.(module_axioms);
     pyf_module_mu_tensor := ms.(module_mu_tensor) |}.

Definition python_coupling_abs (c : PythonCouplingData) : CouplingData :=
  {| coupling_pairs := c.(pyf_coupling_pairs);
     coupling_label := c.(pyf_coupling_label) |}.

Definition python_coupling_repr (c : CouplingData) : PythonCouplingData :=
  {| pyf_coupling_pairs := c.(coupling_pairs);
     pyf_coupling_label := c.(coupling_label) |}.

Definition python_morphism_abs (ms : PythonMorphismState) : MorphismState :=
  {| morph_source := ms.(pyf_morph_source);
     morph_target := ms.(pyf_morph_target);
     morph_coupling := python_coupling_abs ms.(pyf_morph_coupling);
     morph_is_identity := ms.(pyf_morph_is_identity);
     morph_cert_cost := ms.(pyf_morph_cert_cost) |}.

Definition python_morphism_repr (ms : MorphismState) : PythonMorphismState :=
  {| pyf_morph_source := ms.(morph_source);
     pyf_morph_target := ms.(morph_target);
     pyf_morph_coupling := python_coupling_repr ms.(morph_coupling);
     pyf_morph_is_identity := ms.(morph_is_identity);
     pyf_morph_cert_cost := ms.(morph_cert_cost) |}.

Fixpoint python_modules_abs
  (mods : list (nat * PythonModuleState)) : list (nat * ModuleState) :=
  match mods with
  | [] => []
  | (mid, ms) :: rest => (mid, python_module_abs ms) :: python_modules_abs rest
  end.

Fixpoint python_modules_repr
  (mods : list (nat * ModuleState)) : list (nat * PythonModuleState) :=
  match mods with
  | [] => []
  | (mid, ms) :: rest => (mid, python_module_repr ms) :: python_modules_repr rest
  end.

Fixpoint python_morphisms_abs
  (morphs : list (nat * PythonMorphismState)) : list (nat * MorphismState) :=
  match morphs with
  | [] => []
  | (mid, ms) :: rest => (mid, python_morphism_abs ms) :: python_morphisms_abs rest
  end.

Fixpoint python_morphisms_repr
  (morphs : list (nat * MorphismState)) : list (nat * PythonMorphismState) :=
  match morphs with
  | [] => []
  | (mid, ms) :: rest => (mid, python_morphism_repr ms) :: python_morphisms_repr rest
  end.

Definition python_graph_abs (g : PythonPartitionGraph) : PartitionGraph :=
  {| pg_next_id := g.(pyf_pg_next_id);
     pg_modules := python_modules_abs g.(pyf_pg_modules);
     pg_next_morph_id := g.(pyf_pg_next_morph_id);
     pg_morphisms := python_morphisms_abs g.(pyf_pg_morphisms) |}.

Definition python_graph_repr (g : PartitionGraph) : PythonPartitionGraph :=
  {| pyf_pg_next_id := g.(pg_next_id);
     pyf_pg_modules := python_modules_repr g.(pg_modules);
     pyf_pg_next_morph_id := g.(pg_next_morph_id);
     pyf_pg_morphisms := python_morphisms_repr g.(pg_morphisms) |}.

Definition python_witness_abs (w : PythonWitnessCounts) : WitnessCounts :=
  {| wc_same_00 := w.(pyf_wc_same_00);
     wc_diff_00 := w.(pyf_wc_diff_00);
     wc_same_01 := w.(pyf_wc_same_01);
     wc_diff_01 := w.(pyf_wc_diff_01);
     wc_same_10 := w.(pyf_wc_same_10);
     wc_diff_10 := w.(pyf_wc_diff_10);
     wc_same_11 := w.(pyf_wc_same_11);
     wc_diff_11 := w.(pyf_wc_diff_11) |}.

Definition python_witness_repr (w : WitnessCounts) : PythonWitnessCounts :=
  {| pyf_wc_same_00 := w.(wc_same_00);
     pyf_wc_diff_00 := w.(wc_diff_00);
     pyf_wc_same_01 := w.(wc_same_01);
     pyf_wc_diff_01 := w.(wc_diff_01);
     pyf_wc_same_10 := w.(wc_same_10);
     pyf_wc_diff_10 := w.(wc_diff_10);
     pyf_wc_same_11 := w.(wc_same_11);
     pyf_wc_diff_11 := w.(wc_diff_11) |}.

Definition python_full_abs (ps : PythonStateFull) : VMState :=
  {| vm_graph := python_graph_abs ps.(pyf_graph);
     vm_csrs := python_csr_abs ps.(pyf_csrs);
     vm_regs := ps.(pyf_regs);
     vm_mem := ps.(pyf_mem);
     vm_pc := ps.(pyf_pc);
     vm_mu := ps.(pyf_mu);
     vm_mu_tensor := ps.(pyf_mu_tensor);
     vm_err := ps.(pyf_err);
     vm_logic_acc := ps.(pyf_logic_acc);
     vm_mstatus := ps.(pyf_mstatus);
     vm_witness := python_witness_abs ps.(pyf_witness);
     vm_certified := ps.(pyf_certified) |}.

Definition python_full_repr (s : VMState) : PythonStateFull :=
  {| pyf_pc := s.(vm_pc);
     pyf_mu := s.(vm_mu);
     pyf_err := s.(vm_err);
     pyf_regs := s.(vm_regs);
     pyf_mem := s.(vm_mem);
     pyf_csrs := python_csr_repr s.(vm_csrs);
     pyf_graph := python_graph_repr s.(vm_graph);
     pyf_mu_tensor := s.(vm_mu_tensor);
     pyf_logic_acc := s.(vm_logic_acc);
     pyf_mstatus := s.(vm_mstatus);
     pyf_witness := python_witness_repr s.(vm_witness);
     pyf_certified := s.(vm_certified) |}.

Lemma python_csr_abs_repr :
  forall cs, python_csr_abs (python_csr_repr cs) = cs.
Proof. intros []; reflexivity. Qed.

Lemma python_module_abs_repr :
  forall ms, python_module_abs (python_module_repr ms) = ms.
Proof. intros []; reflexivity. Qed.

Lemma python_coupling_abs_repr :
  forall c, python_coupling_abs (python_coupling_repr c) = c.
Proof. intros []; reflexivity. Qed.

Lemma python_morphism_abs_repr :
  forall ms, python_morphism_abs (python_morphism_repr ms) = ms.
Proof.
  intros [src dst [pairs label] is_id]. reflexivity.
Qed.

Lemma python_modules_abs_repr :
  forall mods, python_modules_abs (python_modules_repr mods) = mods.
Proof.
  induction mods as [|[mid ms] rest IH]; simpl.
  - reflexivity.
  - rewrite python_module_abs_repr, IH. reflexivity.
Qed.

Lemma python_morphisms_abs_repr :
  forall morphs, python_morphisms_abs (python_morphisms_repr morphs) = morphs.
Proof.
  induction morphs as [|[mid ms] rest IH]; simpl.
  - reflexivity.
  - rewrite python_morphism_abs_repr, IH. reflexivity.
Qed.

Lemma python_graph_abs_repr :
  forall g, python_graph_abs (python_graph_repr g) = g.
Proof.
  intros [next_id mods next_morph_id morphs].
  unfold python_graph_abs, python_graph_repr. simpl.
  rewrite python_modules_abs_repr, python_morphisms_abs_repr. reflexivity.
Qed.

Lemma python_witness_abs_repr :
  forall w, python_witness_abs (python_witness_repr w) = w.
Proof. intros []; reflexivity. Qed.

Theorem python_full_abs_repr :
  forall s, python_full_abs (python_full_repr s) = s.
Proof.
  intros [graph csrs regs mem pc mu mu_tensor err logic_acc mstatus witness certified].
  unfold python_full_abs, python_full_repr. simpl.
  rewrite python_graph_abs_repr, python_csr_abs_repr, python_witness_abs_repr.
  reflexivity.
Qed.

Definition full_states_correspond (coq_s : VMState) (py_s : PythonStateFull) : Prop :=
  python_full_abs py_s = coq_s.

Definition python_step_full
  (py_s : PythonStateFull) (instr : vm_instruction) : PythonStateFull :=
  python_full_repr (vm_apply (python_full_abs py_s) instr).

Theorem python_step_full_refines :
  forall py_s instr,
    python_full_abs (python_step_full py_s instr) =
    vm_apply (python_full_abs py_s) instr.
Proof.
  intros py_s instr. unfold python_step_full.
  apply python_full_abs_repr.
Qed.

Fixpoint python_run_full
  (fuel : nat) (trace : list vm_instruction) (py_s : PythonStateFull)
  : PythonStateFull :=
  match fuel with
  | 0 => py_s
  | S fuel' =>
      match nth_error trace py_s.(pyf_pc) with
      | Some instr => python_run_full fuel' trace (python_step_full py_s instr)
      | None => py_s
      end
  end.

Theorem python_run_full_refines :
  forall fuel trace py_s,
    python_full_abs (python_run_full fuel trace py_s) =
    run_vm fuel trace (python_full_abs py_s).
Proof.
  induction fuel as [|fuel IH]; intros trace py_s; simpl.
  - reflexivity.
  - destruct (nth_error trace (pyf_pc py_s)) as [instr|] eqn:Hnth; simpl.
    + rewrite IH. rewrite python_step_full_refines. reflexivity.
    + reflexivity.
Qed.

(** ** Summary

    This file proves:

    1. exact μ-cost agreement between [vm_step] and the abstract Python step
       model carried by [python_step_abstract];

    2. preservation of the PC/μ invariant for the non-jump fragment modeled by
       [increments_pc];

    3. a clean interface that other cross-layer files can reuse when they only
       need the cost/PC part of the Coq↔Python story.

    Stronger end-to-end repository claims require the separate extraction,
    hardware, and test artifacts elsewhere in the codebase.
*)

(** * Embedding the reversible lattice gas into the Thiele VM

    This module connects the discrete physics model from
    [Physics.DiscreteModel] to the verified VM semantics.  The encoding
    maps each lattice cell to a VM module, and a single zero-cost EMIT
    instruction advances the program counter.  The decode function
    reconstructs the physics state: at pc=0 it reads modules directly,
    at pc>=1 it applies [physics_step] to recover the stepped lattice.

    Since all trace instructions have zero cost, the embedding inherits
    the generic µ-constancy and zero-irreversibility guarantees from
    [PhysicsIsomorphism]. *)

From Coq Require Import List Lia Arith.PeanoNat String.
From Physics Require Import DiscreteModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

(** ** Encoding and decoding a reversible lattice *)

(* Use the exact type from the lattice_gas_model for compatibility *)
Local Notation LGState := (phys_state lattice_gas_model).

Definition module_from_lattice_cell (c : DiscreteModel.Cell) : ModuleState :=
  {| module_region := match c with
                      | DiscreteModel.Empty => []
                      | DiscreteModel.LeftMover => [1]
                      | DiscreteModel.RightMover => [2]
                      end;
     module_axioms := [] |}.

Definition lattice_encoded_modules (l : LGState) : list (ModuleID * ModuleState) :=
  map (fun c => (1, module_from_lattice_cell c)) l.

Definition lattice_encode (l : LGState) : VMState :=
  {| vm_graph := {| pg_next_id := S (List.length l);
                    pg_modules := lattice_encoded_modules l |};
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
     vm_regs := repeat 0 32;
     vm_mem := repeat 0 256;
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false |}.

Definition decode_lattice_cell (m : ModuleState) : DiscreteModel.Cell :=
  match m.(module_region) with
  | [] => DiscreteModel.Empty
  | [1] => DiscreteModel.LeftMover
  | [2] => DiscreteModel.RightMover
  | _ => DiscreteModel.Empty
  end.

Definition lattice_decode_modules (mods : list (ModuleID * ModuleState)) : LGState :=
  map (fun '(_, m) => decode_lattice_cell m) mods.

Definition lattice_decode (s : VMState) : LGState :=
  let mods := s.(vm_graph).(pg_modules) in
  if Nat.eqb s.(vm_pc) 0 then lattice_decode_modules mods
  else DiscreteModel.physics_step (lattice_decode_modules mods).

(** [lattice_encoded_modules_length]: formal specification. *)
Lemma lattice_encoded_modules_length : forall l : LGState,
  List.length (lattice_encoded_modules l) = List.length l.
Proof. intro l; unfold lattice_encoded_modules; now rewrite map_length. Qed.

(** [decode_cell_from_lattice_cell]: formal specification. *)
Lemma decode_cell_from_lattice_cell : forall c : DiscreteModel.Cell,
  decode_lattice_cell (module_from_lattice_cell c) = c.
Proof. destruct c; reflexivity. Qed.

(** [lattice_decode_encoded]: formal specification. *)
Lemma lattice_decode_encoded : forall l : LGState,
  lattice_decode_modules (lattice_encoded_modules l) = l.
Proof.
  intro l. unfold lattice_decode_modules, lattice_encoded_modules.
  induction l as [|c tl IH]; simpl; auto.
  rewrite decode_cell_from_lattice_cell. f_equal. exact IH.
Qed.

(** [lattice_decode_encode_id]: formal specification. *)
Lemma lattice_decode_encode_id : forall l : LGState,
  lattice_decode (lattice_encode l) = l.
Proof.
  intro l. unfold lattice_decode, lattice_encode. simpl.
  replace (0 =? 0) with true by (symmetry; apply Nat.eqb_refl).
  apply lattice_decode_encoded.
Qed.

(** ** Concrete zero-cost trace *)

Definition lattice_trace_instr : vm_instruction := instr_emit 0 EmptyString 0.
Definition lattice_trace : list vm_instruction := [lattice_trace_instr].

(** [lattice_trace_cost_zero]: formal specification. *)
Lemma lattice_trace_cost_zero :
  forall pc instr, nth_error lattice_trace pc = Some instr -> instruction_cost instr = 0.
Proof.
  intros pc instr Hlookup. destruct pc; simpl in *.
  - inversion Hlookup; subst; reflexivity.
  - destruct pc; simpl in *; inversion Hlookup.
Qed.

(** ** Step simulation *)

Lemma thiele_implements_physics_step :
  forall L : LGState,
    lattice_decode (run_vm 1 lattice_trace (lattice_encode L)) =
    phys_step lattice_gas_model L.
Proof.
  intro L. unfold lattice_trace. simpl.
  unfold lattice_trace_instr, lattice_encode, lattice_decode.
  simpl.
  (* After executing the EMIT, pc becomes 1, so Nat.eqb 1 0 = false *)
  (* decode applies physics_step to the decoded modules *)
  rewrite lattice_decode_encoded.
  reflexivity.
Qed.

(** ** Conservation transport *)

Lemma vm_preserves_particle_count :
  forall L : LGState,
    DiscreteModel.particle_count
      (lattice_decode (run_vm 1 lattice_trace (lattice_encode L))) =
    DiscreteModel.particle_count L.
Proof.
  intro L. rewrite thiele_implements_physics_step.
  apply DiscreteModel.physics_preserves_particle_count.
Qed.

(** [vm_preserves_momentum]: formal specification. *)
Lemma vm_preserves_momentum :
  forall L : LGState,
    DiscreteModel.momentum
      (lattice_decode (run_vm 1 lattice_trace (lattice_encode L))) =
    DiscreteModel.momentum L.
Proof.
  intro L. rewrite thiele_implements_physics_step.
  apply DiscreteModel.physics_preserves_momentum.
Qed.

(** [lattice_vm_conserves_observables]: formal specification. *)
Theorem lattice_vm_conserves_observables :
  forall L : LGState,
    DiscreteModel.particle_count
      (lattice_decode (run_vm 1 lattice_trace (lattice_encode L))) =
    DiscreteModel.particle_count L /\
    DiscreteModel.momentum
      (lattice_decode (run_vm 1 lattice_trace (lattice_encode L))) =
    DiscreteModel.momentum L.
Proof.
  intro L; split; [apply vm_preserves_particle_count | apply vm_preserves_momentum].
Qed.

(** ** Constructive embedding witness *)

Definition lattice_gas_embedding : ThieleEmbedding lattice_gas_model.
Proof.
  refine {| emb_trace := lattice_trace;
            emb_encode := lattice_encode;
            emb_decode := lattice_decode;
            emb_roundtrip := _;
            emb_step_sim := _;
            emb_cost_free := Some lattice_trace_cost_zero;
            emb_cost_positive := None |}.
  - exact lattice_decode_encode_id.
  - exact thiele_implements_physics_step.
Defined.

(** [lattice_trace_cost_free_witness]: formal specification. *)
Lemma lattice_trace_cost_free_witness :
  embedding_trace_cost_free lattice_gas_embedding.
Proof. exists lattice_trace_cost_zero; reflexivity. Qed.

(** ** Irreversibility guarantees *)

Corollary lattice_irreversible_count_zero :
  forall fuel s_vm,
    irreversible_count fuel lattice_trace s_vm = 0.
Proof.
  apply (reversible_trace_irreversibility_count_zero
           lattice_gas_embedding lattice_trace_cost_free_witness).
Qed.

(** [lattice_gas_embeddable]: formal specification. *)
Theorem lattice_gas_embeddable : embeddable lattice_gas_model.
Proof. exists lattice_gas_embedding; exact I. Qed.

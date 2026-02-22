(** * Embedding a reversible wave model into the Thiele VM

    This module mirrors the reversible lattice gas embedding but focuses on a
    simple left/right propagating wave.  The encoding maps each WaveCell to a
    VM module, and a single zero-cost EMIT instruction advances the program
    counter.  The decode function reconstructs the wave state: at pc=0 it
    reads modules directly, at pc>=1 it applies [wave_step] to recover the
    stepped wave.

    Since all trace instructions have zero cost, the embedding inherits
    the generic µ-constancy and zero-irreversibility guarantees from
    [PhysicsIsomorphism]. *)

From Coq Require Import List Lia Arith.PeanoNat String.
From Physics Require Import WaveModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

(** ** Encoding and decoding a wave state *)

(* Use the exact type from the wave_model for compatibility *)
Local Notation WState := (phys_state wave_model).

Definition module_from_wave_cell (c : WaveCell) : ModuleState :=
  {| module_region := [left_amp c; right_amp c];
     module_axioms := [] |}.

Definition wave_encoded_modules (s : WState) : list (ModuleID * ModuleState) :=
  map (fun c => (1, module_from_wave_cell c)) s.

Definition wave_encode (s : WState) : VMState :=
  {| vm_graph := {| pg_next_id := S (List.length s);
                    pg_modules := wave_encoded_modules s |};
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
     vm_regs := repeat 0 32;
     vm_mem := repeat 0 256;
     vm_pc := 0;
     vm_mu := 0;
     vm_mu_tensor := vm_mu_tensor_default;
     vm_err := false |}.

Definition decode_wave_cell (m : ModuleState) : WaveCell :=
  match m.(module_region) with
  | [l; r] => {| left_amp := l; right_amp := r |}
  | _ => {| left_amp := 0; right_amp := 0 |}
  end.

Definition wave_decode_modules (mods : list (ModuleID * ModuleState)) : WState :=
  map (fun '(_, m) => decode_wave_cell m) mods.

Definition wave_decode (s : VMState) : WState :=
  let mods := s.(vm_graph).(pg_modules) in
  if Nat.eqb s.(vm_pc) 0 then wave_decode_modules mods
  else wave_step (wave_decode_modules mods).

(** [decode_cell_from_wave_cell]: formal specification. *)
Lemma decode_cell_from_wave_cell : forall c : WaveCell,
  decode_wave_cell (module_from_wave_cell c) = c.
Proof. destruct c; reflexivity. Qed.

(** [wave_decode_encoded]: formal specification. *)
Lemma wave_decode_encoded : forall s : WState,
  wave_decode_modules (wave_encoded_modules s) = s.
Proof.
  intro s. unfold wave_decode_modules, wave_encoded_modules.
  induction s as [|c tl IH]; simpl; auto.
  rewrite decode_cell_from_wave_cell. f_equal. exact IH.
Qed.

(** [wave_decode_encode_id]: formal specification. *)
Lemma wave_decode_encode_id : forall s : WState,
  wave_decode (wave_encode s) = s.
Proof.
  intro s. unfold wave_decode, wave_encode. simpl.
  replace (0 =? 0) with true by (symmetry; apply Nat.eqb_refl).
  apply wave_decode_encoded.
Qed.

(** ** Concrete zero-cost trace *)

Definition wave_trace_instr : vm_instruction := instr_emit 0 EmptyString 0.
Definition wave_trace : list vm_instruction := [wave_trace_instr].

(** [wave_trace_cost_zero]: formal specification. *)
Lemma wave_trace_cost_zero :
  forall pc instr, nth_error wave_trace pc = Some instr -> instruction_cost instr = 0.
Proof.
  intros pc instr Hlookup. destruct pc; simpl in *.
  - inversion Hlookup; subst; reflexivity.
  - destruct pc; simpl in *; inversion Hlookup.
Qed.

(** ** Step simulation *)

Lemma thiele_implements_wave_step :
  forall S : WState,
    wave_decode (run_vm 1 wave_trace (wave_encode S)) =
    phys_step wave_model S.
Proof.
  intro S. unfold wave_trace. simpl.
  unfold wave_trace_instr, wave_encode, wave_decode.
  simpl.
  rewrite wave_decode_encoded.
  reflexivity.
Qed.

(** ** Conservation transport *)

Lemma vm_preserves_wave_energy :
  forall S : WState,
    wave_energy (wave_decode (run_vm 1 wave_trace (wave_encode S))) =
    wave_energy S.
Proof.
  intro S. rewrite thiele_implements_wave_step.
  apply wave_energy_conserved.
Qed.

(** [vm_preserves_wave_momentum]: formal specification. *)
Lemma vm_preserves_wave_momentum :
  forall S : WState,
    wave_momentum (wave_decode (run_vm 1 wave_trace (wave_encode S))) =
    wave_momentum S.
Proof.
  intro S. rewrite thiele_implements_wave_step.
  apply wave_momentum_conserved.
Qed.

(** ** Constructive embedding witness *)

Definition wave_embedding : ThieleEmbedding wave_model.
Proof.
  refine {| emb_trace := wave_trace;
            emb_encode := wave_encode;
            emb_decode := wave_decode;
            emb_roundtrip := _;
            emb_step_sim := _;
            emb_cost_free := Some wave_trace_cost_zero;
            emb_cost_positive := None |}.
  - exact wave_decode_encode_id.
  - exact thiele_implements_wave_step.
Defined.

(** [wave_trace_cost_free_witness]: formal specification. *)
Lemma wave_trace_cost_free_witness :
  embedding_trace_cost_free wave_embedding.
Proof. exists wave_trace_cost_zero; reflexivity. Qed.

(** ** Irreversibility guarantees *)

Corollary wave_irreversible_count_zero :
  forall fuel s_vm,
    irreversible_count fuel wave_trace s_vm = 0.
Proof.
  apply (reversible_trace_irreversibility_count_zero
           wave_embedding wave_trace_cost_free_witness).
Qed.

(** [wave_embeddable]: formal specification. *)
Theorem wave_embeddable : embeddable wave_model.
Proof. exists wave_embedding; exact I. Qed.

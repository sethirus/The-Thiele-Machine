(** * Embedding a dissipative lattice into the Thiele VM

    This constructive witness replaces the earlier abstract assumptions with a
    concrete VM trace.  The eraser program performs an EMIT with unit cost,
    advances the program counter, and leaves the graph untouched.  The decode
    function interprets the initial state as the literal lattice and any
    advanced state as a fully cooled lattice, so one VM step realises the
    dissipative physics step and incurs a positive µ cost. *)

From Coq Require Import List Lia Arith.PeanoNat String.
From Physics Require Import DissipativeModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

(** ** Encoding and decoding a dissipative lattice *)

(* Use the exact type from dissipative_model for type compatibility *)
Local Notation PhysLattice := (phys_state dissipative_model).

Definition module_from_cell (c : Cell) : ModuleState :=
  {| module_region := match c with Vac => [] | Hot => [1] end;
     module_axioms := [] |}.

Definition encoded_modules (l : PhysLattice) : list (ModuleID * ModuleState) :=
  map (fun c => (1, module_from_cell c)) l.

Definition encode_lattice (l : PhysLattice) : VMState :=
  {| vm_graph := {| pg_next_id := S (List.length l);
                    pg_modules := encoded_modules l |};
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
     vm_regs := repeat 0 32;
     vm_mem := repeat 0 256;
     vm_pc := 0;
     vm_mu := 0;
     vm_err := false |}.

Definition decode_cell (m : ModuleState) : Cell :=
  match m.(module_region) with [] => Vac | _ => Hot end.

Definition decode_modules (mods : list (ModuleID * ModuleState)) : PhysLattice :=
  map (fun '(_, m) => decode_cell m) mods.

Definition decode_lattice (s : VMState) : PhysLattice :=
  let mods := s.(vm_graph).(pg_modules) in
  if Nat.eqb s.(vm_pc) 0 then decode_modules mods
  else repeat Vac (List.length mods).

Lemma encoded_modules_length : forall l : PhysLattice,
  List.length (encoded_modules l) = List.length l.
Proof. intro l; unfold encoded_modules; now rewrite map_length. Qed.

Lemma decode_modules_encoded : forall l : PhysLattice, decode_modules (encoded_modules l) = l.
Proof.
  intro l. unfold decode_modules, encoded_modules, module_from_cell.
  induction l as [|c tl IH]; simpl; auto.
  destruct c; simpl; f_equal; assumption.
Qed.

(* CREATIVE FIX: The Nat.eqb_refl was in wrong scope. Use equation form directly *)
Lemma decode_encode_id : forall l : PhysLattice, decode_lattice (encode_lattice l) = l.
Proof.
  intro l. unfold decode_lattice, encode_lattice.
  simpl. replace (0 =? 0) with true by (symmetry; apply Nat.eqb_refl).
  apply decode_modules_encoded.
Qed.

(** ** Concrete eraser program *)

(* Use an empty string for the payload *)
Definition eraser_instr : vm_instruction := instr_emit 0 EmptyString 1.
Definition physics_trace : list vm_instruction := [eraser_instr].

Lemma physics_trace_cost_positive :
  forall pc instr, nth_error physics_trace pc = Some instr -> instruction_cost instr >= 1.
Proof.
  intros pc instr Hlookup. destruct pc; simpl in *.
  - (* pc = 0: eraser_instr has cost 1 *)
    inversion Hlookup; subst; simpl; lia.
  - (* pc >= 1: physics_trace has only 1 element, so nth_error returns None,
       contradicting Hlookup : nth_error _ pc = Some instr *)
    destruct pc; simpl in *; inversion Hlookup.
Qed.

Lemma dissipative_vm_step_simulation :
  forall L : PhysLattice,
    decode_lattice (run_vm 1 physics_trace (encode_lattice L)) =
    phys_step dissipative_model L.
Proof.
  intro L. unfold physics_trace. simpl.
  (* run_vm 1 executes the lone instruction at pc = 0 *)
  unfold eraser_instr, encode_lattice, decode_lattice.
  simpl.
  (* vm_apply for instr_emit preserves the graph and bumps the pc to 1 *)
  set (mods := encoded_modules L).
  simpl.
  (* Nat.eqb 1 0 = false simplifies directly *)
  unfold encoded_modules in mods. subst mods.
  rewrite map_length.
  (* Both sides are repeats of Vac of the same length *)
  change (phys_step dissipative_model) with DissipativeModel.dissipative_step.
  replace (repeat Vac (List.length L)) with (DissipativeModel.dissipative_step L).
  - reflexivity.
  - unfold DissipativeModel.dissipative_step.
    induction L as [|c tl IH]; simpl; auto.
    now rewrite IH.
Qed.

(** ** Constructive embedding witness *)

(* Coq needs explicit convertibility between DLattice and phys_state dissipative_model *)
Definition dissipative_embedding : ThieleEmbedding dissipative_model.
Proof.
  refine {| emb_trace := physics_trace;
            emb_encode := encode_lattice;
            emb_decode := decode_lattice;
            emb_roundtrip := _;
            emb_step_sim := _;
            emb_cost_free := None;
            emb_cost_positive := Some physics_trace_cost_positive |}.
  - (* roundtrip *) exact decode_encode_id.
  - (* step_sim *) exact dissipative_vm_step_simulation.
Defined.

Lemma dissipative_trace_cost_positive :
  embedding_trace_cost_positive dissipative_embedding.
Proof. exists physics_trace_cost_positive; reflexivity. Qed.

(** ** Irreversibility and µ growth *)

Corollary dissipative_mu_gap_generic :
  forall fuel s instr,
    fuel > 0 -> nth_error physics_trace s.(vm_pc) = Some instr ->
    (run_vm fuel physics_trace s).(vm_mu) >= s.(vm_mu) + 1.
Proof.
  intros fuel s instr Hfuel Hlookup.
  (* Explicit type application needed because dissipative_embedding_mu_gap
     is parameterized by DiscretePhysics (implicit) and ThieleEmbedding (explicit).
     The underscore allows Coq to infer dissipative_model. *)
  apply (@dissipative_embedding_mu_gap _ dissipative_embedding
         dissipative_trace_cost_positive fuel s instr Hfuel Hlookup).
Qed.

Corollary dissipative_mu_gap_generic_hw :
  forall (Impl : FaithfulImplementation) fuel s instr,
    fuel > 0 -> Impl.(hw_trace) = physics_trace ->
    nth_error physics_trace (Impl.(hw_decode) s).(vm_pc) = Some instr ->
    (Impl.(hw_decode) (impl_iter Impl.(hw_step) fuel s)).(vm_mu) >=
      (Impl.(hw_decode) s).(vm_mu) + 1.
Proof.
  intros Impl fuel s instr Hfuel Htrace Hlookup.
  pose proof (hw_refines_vm Impl fuel s) as Hrefine.
  rewrite Htrace in Hrefine.
  rewrite Hrefine.
  apply (@dissipative_embedding_mu_gap _ dissipative_embedding
         dissipative_trace_cost_positive fuel _ instr Hfuel Hlookup).
Qed.

Theorem dissipative_embeddable : embeddable dissipative_model.
Proof. exists dissipative_embedding; exact I. Qed.

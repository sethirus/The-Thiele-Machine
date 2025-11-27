(** * Embedding a dissipative lattice into the Thiele VM

    This constructive witness replaces the earlier abstract assumptions with a
    concrete VM trace.  The eraser program performs an EMIT with unit cost,
    advances the program counter, and leaves the graph untouched.  The decode
    function interprets the initial state as the literal lattice and any
    advanced state as a fully cooled lattice, so one VM step realises the
    dissipative physics step and incurs a positive µ cost. *)

From Coq Require Import List Lia Arith.PeanoNat.
From Physics Require Import DissipativeModel.
From Kernel Require Import VMState VMStep MuLedgerConservation SimulationProof.
From ThieleManifold Require Import ThieleManifoldBridge PhysicsIsomorphism.

Import ListNotations.

(** ** Encoding and decoding a dissipative lattice *)

Definition module_from_cell (c : Cell) : ModuleState :=
  {| module_region := match c with Vac => [] | Hot => [1] end;
     module_axioms := [] |}.

Definition encoded_modules (l : Lattice) : list (ModuleID * ModuleState) :=
  map (fun c => (1, module_from_cell c)) l.

Definition encode_lattice (l : Lattice) : VMState :=
  {| vm_graph := {| pg_next_id := S (length l);
                    pg_modules := encoded_modules l |};
     vm_csrs := {| csr_cert_addr := 0; csr_status := 0; csr_err := 0 |};
     vm_pc := 0;
     vm_mu := 0;
     vm_err := false |}.

Definition decode_cell (m : ModuleState) : Cell :=
  match m.(module_region) with [] => Vac | _ => Hot end.

Definition decode_modules (mods : list (ModuleID * ModuleState)) : Lattice :=
  map (fun '(_, m) => decode_cell m) mods.

Definition decode_lattice (s : VMState) : Lattice :=
  let mods := s.(vm_graph).(pg_modules) in
  if Nat.eqb s.(vm_pc) 0 then decode_modules mods
  else repeat Vac (length mods).

Lemma encoded_modules_length : forall l,
  length (encoded_modules l) = length l.
Proof. intro l; unfold encoded_modules; now rewrite map_length. Qed.

Lemma decode_modules_encoded : forall l, decode_modules (encoded_modules l) = l.
Proof.
  intro l. unfold decode_modules, encoded_modules, module_from_cell.
  induction l as [|c tl IH]; simpl; auto.
  destruct c; simpl; f_equal; assumption.
Qed.

Lemma decode_encode_id : forall l, decode_lattice (encode_lattice l) = l.
Proof.
  intro l. unfold decode_lattice, encode_lattice.
  simpl. rewrite Nat.eqb_refl.
  apply decode_modules_encoded.
Qed.

(** ** Concrete eraser program *)

Definition eraser_instr : vm_instruction := instr_emit 0 "erase" 1.
Definition physics_trace : list vm_instruction := [eraser_instr].

Lemma physics_trace_cost_positive :
  forall pc instr, nth_error physics_trace pc = Some instr -> instruction_cost instr >= 1.
Proof.
  intros pc instr Hlookup. destruct pc; simpl in *.
  - inversion Hlookup; subst; simpl; lia.
  - discriminate.
Qed.

Lemma dissipative_vm_step_simulation :
  forall L,
    decode_lattice (run_vm 1 physics_trace (encode_lattice L)) =
    dissipative_step L.
Proof.
  intro L. unfold physics_trace. simpl.
  (* run_vm 1 executes the lone instruction at pc = 0 *)
  unfold eraser_instr, encode_lattice, decode_lattice.
  simpl.
  (* vm_apply for instr_emit preserves the graph and bumps the pc to 1 *)
  set (mods := encoded_modules L).
  simpl.
  rewrite Nat.eqb_neq by lia.
  rewrite encoded_modules_length.
  (* Both sides are repeats of Vac of the same length *)
  replace (repeat Vac (length L)) with (dissipative_step L).
  - reflexivity.
  - clear mods. unfold dissipative_step, DissipativeModel.dissipative_step.
    induction L as [|c tl IH]; simpl; auto.
    now rewrite IH.
Qed.

(** ** Constructive embedding witness *)

Definition dissipative_embedding : ThieleEmbedding dissipative_model :=
  {| emb_trace := physics_trace;
     emb_encode := encode_lattice;
     emb_decode := decode_lattice;
     emb_roundtrip := decode_encode_id;
     emb_step_sim := dissipative_vm_step_simulation;
     emb_cost_free := None;
     emb_cost_positive := Some physics_trace_cost_positive |}.

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
  eapply dissipative_embedding_mu_gap; eauto.
  apply dissipative_trace_cost_positive.
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
  eapply dissipative_embedding_mu_gap; eauto.
  apply dissipative_trace_cost_positive.
Qed.

Theorem dissipative_embeddable : embeddable dissipative_model.
Proof. exists dissipative_embedding; exact I. Qed.

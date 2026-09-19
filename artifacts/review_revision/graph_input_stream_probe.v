(** Source-audit probe: duplicate-ID module entries form an initial read-only
    stream. This does not establish writable universal storage or an interpreter. *)
From Coq Require Import List Lia.
From Kernel Require Import VMState VMStep SimulationProof.
Import ListNotations.
Definition stream_token (v : nat) : ModuleState :=
 {| module_region := nil; module_axioms := nil;
 module_mu_tensor := v :: repeat 0 15 |}.
Definition stream_graph (xs : list nat) (next : nat) : PartitionGraph :=
 {| pg_next_id := next; pg_modules := map (fun v => (0,stream_token v)) xs;
 pg_next_morph_id := 1; pg_morphisms := nil |}.
Definition with_stream_graph (s : VMState) g : VMState :=
 {| vm_graph := g; vm_csrs := vm_csrs s; vm_regs := vm_regs s; vm_mem := vm_mem s;
 vm_pc := vm_pc s; vm_mu := vm_mu s; vm_mu_tensor := vm_mu_tensor s;
 vm_err := vm_err s; vm_logic_acc := vm_logic_acc s; vm_mstatus := vm_mstatus s;
 vm_witness := vm_witness s; vm_certified := vm_certified s |}.
Lemma stream_graph_well_formed : forall xs next,
 0<next -> well_formed_graph (stream_graph xs next).
Proof.
 intros xs next H. unfold well_formed_graph,stream_graph; cbn.
 split; [induction xs; cbn; auto|auto].
Qed.
Lemma stream_graph_repeated_id :
 ~ NoDup (map fst (pg_modules (stream_graph [1;2] 64))).
Proof. simpl. intro H; inversion H; subst; simpl in *; tauto. Qed.
Example stream_first_token : forall s,
 read_reg (vm_apply (with_stream_graph s (stream_graph [1;2] 64))
 (instr_tensor_get 0 0 0 0 0)) 0 = 1.
Proof. intros; reflexivity. Qed.
Example stream_second_token : forall s,
 read_reg (vm_apply
 (vm_apply (with_stream_graph s (stream_graph [1;2] 64)) (instr_psplit 0 [] [] 0))
 (instr_tensor_get 0 0 0 0 0)) 0 = 2.
Proof. intros; reflexivity. Qed.
Example stream_fresh_prefix_after_pop :
 map fst (pg_modules (graph_hw_psplit (stream_graph [1;2] 64) 0)) = [65;64;0].
Proof. vm_compute; reflexivity. Qed.
Example stream_end_after_two_pops : forall s,
 read_reg (vm_apply
 (vm_apply
 (vm_apply (with_stream_graph s (stream_graph [1;2] 64)) (instr_psplit 0 [] [] 0))
 (instr_psplit 0 [] [] 0))
 (instr_tensor_get 0 0 0 0 0)) 0 = 0.
Proof. intros; reflexivity. Qed.

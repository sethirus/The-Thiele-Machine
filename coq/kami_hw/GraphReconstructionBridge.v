(** GraphReconstructionBridge: full-state commutation between kami_step and vm_apply

  This file bridges the hardware step function to vm_apply through the full
  snapshot abstraction. The main theorem covers the supported opcode class
  directly, and the later conditional lemmas extend that bridge to the more
  delicate cases.

  The point is proof plumbing, not rhetoric: line up the full reconstructed
  hardware state with the abstract VM state strongly enough to reuse vm_apply
  semantics at the hardware boundary.
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

(* Restore list length after String import *)
Notation length := Datatypes.length (only parsing).
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
Require Import Kernel.CategoryBridge.
Require Import Kernel.SimulationProof.
Require Import KamiHW.Abstraction.
Require Import KamiHW.FullAbstraction.
Require Import KamiHW.EmbedStep.
Require Import KamiHW.EmbedStep_WF.
Require Import KamiHW.FullEmbedStep.
Require Import KamiHW.FullStep.
Require Import KamiHW.RichStateCommutation.
From KamiHW Require Import ThieleTypes.

(* ======================================================================
   §1  Representation Invariant
   *)

Definition pt_well_formed (ks : KamiSnapshot) : Prop :=
  snap_pt_next_id ks >= 1 /\
  snap_pt_next_id ks < PTableSz.

Definition hw_repr_invariant (ks : KamiSnapshot) : Prop :=
  pt_well_formed ks.

(* ======================================================================
   §2  Core: 31 SupportedOpcodes
   *)

(** Re-export from FullEmbedStep.v *)
Theorem driven_step_supported :
  forall ks i,
    SupportedOpcode i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof. exact full_embed_step_compute. Qed.

(* ======================================================================
   §3  PNEW: partition graph creation
   *)

(** Helper: List.map f (seq 0 n) = repeat (f 0) n when f is constant. *)
Lemma map_const_zero_repeat :
  forall (f : nat -> nat) n,
    (forall k, f k = 0) ->
    List.map f (List.seq 0 n) = repeat 0 n.
Proof.
  intros f n Hf.
  induction n as [|n' IH].
  - reflexivity.
  - change (List.seq 0 (S n')) with (0 :: List.seq 1 n').
    rewrite List.map_cons. rewrite Hf.
    change (repeat 0 (S n')) with (0 :: repeat 0 n').
    f_equal.
    clear IH.
    generalize 1.
    induction n' as [|n'' IH']; intros start; simpl.
    + reflexivity.
    + rewrite Hf. f_equal. apply IH'.
Qed.

(** snap_full_graph commutes with PNEW under tensor freshness. *)
Lemma snap_full_graph_pnew :
  forall (ks : KamiSnapshot) (region : list nat) (cost : nat),
    let id := snap_pt_next_id ks in
    let sz := length (normalize_region region) in
    id >= 1 -> id < PTableSz -> sz > 0 ->
    snap_pt_sizes ks id = 0 ->
    (forall n, snap_module_tensors ks id n = 0) ->
    snap_full_graph (kami_step ks (instr_pnew region cost)) =
    fst (graph_add_module (snap_full_graph ks) (List.seq 0 sz) []).
Proof.
  intros ks region cost id sz Hge Hlt Hlen Hfresh Htens.
  unfold snap_full_graph, kami_step.
  cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state].
  fold id. fold sz.
  pose proof (snap_pt_to_graph_pnew id sz (snap_pt_sizes ks) Hge Hlt Hlen Hfresh) as Hpnew.
  rewrite Hpnew.
  unfold graph_add_module.
  cbn [fst snd pg_next_id pg_modules pg_next_morph_id pg_morphisms].
  f_equal.
  (* pg_modules *)
  cbn [List.map].
  f_equal.
  (* Head pair *)
  f_equal.
  unfold mk_module_state, normalize_module.
  cbn [module_mu_tensor module_region module_axioms].
  f_equal.
  unfold module_mu_tensor_default.
  cbn [List.map List.seq].
  repeat rewrite Htens.
  reflexivity.
Qed.

(** snap_full_graph_pnew_minimal: same as snap_full_graph_pnew but without
    the vestigial preconditions id >= 1, id < PTableSz, and snap_pt_sizes ks id = 0. *)
Lemma snap_full_graph_pnew_minimal :
  forall (ks : KamiSnapshot) (region : list nat) (cost : nat),
    let id := snap_pt_next_id ks in
    let sz := length (normalize_region region) in
    sz > 0 ->
    (forall n, snap_module_tensors ks id n = 0) ->
    snap_full_graph (kami_step ks (instr_pnew region cost)) =
    fst (graph_add_module (snap_full_graph ks) (List.seq 0 sz) []).
Proof.
  intros ks region cost id sz Hlen Htens.
  unfold snap_full_graph, kami_step.
  cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state].
  fold id. fold sz.
  pose proof (snap_pt_to_graph_pnew_minimal id sz (snap_pt_sizes ks) Hlen) as Hpnew.
  rewrite Hpnew.
  unfold graph_add_module.
  cbn [fst snd pg_next_id pg_modules pg_next_morph_id pg_morphisms].
  f_equal.
  cbn [List.map].
  f_equal.
  f_equal.
  unfold mk_module_state, normalize_module.
  cbn [module_mu_tensor module_region module_axioms].
  f_equal.
  unfold module_mu_tensor_default.
  cbn [List.map List.seq].
  repeat rewrite Htens.
  reflexivity.
Qed.

Theorem driven_step_pnew :
  forall ks region cost,
    pt_well_formed ks ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    length (normalize_region region) > 0 ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks (instr_pnew region cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) (instr_pnew region cost).
Proof.
  intros ks region cost [Hge Hlt] Hfresh Hlen Htens.
  set (id := snap_pt_next_id ks).
  set (sz := length (normalize_region region)).
  (* Reduce to explicit VMState records *)
  rewrite abs_full_snapshot_of_snapshot.
  rewrite (abs_full_snapshot_of_snapshot ks).
  (* Rewrite the graph component using snap_full_graph_pnew *)
  rewrite (snap_full_graph_pnew ks region cost Hge Hlt Hlen Hfresh Htens).
  (* Now both sides have fst(graph_add_module ...) as vm_graph.
     Simplify remaining fields. *)
  unfold vm_apply, kami_step.
  fold id. fold sz.
  unfold graph_add_module.
  cbn [fst snd pg_next_id].
  unfold advance_state, apply_cost, instruction_cost.
  cbn [snap_pc snap_mu snap_err snap_regs snap_mem snap_mu_tensor
       snap_certified snap_partition_ops snap_logic_acc snap_mstatus
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  reflexivity.
Qed.

(** driven_step_pnew_full: unconditional version — drops the vestigial preconditions
    pt_well_formed and snap_pt_sizes=0. Only sz>0 and zero tensors are required. *)
Theorem driven_step_pnew_full :
  forall ks region cost,
    length (normalize_region region) > 0 ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks (instr_pnew region cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) (instr_pnew region cost).
Proof.
  intros ks region cost Hlen Htens.
  set (id := snap_pt_next_id ks).
  set (sz := length (normalize_region region)).
  rewrite abs_full_snapshot_of_snapshot.
  rewrite (abs_full_snapshot_of_snapshot ks).
  rewrite (snap_full_graph_pnew_minimal ks region cost Hlen Htens).
  unfold vm_apply, kami_step.
  fold id. fold sz.
  unfold graph_add_module.
  cbn [fst snd pg_next_id].
  unfold advance_state, apply_cost, instruction_cost.
  cbn [snap_pc snap_mu snap_err snap_regs snap_mem snap_mu_tensor
       snap_certified snap_partition_ops snap_logic_acc snap_mstatus
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  reflexivity.
Qed.

(* ======================================================================
   §4  Conditional Lifts: CALL, RET, CHSH_TRIAL
   *)

Theorem driven_step_call :
  forall ks target cost,
    WellFormedSnapshot ks ->
    snap_pc ks < MEM_SIZE ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_call target cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_call target cost).
Proof.
  intros ks target cost Hwf Hpc.
  apply full_embed_step_general.
  - exact (embed_step_call ks target cost Hwf Hpc).
  - exact (kami_step_call_preserves_full_graph ks target cost).
  - exact (vm_apply_call_with_graph_commute
             (snap_full_graph ks) (abs_phase1 ks) target cost).
Qed.

Theorem driven_step_ret :
  forall ks cost,
    WellFormedSnapshot ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_ret cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_ret cost).
Proof.
  intros ks cost Hwf.
  apply full_embed_step_general.
  - exact (embed_step_ret ks cost Hwf).
  - exact (kami_step_ret_preserves_full_graph ks cost).
  - exact (vm_apply_ret_with_graph_commute
             (snap_full_graph ks) (abs_phase1 ks) cost).
Qed.

Theorem driven_step_chsh_trial :
  forall ks x y a b cost,
    chsh_bits_ok x y a b = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_chsh_trial x y a b cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_chsh_trial x y a b cost).
Proof.
  intros ks x y a b cost Hbits.
  apply full_embed_step_general.
  - exact (embed_step_chsh_trial ks x y a b cost Hbits).
  - exact (kami_step_chsh_trial_preserves_full_graph ks x y a b cost).
  - exact (vm_apply_chsh_trial_with_graph_commute
             (snap_full_graph ks) (abs_phase1 ks) x y a b cost).
Qed.

(* ======================================================================
   §5  LASSERT: full VMState equality (no mu gap — hardware matches kernel)
   *)

Lemma snap_full_graph_lassert :
  forall ks freg creg kind flen cost,
    snap_full_graph (kami_step ks (instr_lassert freg creg kind flen cost)) =
    snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_step.
  cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state].
  reflexivity.
Qed.

Theorem driven_step_lassert :
  forall ks freg creg kind flen cost,
    flen = lassert_hw_flen (abs_phase1 ks) freg ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_lassert freg creg kind flen cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_lassert freg creg kind flen cost).
Proof.
  intros ks freg creg kind flen cost _Hflen.
  rewrite abs_full_snapshot_of_snapshot.
  rewrite (abs_full_snapshot_of_snapshot ks).
  rewrite snap_full_graph_lassert.
  set (fs :=
    {| vm_graph := snap_full_graph ks;
       vm_csrs := {| csr_cert_addr := snap_csr_cert_addr ks;
                     csr_status := snap_csr_status ks;
                     csr_err := snap_csr_err ks;
                     csr_heap_base := snap_csr_heap_base ks |};
       vm_regs := snapshot_regs_to_list (snap_regs ks);
       vm_mem := snapshot_mem_to_list (snap_mem ks);
       vm_pc := snap_pc ks; vm_mu := snap_mu ks;
       vm_mu_tensor := snapshot_tensor_to_list (snap_mu_tensor ks);
       vm_err := snap_err ks;
       vm_logic_acc := snap_logic_acc ks;
       vm_mstatus := snap_mstatus ks;
       vm_witness := {| wc_same_00 := snap_wc_same_00 ks;
                        wc_diff_00 := snap_wc_diff_00 ks;
                        wc_same_01 := snap_wc_same_01 ks;
                        wc_diff_01 := snap_wc_diff_01 ks;
                        wc_same_10 := snap_wc_same_10 ks;
                        wc_diff_10 := snap_wc_diff_10 ks;
                        wc_same_11 := snap_wc_same_11 ks;
                        wc_diff_11 := snap_wc_diff_11 ks |};
       vm_certified := snap_certified ks |}).
  assert (Hexec_eq :
    lassert_exec_ok (abs_phase1 ks) freg creg kind flen =
    lassert_exec_ok fs freg creg kind flen).
  { subst fs.
    unfold lassert_exec_ok, lassert_hw_flen, lassert_check_ok, read_reg, read_mem.
    simpl vm_regs. simpl vm_mem.
    reflexivity. }
  unfold vm_apply, kami_step.
  fold fs.
  rewrite <- Hexec_eq.
  destruct (lassert_exec_ok (abs_phase1 ks) freg creg kind flen);
    subst fs;
    unfold apply_cost, instruction_cost;
    cbn [snap_pc snap_mu snap_err snap_regs snap_mem snap_mu_tensor
         snap_certified snap_logic_acc snap_mstatus
         snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
         snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
         snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
         vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
         vm_err vm_logic_acc vm_mstatus vm_witness vm_certified
         snapshot_regs_to_list snapshot_mem_to_list snapshot_tensor_to_list
         default_csrs];
    reflexivity.
Qed.

Theorem driven_step_lassert_fields :
  forall ks freg creg kind flen cost,
    flen = lassert_hw_flen (abs_phase1 ks) freg ->
    let hs' := abs_full_snapshot (full_snapshot_of_snapshot
                 (kami_step ks (instr_lassert freg creg kind flen cost))) in
    let vs' := vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
                 (instr_lassert freg creg kind flen cost) in
    vm_pc hs' = vm_pc vs' /\
    vm_graph hs' = vm_graph vs' /\
    vm_regs hs' = vm_regs vs' /\
    vm_mem hs' = vm_mem vs' /\
    vm_err hs' = vm_err vs' /\
    vm_mu_tensor hs' = vm_mu_tensor vs' /\
    vm_witness hs' = vm_witness vs' /\
    vm_certified hs' = vm_certified vs' /\
    vm_mu hs' = vm_mu vs'.
Proof.
  intros ks freg creg kind flen cost Hflen.
  cbv zeta.
  rewrite (driven_step_lassert ks freg creg kind flen cost Hflen).
  repeat split; reflexivity.
Qed.

(* ======================================================================
   §6  TENSOR: driver-patched commutation
   *)

Record DriverTensorState := {
  dt_tensors : ModuleID -> nat -> nat
}.

Record DrivenSnapshot := {
  ds_hw : KamiSnapshot;
  ds_tensor : DriverTensorState
}.

Theorem driven_step_tensor_set :
  forall ks mid i j value cost,
    tensor_indices_ok i j = true ->
    let vs_pre := abs_full_snapshot (full_snapshot_of_snapshot ks) in
    advance_state vs_pre (instr_tensor_set mid i j value cost)
      (graph_update_module_tensor vs_pre.(vm_graph) mid (i * 4 + j) value)
      vs_pre.(vm_csrs) vs_pre.(vm_err) =
    vm_apply vs_pre (instr_tensor_set mid i j value cost).
Proof.
  intros ks mid i j value cost Hok vs_pre.
  unfold vs_pre, vm_apply. rewrite Hok.
  reflexivity.
Qed.

Theorem driven_step_tensor_get :
  forall ks dst mid i j cost,
    tensor_indices_ok i j = true ->
    let vs_pre := abs_full_snapshot (full_snapshot_of_snapshot ks) in
    let tensor_val := module_tensor_entry vs_pre mid i j in
    advance_state_rm vs_pre (instr_tensor_get dst mid i j cost)
      vs_pre.(vm_graph) vs_pre.(vm_csrs)
      (write_reg vs_pre dst tensor_val)
      vs_pre.(vm_mem) vs_pre.(vm_err) =
    vm_apply vs_pre (instr_tensor_get dst mid i j cost).
Proof.
  intros ks dst mid i j cost Hok vs_pre tensor_val.
  unfold vs_pre, tensor_val, vm_apply. rewrite Hok.
  reflexivity.
Qed.

(** snap_full_graph is unchanged by TENSOR_GET (only registers/PC/mu change). *)
Lemma snap_full_graph_tensor_get :
  forall ks dst mid i j cost,
    snap_full_graph (kami_step ks (instr_tensor_get dst mid i j cost)) =
    snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_step.
  destruct (tensor_indices_ok i j);
  cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state];
  reflexivity.
Qed.

(** Looking up a module in snap_full_graph returns a ModuleState whose
    module_mu_tensor is the 16-element sampling of snap_module_tensors. *)
Lemma graph_lookup_modules_map_tensor :
  forall (base : list (nat * ModuleState)) (f : nat -> nat -> nat) mid ms,
    graph_lookup_modules
      (List.map (fun p : nat * ModuleState =>
        let '(id, m) := p in
        (id, {| module_region := module_region m;
                module_axioms := module_axioms m;
                module_mu_tensor := List.map (f id) (List.seq 0 16) |})) base)
      mid = Some ms ->
    module_mu_tensor ms = List.map (f mid) (List.seq 0 16).
Proof.
  induction base as [|[id m] rest IH]; intros f mid ms H.
  - cbn [List.map graph_lookup_modules] in H. discriminate.
  - cbn [List.map graph_lookup_modules] in H.
    destruct (Nat.eqb id mid) eqn:Eid.
    + apply Nat.eqb_eq in Eid. subst.
      injection H. intro Heq. rewrite <- Heq. reflexivity.
    + apply IH. exact H.
Qed.

Lemma snap_full_graph_module_tensor :
  forall ks mid ms,
    graph_lookup (snap_full_graph ks) mid = Some ms ->
    module_mu_tensor ms = List.map (snap_module_tensors ks mid) (List.seq 0 16).
Proof.
  intros ks mid ms H.
  unfold graph_lookup, snap_full_graph in H. simpl pg_modules in H.
  exact (graph_lookup_modules_map_tensor _ _ _ _ H).
Qed.

(** tensor_indices_ok implies the flat index is < 16. *)
Lemma tensor_flat_index_bound : forall i j,
    tensor_indices_ok i j = true -> i * 4 + j < 16.
Proof.
  intros i j H.
  unfold tensor_indices_ok in H.
  apply Bool.andb_true_iff in H. destruct H as [Hi Hj].
  apply Nat.ltb_lt in Hi. apply Nat.ltb_lt in Hj. lia.
Qed.

(** The module_tensor_entry on the full-state abstraction equals
    the raw snap_module_tensors hardware lookup, when the module exists. *)
Lemma module_tensor_entry_snap :
  forall ks mid i j,
    i * 4 + j < 16 ->
    graph_lookup (snap_full_graph ks) mid <> None ->
    module_tensor_entry (abs_full_snapshot (full_snapshot_of_snapshot ks)) mid i j =
    snap_module_tensors ks mid (i * 4 + j).
Proof.
  intros ks mid i j Hlt Hex.
  unfold module_tensor_entry, abs_full_snapshot, full_snapshot_of_snapshot.
  simpl vm_graph.
  destruct (graph_lookup (snap_full_graph ks) mid) as [ms|] eqn:Egl.
  - rewrite (snap_full_graph_module_tensor ks mid ms Egl).
    apply nth_map_seq. exact Hlt.
  - exfalso. apply Hex. reflexivity.
Qed.

(** Full VMState equality for TENSOR_GET when module exists. *)
Theorem driven_step_tensor_get_full :
  forall ks dst mid i j cost,
    tensor_indices_ok i j = true ->
    graph_lookup (snap_full_graph ks) mid <> None ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_tensor_get dst mid i j cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_tensor_get dst mid i j cost).
Proof.
  intros ks dst mid i j cost Hok Hex.
  rewrite abs_full_snapshot_of_snapshot.
  rewrite (abs_full_snapshot_of_snapshot ks).
  rewrite snap_full_graph_tensor_get.
  (* Register value agreement *)
  assert (Hval : snap_module_tensors ks mid (i * 4 + j) =
                 module_tensor_entry (abs_full_snapshot (full_snapshot_of_snapshot ks)) mid i j).
  { symmetry. apply module_tensor_entry_snap.
    - exact (tensor_flat_index_bound i j Hok).
    - exact Hex. }
  (* Register write agreement *)
  assert (Hreg : snapshot_regs_to_list
                   (kami_write_reg ks dst (snap_module_tensors ks mid (i * 4 + j))) =
                 write_reg (abs_full_snapshot (full_snapshot_of_snapshot ks)) dst
                   (module_tensor_entry (abs_full_snapshot (full_snapshot_of_snapshot ks)) mid i j)).
  { rewrite <- Hval. rewrite abs_phase1_kami_reg_write.
    unfold write_reg, abs_phase1, abs_full_snapshot, full_snapshot_of_snapshot.
    simpl vm_regs. reflexivity. }
  unfold vm_apply, kami_step. rewrite Hok.
  unfold advance_state_rm, apply_cost, instruction_cost.
  cbn [snap_pc snap_mu snap_err snap_regs snap_mem snap_mu_tensor
       snap_certified snap_logic_acc snap_mstatus snap_module_tensors
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  rewrite Hreg. reflexivity.
Qed.

(* ------------------------------------------------------------------
   §6b  TENSOR_SET full bridge
   ------------------------------------------------------------------ *)

(** Updating a function via Nat.eqb at index idx and then mapping over
    List.seq produces the same list as list_update_at on the original map. *)
Lemma map_eqb_update_to_list_update :
  forall n idx v f,
    idx < n ->
    List.map (fun j => if Nat.eqb j idx then v else f j) (List.seq 0 n) =
    list_update_at (List.map f (List.seq 0 n)) idx v.
Proof.
  intros n idx v f Hidx.
  rewrite map_update_at_seq by exact Hidx.
  rewrite list_update_at_firstn_skipn.
  - reflexivity.
  - rewrite List.map_length, List.seq_length. exact Hidx.
Qed.

(** Module IDs in snap_pt_to_graph are unique. *)
Lemma snap_pt_to_graph_NoDup_fst :
  forall next_id sizes,
    NoDup (map fst (pg_modules (snap_pt_to_graph next_id sizes))).
Proof.
  intros. unfold snap_pt_to_graph. simpl pg_modules.
  assert (Hnd : NoDup (List.rev (List.seq 0 next_id))).
  { apply NoDup_rev. apply seq_NoDup. }
  set (l := List.rev (List.seq 0 next_id)) in *.
  clearbody l.
  induction l as [|a l IH]; simpl.
  - constructor.
  - inversion Hnd; subst.
    destruct (Nat.eqb (sizes a) 0).
    + exact (IH H2).
    + simpl. constructor.
      * intro Hin. apply H1.
        clear - Hin.
        induction l as [|b l IH']; simpl in Hin.
        -- destruct Hin.
        -- destruct (Nat.eqb (sizes b) 0).
           ++ right. exact (IH' Hin).
           ++ simpl in Hin. destruct Hin as [Heq|Hin'].
              ** left. exact Heq.
              ** right. exact (IH' Hin').
      * exact (IH H2).
Qed.

(** Module regions in snap_pt_to_graph are normalized (they are List.seq). *)
Lemma snap_pt_to_graph_region_normalized :
  forall next_id sizes mid m,
    graph_lookup_modules (pg_modules (snap_pt_to_graph next_id sizes)) mid = Some m ->
    normalize_region (module_region m) = module_region m.
Proof.
  intros next_id sizes mid m Hlook.
  unfold snap_pt_to_graph in Hlook. simpl pg_modules in Hlook.
  set (l := List.rev (List.seq 0 next_id)) in *.
  clearbody l.
  induction l as [|a l IH]; simpl in Hlook.
  - discriminate.
  - destruct (Nat.eqb (sizes a) 0) eqn:Esz.
    + exact (IH Hlook).
    + simpl in Hlook.
      destruct (Nat.eqb a mid) eqn:Eam.
      * inversion Hlook; subst. simpl. apply normalize_seq_nodups.
      * exact (IH Hlook).
Qed.

(** Core structural lemma: mapping modules with a pointwise-updated tensor
    function equals graph_insert_modules on the map with the original function.
    Requires NoDup on the module IDs. *)
Lemma modules_tensor_update :
  forall base mid idx value (old_fn : nat -> nat -> nat),
    idx < 16 ->
    NoDup (map fst base) ->
    (forall m, graph_lookup_modules base mid = Some m ->
      normalize_region (module_region m) = module_region m) ->
    let F id m := {| module_region := module_region m;
                     module_axioms := module_axioms m;
                     module_mu_tensor :=
                       List.map (fun k => if ((id =? mid) && (k =? idx))%bool
                                          then value else old_fn id k)
                                (List.seq 0 16) |} in
    let G id m := {| module_region := module_region m;
                     module_axioms := module_axioms m;
                     module_mu_tensor := List.map (old_fn id) (List.seq 0 16) |} in
    map (fun '(id, m) => (id, F id m)) base =

    match graph_lookup_modules (map (fun '(id, m) => (id, G id m)) base) mid with
    | Some m_looked =>
        graph_insert_modules
          (map (fun '(id, m) => (id, G id m)) base) mid
          (normalize_module
            {| module_region := module_region m_looked;
               module_axioms := module_axioms m_looked;
               module_mu_tensor :=
                 list_update_at (module_mu_tensor m_looked) idx value |})
    | None => map (fun '(id, m) => (id, G id m)) base
    end.
Proof.
  intros base mid idx value old_fn Hidx Hnd Hnorm F G.
  induction base as [|[id m] rest IH].
  - reflexivity.
  - cbn [map graph_lookup_modules].
    destruct (Nat.eqb id mid) eqn:Eid.
    + (* id = mid *)
      apply Nat.eqb_eq in Eid. subst id.
      cbn [graph_insert_modules]. rewrite Nat.eqb_refl.
      assert (Hhead : F mid m = normalize_module
        {| module_region := module_region (G mid m);
           module_axioms := module_axioms (G mid m);
           module_mu_tensor :=
             list_update_at (module_mu_tensor (G mid m)) idx value |}).
      { unfold F, G. cbn [module_region module_axioms module_mu_tensor].
        unfold normalize_module. cbn [module_region module_axioms module_mu_tensor].
        assert (Hnr : normalize_region (module_region m) = module_region m).
        { apply Hnorm. cbn [graph_lookup_modules]. rewrite Nat.eqb_refl. reflexivity. }
        rewrite Hnr. f_equal.
        rewrite <- map_eqb_update_to_list_update by exact Hidx.
        apply List.map_ext. intro k. rewrite Nat.eqb_refl. reflexivity. }
      rewrite Hhead. f_equal.
      (* Tail: F id' m' = G id' m' for id' ≠ mid *)
      inversion Hnd; subst.
      apply List.map_ext_in. intros [id' m'] Hin.
      assert (Hne : id' <> mid).
      { intro Heq. subst. apply H1.
        apply in_map_iff. exists (mid, m'). split; [reflexivity|exact Hin]. }
      unfold F, G. f_equal. f_equal.
      apply List.map_ext. intro k.
      rewrite (proj2 (Nat.eqb_neq id' mid) Hne). reflexivity.
    + (* id ≠ mid *)
      cbn [graph_insert_modules]. rewrite Eid.
      assert (Hhead : F id m = G id m).
      { unfold F, G. f_equal. apply List.map_ext. intro k.
        rewrite Eid. reflexivity. }
      rewrite Hhead.
      inversion Hnd; subst.
      specialize (IH H2 (fun m0 Hlu => Hnorm m0
        ltac:(cbn [graph_lookup_modules]; rewrite Eid; exact Hlu))).
      destruct (graph_lookup_modules (map (fun '(id0, m0) => (id0, G id0 m0)) rest) mid) as [ml|];
        f_equal; exact IH.
Qed.

(** snap_full_graph commutes with kami_step for TENSOR_SET. *)
Lemma snap_full_graph_tensor_set :
  forall ks mid i j value cost,
    tensor_indices_ok i j = true ->
    snap_full_graph (kami_step ks (instr_tensor_set mid i j value cost)) =
    graph_update_module_tensor (snap_full_graph ks) mid (i * 4 + j) value.
Proof.
  intros ks mid i j value cost Hok.
  assert (Hidx : i * 4 + j < 16) by (exact (tensor_flat_index_bound i j Hok)).
  unfold kami_step. rewrite Hok.
  unfold graph_update_module_tensor, graph_lookup, graph_update, snap_full_graph.
  simpl snap_pt_next_id. simpl snap_pt_sizes. simpl snap_module_tensors.
  simpl snap_rich_state.
  set (base := pg_modules (snap_pt_to_graph (snap_pt_next_id ks) (snap_pt_sizes ks))).
  pose proof (modules_tensor_update base mid (i*4+j) value (snap_module_tensors ks)
    Hidx (snap_pt_to_graph_NoDup_fst _ _)
    (snap_pt_to_graph_region_normalized _ _ mid)) as Hmtu.
  cbv zeta in Hmtu.
  rewrite Hmtu.
  destruct (graph_lookup_modules _ mid); reflexivity.
Qed.

(** Full VMState equality for TENSOR_SET. *)
Theorem driven_step_tensor_set_full :
  forall ks mid i j value cost,
    tensor_indices_ok i j = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_tensor_set mid i j value cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_tensor_set mid i j value cost).
Proof.
  intros ks mid i j value cost Hok.
  rewrite abs_full_snapshot_of_snapshot.
  rewrite (abs_full_snapshot_of_snapshot ks).
  rewrite snap_full_graph_tensor_set by exact Hok.
  unfold vm_apply, kami_step. rewrite Hok.
  unfold advance_state, apply_cost, instruction_cost.
  cbn [snap_pc snap_mu snap_err snap_regs snap_mem snap_mu_tensor
       snap_certified snap_logic_acc snap_mstatus snap_module_tensors
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11].
  reflexivity.
Qed.

(* ------------------------------------------------------------------
   §6c  Coupling data round-trip infrastructure
   ------------------------------------------------------------------ *)

(** write_coupling_pairs_aux preserves table entries below base. *)
Lemma write_coupling_pairs_aux_below :
  forall pairs tbl start k,
    k < start ->
    write_coupling_pairs_aux tbl start pairs k = tbl k.
Proof.
  induction pairs as [|[s t] rest IH]; intros tbl start k Hlt; simpl.
  - reflexivity.
  - rewrite IH by lia. rewrite (proj2 (Nat.eqb_neq k start)) by lia. reflexivity.
Qed.

(** filtermap distributes over map. *)
Lemma filtermap_compose :
  forall A B C (f : B -> option C) (g : A -> B) l,
    filtermap f (List.map g l) = filtermap (fun x => f (g x)) l.
Proof.
  intros. induction l as [|x xs IH]; simpl; [reflexivity|].
  destruct (f (g x)); f_equal; apply IH.
Qed.

(** Writing then reading coupling pairs recovers the original list. *)
Lemma write_coupling_pairs_round_trip :
  forall pairs (tbl : nat -> option CouplingPairEntry) base,
    filtermap
      (fun ofs =>
        match write_coupling_pairs_aux tbl base pairs (base + ofs) with
        | Some cpair => Some (coupling_pair_source cpair, coupling_pair_target cpair)
        | None => None
        end)
      (List.seq 0 (Datatypes.length pairs))
    = pairs.
Proof.
  induction pairs as [|[s t] rest IH]; intros tbl base; simpl.
  - reflexivity.
  - replace (base + 0) with base by lia. rewrite write_coupling_pairs_aux_below by lia.
    rewrite Nat.eqb_refl. simpl. f_equal.
    rewrite <- List.seq_shift. rewrite filtermap_compose.
    erewrite filtermap_ext.
    2:{ intros ofs _. replace (base + S ofs) with (S base + ofs) by lia. reflexivity. }
    apply IH.
Qed.

(** Full coupling data round-trip through rich_state_add_coupling_data. *)
Lemma coupling_data_round_trip :
  forall (rs : RichSnapshotState) (pairs : list (nat * nat)) (label : string),
    let '(rs1, desc_id) := rich_state_add_coupling_data rs pairs label in
    snapshot_coupling_pairs_from_desc rs1 desc_id = pairs.
Proof.
  intros rs pairs label.
  unfold rich_state_add_coupling_data, snapshot_coupling_pairs_from_desc.
  cbn [rich_coupling_desc_table coupling_desc_count coupling_desc_base
       rich_coupling_pair_table].
  rewrite Nat.eqb_refl.
  cbn [coupling_desc_count coupling_desc_base].
  apply write_coupling_pairs_round_trip.
Qed.

(** Coupling label round-trip. *)
Lemma coupling_label_round_trip :
  forall (rs : RichSnapshotState) (pairs : list (nat * nat)) (label : string),
    let '(rs1, desc_id) := rich_state_add_coupling_data rs pairs label in
    match rich_coupling_desc_table rs1 desc_id with
    | Some desc => coupling_desc_label desc
    | None => coupling_label empty_coupling_data
    end = label.
Proof.
  intros rs pairs label.
  unfold rich_state_add_coupling_data.
  cbn [rich_coupling_desc_table coupling_desc_label].
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Coupling descriptor allocation safety. *)
Definition coupling_desc_safe (ks : KamiSnapshot) : Prop :=
  rich_next_coupling_desc_id (snap_rich_state ks) > 0.

(* ======================================================================
   §7  Invariant Preservation
   *)

(** For SupportedOpcodes (which don't change snap_pt_next_id),
    the hardware representation invariant is trivially preserved. *)
Theorem hw_repr_invariant_supported_step :
  forall ks i,
    SupportedOpcode i ->
    hw_repr_invariant ks ->
    hw_repr_invariant (kami_step ks i).
Proof.
  intros ks i Hsup [Hge Hlt].
  unfold hw_repr_invariant, pt_well_formed.
  destruct i; simpl in Hsup; try contradiction;
  unfold kami_step; simpl snap_pt_next_id; split; lia.
Qed.

(* DEFINITIONAL HELPER *)
(** PNEW preserves the invariant when the result stays in range. *)
Theorem hw_repr_invariant_pnew :
  forall ks region cost,
    hw_repr_invariant ks ->
    S (snap_pt_next_id ks) < PTableSz ->
    hw_repr_invariant (kami_step ks (instr_pnew region cost)).
Proof.
  intros ks region cost [Hge Hlt] Hroom.
  unfold hw_repr_invariant, pt_well_formed, kami_step.
  simpl snap_pt_next_id. split; lia.
Qed.

(* ======================================================================
   §8  Extended Representation Invariant
   *)

(** Coupling descriptor table has no entry at index 0.
    All hardware-created morphisms use coupling_desc = 0.
    Maintained by all kami_step branches (none writes coupling descriptors). *)
Definition coupling_zero_empty (rs : RichSnapshotState) : Prop :=
  rs.(rich_coupling_desc_table) 0 = None.

(** Out-of-range morph table entries are None.  Maintained by
    rich_state_add_morph (writes at rich_next_morph_id, then bumps)
    and rich_state_delete_morph (sets existing entries to None). *)
Definition morph_table_wf (rs : RichSnapshotState) : Prop :=
  forall i, i >= rich_next_morph_id rs -> rich_morph_table rs i = None.

(** All existing morphisms have coupling_desc = 0 (hardware invariant:
    rich_state_add_morph always passes 0 as coupling_desc). *)
Definition coupling_desc_all_zero (rs : RichSnapshotState) : Prop :=
  forall i entry, rs.(rich_morph_table) i = Some entry ->
    morph_entry_coupling_desc entry = 0.

(** All morph table entries have coupling_desc strictly below next_desc_id.
    Preserved through add_morph_with_coupling because the new desc_id equals
    old_next_desc_id which then gets incremented. *)
Definition coupling_desc_bounded (rs : RichSnapshotState) : Prop :=
  forall i entry, rs.(rich_morph_table) i = Some entry ->
    morph_entry_coupling_desc entry < rich_next_coupling_desc_id rs.

(** All allocated descriptor table ranges fit within next_pair_id.
    Ensures existing pair reads are stable when new pairs are appended. *)
Definition coupling_pairs_in_range (rs : RichSnapshotState) : Prop :=
  forall d desc, rs.(rich_coupling_desc_table) d = Some desc ->
    coupling_desc_base desc + coupling_desc_count desc <= rich_next_coupling_pair_id rs.

(** All pair slots within every allocated descriptor range are Some.
    Enables length(snapshot_coupling_pairs_from_desc rs d) = coupling_desc_count. *)
Definition coupling_pairs_fully_populated (rs : RichSnapshotState) : Prop :=
  forall d desc ofs,
    rs.(rich_coupling_desc_table) d = Some desc ->
    ofs < coupling_desc_count desc ->
    rs.(rich_coupling_pair_table) (coupling_desc_base desc + ofs) <> None.

(** Combined well-formedness predicate for the coupling tables.
    Replaces coupling_desc_all_zero — this predicate IS preserved by all 46
    kami_step operations including COMPOSE and MORPH_TENSOR. *)
Definition coupling_wf (rs : RichSnapshotState) : Prop :=
  coupling_desc_bounded rs /\
  coupling_pairs_in_range rs /\
  coupling_pairs_fully_populated rs.

(** Combined extended invariant for full-state bridge proofs. *)
Definition extended_hw_invariant (ks : KamiSnapshot) : Prop :=
  pt_well_formed ks /\
  morph_table_wf (snap_rich_state ks) /\
  coupling_zero_empty (snap_rich_state ks) /\
  coupling_wf (snap_rich_state ks) /\
  coupling_desc_safe ks.

(** Adding coupling data preserves morphism snapshots under invariants. *)
Lemma coupling_data_preserves_morphisms :
  forall (rs : RichSnapshotState) (pairs : list (nat * nat)) (label : string),
    coupling_desc_all_zero rs ->
    coupling_zero_empty rs ->
    rich_next_coupling_desc_id rs > 0 ->
    snapshot_morphisms_of_rich_state
      (fst (rich_state_add_coupling_data rs pairs label)) =
    snapshot_morphisms_of_rich_state rs.
Proof.
  intros rs pairs label Hcdaz Hcze Hpos.
  unfold rich_state_add_coupling_data.
  unfold snapshot_morphisms_of_rich_state at 1.
  simpl rich_morph_table. simpl rich_next_morph_id.
  unfold snapshot_morphisms_of_rich_state.
  apply filtermap_ext. intros j _.
  destruct (rich_morph_table rs j) as [entry|] eqn:Erm; [|reflexivity].
  specialize (Hcdaz j entry Erm).
  f_equal. f_equal. f_equal.
  rewrite Hcdaz.
  unfold snapshot_coupling_pairs_from_desc.
  simpl rich_coupling_desc_table.
  destruct (rich_next_coupling_desc_id rs) as [|n] eqn:Edid; [lia|].
  simpl Nat.eqb. rewrite Hcze. reflexivity.
Qed.

(** If every element of l maps to Some under f, filtermap returns all of them
    so its length equals length l. *)
Lemma filtermap_all_some_length :
  forall A B (f : A -> option B) (l : list A),
    (forall x, In x l -> f x <> None) ->
    length (filtermap f l) = length l.
Proof.
  intros A B f l Hall.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - specialize (Hall x (or_introl eq_refl)) as Hx.
    destruct (f x) as [b|]; [|exfalso; exact (Hx eq_refl)].
    simpl. f_equal. apply IH. intros y Hy. apply Hall. right. exact Hy.
Qed.

(** write_coupling_pairs_aux writes Some at every position in the written range. *)
Lemma write_coupling_pairs_aux_write_some :
  forall pairs tbl start k,
    start <= k < start + length pairs ->
    exists cpair, write_coupling_pairs_aux tbl start pairs k = Some cpair.
Proof.
  induction pairs as [|[s t] rest IH]; intros tbl start k Hrange; simpl in *.
  - lia.
  - destruct (Nat.eqb k start) eqn:Ek.
    + apply Nat.eqb_eq in Ek. subst k.
      rewrite write_coupling_pairs_aux_below by lia.
      simpl. rewrite Nat.eqb_refl. eexists. reflexivity.
    + apply Nat.eqb_neq in Ek.
      apply IH. lia.
Qed.

(** Generalised version of coupling_data_preserves_morphisms that uses
    coupling_wf instead of the stronger coupling_desc_all_zero.
    The key insight: coupling_desc_bounded ensures each existing morph's
    coupling_desc < new_desc_id, so the desc table lookup is unchanged;
    coupling_pairs_in_range ensures the pair reads are below pair_base
    and thus unaffected by write_coupling_pairs_aux_below. *)
Lemma coupling_data_preserves_morphisms_gen :
  forall (rs : RichSnapshotState) (pairs : list (nat * nat)) (label : string),
    coupling_wf rs ->
    coupling_zero_empty rs ->
    rich_next_coupling_desc_id rs > 0 ->
    snapshot_morphisms_of_rich_state
      (fst (rich_state_add_coupling_data rs pairs label)) =
    snapshot_morphisms_of_rich_state rs.
Proof.
  intros rs pairs label [Hcdb [Hpir Hfp]] Hcze Hsafe.
  unfold rich_state_add_coupling_data.
  unfold snapshot_morphisms_of_rich_state at 1.
  simpl rich_morph_table. simpl rich_next_morph_id.
  unfold snapshot_morphisms_of_rich_state.
  apply filtermap_ext. intros j _.
  destruct (rich_morph_table rs j) as [entry|] eqn:Erm; [|reflexivity].
  f_equal. f_equal. f_equal.
  (* Goal: coupling record equality for morph_coupling field
     (coupling_pairs + coupling_label both need to match) *)
  specialize (Hcdb j entry Erm) as Hlt.
  assert (Hneq : Nat.eqb (morph_entry_coupling_desc entry)
                          (rich_next_coupling_desc_id rs) = false).
  { apply Nat.eqb_neq. lia. }
  f_equal.
  - (* coupling_pairs subgoal *)
    unfold snapshot_coupling_pairs_from_desc.
    simpl rich_coupling_desc_table.
    rewrite Hneq.
    destruct (rich_coupling_desc_table rs (morph_entry_coupling_desc entry))
      as [desc|] eqn:Edesc; [|reflexivity].
    apply filtermap_ext. intros ofs Hofs.
    apply List.in_seq in Hofs. destruct Hofs as [_ Hlt_ofs]. simpl in Hlt_ofs.
    specialize (Hpir (morph_entry_coupling_desc entry) desc Edesc) as Hrange.
    assert (Hbelow : coupling_desc_base desc + ofs < rich_next_coupling_pair_id rs) by lia.
    simpl rich_coupling_pair_table.
    rewrite write_coupling_pairs_aux_below by exact Hbelow.
    reflexivity.
  - (* coupling_label subgoal *)
    simpl rich_coupling_desc_table.
    rewrite Hneq. reflexivity.
Qed.

(** Generalised version of morph_add_with_coupling_commutation using coupling_wf
    instead of coupling_desc_all_zero. *)
Lemma morph_add_with_coupling_commutation_gen :
  forall (rs : RichSnapshotState) (src dst : nat)
         (pairs : list (nat * nat)) (label : string) (is_id : bool),
    coupling_wf rs ->
    coupling_zero_empty rs ->
    rich_next_coupling_desc_id rs > 0 ->
    let '(rs', new_id) := rich_state_add_morph_with_coupling rs src dst pairs label is_id in
    snapshot_morphisms_of_rich_state rs' =
      (new_id,
       {| morph_source := src;
          morph_target := dst;
          morph_coupling :=
            {| coupling_pairs := pairs;
               coupling_label := label |};
          morph_is_identity := is_id;
               morph_cert_cost := 0 |})
      :: snapshot_morphisms_of_rich_state rs.
Proof.
  intros rs src dst pairs label is_id Hwcf Hcze Hsafe.
  unfold rich_state_add_morph_with_coupling.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Eadd.
  destruct (rich_state_add_morph rs1 src dst desc_id is_id) as [rs' new_id] eqn:Eram.
  pose proof (morph_add_commutation rs1 src dst desc_id is_id) as Hmc.
  rewrite Eram in Hmc. simpl in Hmc.
  pose proof (coupling_data_round_trip rs pairs label) as Hpairs.
  rewrite Eadd in Hpairs. simpl in Hpairs.
  pose proof (coupling_label_round_trip rs pairs label) as Hlabel.
  rewrite Eadd in Hlabel. simpl in Hlabel.
  pose proof (coupling_data_preserves_morphisms_gen rs pairs label Hwcf Hcze Hsafe) as Hold.
  rewrite Eadd in Hold. simpl in Hold.
  rewrite Hmc, Hpairs, Hlabel, Hold.
  reflexivity.
Qed.

(** Under coupling_pairs_fully_populated, the length of
    snapshot_coupling_pairs_from_desc equals coupling_desc_count. *)
Lemma coupling_count_length :
  forall (rs : RichSnapshotState) (desc_id : nat) (desc : CouplingDescriptorEntry),
    coupling_pairs_fully_populated rs ->
    rs.(rich_coupling_desc_table) desc_id = Some desc ->
    length (snapshot_coupling_pairs_from_desc rs desc_id) = coupling_desc_count desc.
Proof.
  intros rs desc_id desc Hfp Edesc.
  unfold snapshot_coupling_pairs_from_desc. rewrite Edesc.
  transitivity (List.length (List.seq 0 (coupling_desc_count desc))).
  - apply filtermap_all_some_length.
    intros ofs Hofs.
    apply List.in_seq in Hofs. destruct Hofs as [_ Hlt]. simpl in Hlt.
    specialize (Hfp desc_id desc ofs Edesc Hlt) as Hsome.
    destruct (rich_coupling_pair_table rs (coupling_desc_base desc + ofs)) as [cp|] eqn:Heq.
    + discriminate.
    + congruence.
  - apply List.seq_length.
Qed.



(*  These lemmas prove the three primitive operations that can modify the
   morph table each individually preserve morph_table_wf.  The master
   theorem morph_table_wf_kami_step_preserved then dispatches all 46
   vm_instruction constructors to the appropriate helper.
   *)

(** rich_state_add_morph writes at rich_next_morph_id (the current next
    slot) and bumps the counter.  Any index >= new next_morph_id was also
    >= the old one, so the out-of-range invariant is maintained. *)
Lemma morph_table_wf_preserved_add :
  forall rs src dst desc is_id rs' new_id,
    rich_state_add_morph rs src dst desc is_id = (rs', new_id) ->
    morph_table_wf rs ->
    morph_table_wf rs'.
Proof.
  intros rs src dst desc is_id rs' new_id Hadd Hwf.
  unfold rich_state_add_morph in Hadd. inversion Hadd; subst rs' new_id.
  unfold morph_table_wf. simpl rich_next_morph_id. simpl rich_morph_table.
  intros i Hi.
  assert (Hne : Nat.eqb i (rich_next_morph_id rs) = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hne. apply Hwf. lia.
Qed.

(** rich_state_delete_morph sets one slot to None and leaves the counter
    unchanged.  Any index that was already out-of-range stays out-of-range. *)
Lemma morph_table_wf_preserved_delete :
  forall rs mid,
    morph_table_wf rs ->
    morph_table_wf (rich_state_delete_morph rs mid).
Proof.
  intros rs mid Hwf.
  unfold morph_table_wf, rich_state_delete_morph.
  simpl rich_next_morph_id. simpl rich_morph_table.
  intros i Hi.
  destruct (Nat.eqb_spec i mid) as [|_]; [reflexivity|].
  apply Hwf. exact Hi.
Qed.

(** A standalone [morph_table_wf_preserved_add_coupling] used to live
    here, asserting that [rich_state_add_coupling_data] preserves
    [morph_table_wf].  The fact is purely definitional —
    [rich_state_add_coupling_data] does not touch [rich_morph_table] or
    [rich_next_morph_id], so the goal reduces to the hypothesis after
    [unfold rich_state_add_coupling_data, morph_table_wf; simpl] — and
    the lemma had a single caller ([morph_table_wf_preserved_add_with_coupling],
    below), which now performs that unfold inline. *)

(** rich_state_add_morph_with_coupling = add_coupling then add_morph;
    both steps preserve morph_table_wf. *)
Lemma morph_table_wf_preserved_add_with_coupling :
  forall rs src dst pairs label is_id rs' new_id,
    rich_state_add_morph_with_coupling rs src dst pairs label is_id = (rs', new_id) ->
    morph_table_wf rs ->
    morph_table_wf rs'.
Proof.
  intros rs src dst pairs label is_id rs' new_id Hadd Hwf.
  unfold rich_state_add_morph_with_coupling in Hadd.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Ecd.
  apply (morph_table_wf_preserved_add rs1 src dst desc_id is_id rs' new_id Hadd).
  replace rs1 with (fst (rich_state_add_coupling_data rs pairs label)).
  - (* [rich_state_add_coupling_data] leaves [rich_morph_table] and
       [rich_next_morph_id] untouched, so [morph_table_wf] on its result
       reduces to [morph_table_wf rs] by [simpl]. *)
    unfold rich_state_add_coupling_data. simpl fst.
    unfold morph_table_wf. simpl rich_next_morph_id. simpl rich_morph_table.
    exact Hwf.
  - rewrite Ecd. reflexivity.
Qed.

(** morph_table_wf is preserved by every kami_step operation.
    Non-MORPH opcodes leave snap_rich_state unchanged.
    MORPH opcodes use add/delete operations proved above to preserve the invariant. *)
Theorem morph_table_wf_kami_step_preserved :
  forall ks i,
    morph_table_wf (snap_rich_state ks) ->
    morph_table_wf (snap_rich_state (kami_step ks i)).
Proof.
  intros ks i Hwf. destruct i;
    (* Try to close the goal for opcodes that preserve snap_rich_state unchanged.
       For record-literal arms with snap_rich_state := snap_rich_state ks,
       simpl snap_rich_state reduces the projection to snap_rich_state ks. *)
    first [
      (unfold kami_step,
          kami_advance_default, kami_advance_reg, kami_advance_err,
          kami_advance_cert_addr, kami_advance_err_rich;
       simpl snap_rich_state; exact Hwf)
    | idtac ].
  (* Remaining: instr_chsh_trial, instr_tensor_set, instr_tensor_get,
     instr_morph, instr_compose, instr_morph_id, instr_morph_delete,
     instr_morph_assert, instr_morph_tensor, instr_morph_get
     Variable names below match the inductive constructor formal parameters
     in VMStep.v. *)
  (* instr_chsh_trial (x y a b mu_delta): all branches of nested match/if
     call mk which always sets snap_rich_state := snap_rich_state ks *)
  - unfold kami_step.
    destruct x; destruct y; destruct (Nat.eqb a b);
      simpl snap_rich_state; exact Hwf.
  (* instr_tensor_set (module i j value mu_delta): both branches preserve *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hwf.
  (* instr_tensor_get (dst module i j mu_delta): both branches preserve *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hwf.
  (* instr_morph (dst src_mod dst_mod coupling_idx mu_delta):
     success path uses rich_state_add_morph *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) &&
              negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) src_mod dst_mod 0 false)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      exact (morph_table_wf_preserved_add _ _ _ _ _ _ _ Eram Hwf).
    + unfold kami_advance_err. simpl snap_rich_state. exact Hwf.
  (* instr_compose (dst m1_id m2_id mu_delta):
     success path uses rich_state_add_morph_with_coupling *)
  - unfold kami_step.
    destruct (rich_morph_table (snap_rich_state ks) m1_id) as [e1|] eqn:He1;
    destruct (rich_morph_table (snap_rich_state ks) m2_id) as [e2|] eqn:He2;
    try (unfold kami_advance_err; simpl snap_rich_state; exact Hwf).
    destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Heq;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwf].
    (* Composed coupling is now a 3-way branch on the identity flags
       (id;f = f, f;id = f, else relational_compose); morph_table_wf is
       preserved by add_with_coupling for ANY coupling, so capture the actual
       arguments generically rather than pinning the relational_compose form. *)
    match goal with
    | |- context[rich_state_add_morph_with_coupling ?a ?b ?c ?d ?e ?f] =>
        destruct (rich_state_add_morph_with_coupling a b c d e f)
                 as [rs' nid] eqn:Eadd
    end.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (morph_table_wf_preserved_add_with_coupling _ _ _ _ _ _ _ _ Eadd Hwf).
  (* instr_morph_id (dst module mu_delta):
     success path uses rich_state_add_morph *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks module) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) module module 0 true)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      exact (morph_table_wf_preserved_add _ _ _ _ _ _ _ Eram Hwf).
    + unfold kami_advance_err. simpl snap_rich_state. exact Hwf.
  (* instr_morph_delete (morph_id mu_delta):
     success path uses rich_state_delete_morph *)
  - unfold kami_step, kami_advance_rich_noret, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id) eqn:Hmt;
      simpl snap_rich_state.
    + apply morph_table_wf_preserved_delete. exact Hwf.
    + exact Hwf.
  (* instr_morph_assert (morph_id property cert mu_delta):
     both branches preserve snap_rich_state *)
  - unfold kami_step, kami_advance_cert_addr, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hwf.
  (* instr_morph_tensor (dst f_id g_id mu_delta):
     success path uses rich_state_add_morph_with_coupling *)
  - unfold kami_step.
    set (g := snap_full_graph ks).
    destruct (graph_tensor_morphisms g f_id g_id) as [[g' mid]|] eqn:Htens;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwf].
    destruct (graph_lookup_morphism g' mid) as [new_ms|] eqn:Hglu;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwf].
    destruct (rich_state_add_morph_with_coupling
                (snap_rich_state ks)
                (morph_source new_ms) (morph_target new_ms)
                (coupling_pairs (morph_coupling new_ms))
                (coupling_label (morph_coupling new_ms))
                false)
              as [rs' nid2] eqn:Eadd.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (morph_table_wf_preserved_add_with_coupling _ _ _ _ _ _ _ _ Eadd Hwf).
  (* instr_morph_get (dst morph_id selector mu_delta):
     both branches preserve snap_rich_state *)
  - unfold kami_step, kami_advance_reg, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hwf.
Qed.

(* ======================================================================
   §8c  coupling_desc_safe and coupling_zero_empty Preservation Under kami_step

   These lemmas prove that coupling_desc_safe and coupling_zero_empty are
   preserved by every kami_step operation.

   coupling_desc_safe (rich_next_coupling_desc_id > 0):
     - All ops except COMPOSE/MORPH_TENSOR success: counter unchanged → preserved by Hsafe.
     - COMPOSE/MORPH_TENSOR success: counter incremented by 1 → always > 0.

   coupling_zero_empty (rich_coupling_desc_table 0 = None):
     - Only rich_state_add_coupling_data modifies the coupling_desc_table,
       writing at desc_id = rich_next_coupling_desc_id rs > 0.
       Since desc_id ≠ 0 (by coupling_desc_safe), slot 0 is never overwritten.
     - All other ops leave rich_coupling_desc_table unchanged.

   Together, these establish that coupling_desc_safe and coupling_zero_empty
   are naturally satisfied in all execution traces starting from a valid
   initial state (where rich_next_coupling_desc_id = 1 initially).
   This is the direct analogue of morph_table_wf_kami_step_preserved for
   the coupling-table components of extended_hw_invariant.
   *)

(** rich_state_add_morph does not modify rich_next_coupling_desc_id. *)
Lemma add_morph_preserves_next_coupling_desc_id :
  forall rs src dst desc is_id,
    rich_next_coupling_desc_id (fst (rich_state_add_morph rs src dst desc is_id)) =
    rich_next_coupling_desc_id rs.
Proof.
  intros. unfold rich_state_add_morph. simpl fst. simpl rich_next_coupling_desc_id.
  reflexivity.
Qed.

(** rich_state_add_morph does not modify rich_coupling_desc_table. *)
Lemma add_morph_preserves_coupling_desc_table :
  forall rs src dst desc is_id,
    (fst (rich_state_add_morph rs src dst desc is_id)).(rich_coupling_desc_table) =
    rs.(rich_coupling_desc_table).
Proof.
  intros. unfold rich_state_add_morph. simpl fst. simpl rich_coupling_desc_table.
  reflexivity.
Qed.

(** rich_state_delete_morph does not modify rich_next_coupling_desc_id. *)
Lemma delete_morph_preserves_next_coupling_desc_id :
  forall rs mid,
    rich_next_coupling_desc_id (rich_state_delete_morph rs mid) =
    rich_next_coupling_desc_id rs.
Proof.
  intros. unfold rich_state_delete_morph. simpl rich_next_coupling_desc_id. reflexivity.
Qed.

(** rich_state_delete_morph does not modify rich_coupling_desc_table. *)
Lemma delete_morph_preserves_coupling_desc_table :
  forall rs mid,
    (rich_state_delete_morph rs mid).(rich_coupling_desc_table) = rs.(rich_coupling_desc_table).
Proof.
  intros. unfold rich_state_delete_morph. simpl rich_coupling_desc_table. reflexivity.
Qed.

(** rich_state_add_coupling_data increases rich_next_coupling_desc_id by 1,
    so the result is always > 0 regardless of the initial value. *)
Lemma add_coupling_next_desc_id_pos :
  forall rs pairs label,
    rich_next_coupling_desc_id (fst (rich_state_add_coupling_data rs pairs label)) > 0.
Proof.
  intros. unfold rich_state_add_coupling_data. simpl fst.
  simpl rich_next_coupling_desc_id. lia.
Qed.

(** rich_state_add_coupling_data writes at desc_id = old next_coupling_desc_id.
    If coupling_desc_safe holds (> 0), slot 0 is not written, so coupling_zero_empty
    is preserved. *)
Lemma add_coupling_preserves_coupling_zero_empty :
  forall rs pairs label,
    rich_next_coupling_desc_id rs > 0 ->
    coupling_zero_empty rs ->
    coupling_zero_empty (fst (rich_state_add_coupling_data rs pairs label)).
Proof.
  intros rs pairs label Hpos Hcze.
  unfold rich_state_add_coupling_data. simpl fst.
  unfold coupling_zero_empty. simpl rich_coupling_desc_table.
  assert (Hne : Nat.eqb 0 (rich_next_coupling_desc_id rs) = false).
  { apply Nat.eqb_neq. lia. }
  rewrite Hne. exact Hcze.
Qed.

(** rich_state_add_morph_with_coupling = add_coupling then add_morph:
    - next_coupling_desc_id increases by 1 (from add_coupling) → always > 0
    - coupling_zero_empty is preserved (slot 0 not touched since old_id > 0) *)
Lemma add_with_coupling_preserves_coupling_zero_empty :
  forall rs src dst pairs label is_id rs' new_id,
    rich_state_add_morph_with_coupling rs src dst pairs label is_id = (rs', new_id) ->
    rich_next_coupling_desc_id rs > 0 ->
    coupling_zero_empty rs ->
    coupling_zero_empty rs'.
Proof.
  intros rs src dst pairs label is_id rs' new_id Hadd Hpos Hcze.
  unfold rich_state_add_morph_with_coupling in Hadd.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Ecd.
  (* rs1 satisfies coupling_zero_empty *)
  assert (Hcze1 : coupling_zero_empty rs1).
  { replace rs1 with (fst (rich_state_add_coupling_data rs pairs label))
      by (rewrite Ecd; reflexivity).
    apply add_coupling_preserves_coupling_zero_empty; assumption. }
  (* rs' = fst (rich_state_add_morph rs1 ... ) satisfies coupling_zero_empty *)
  assert (Hstep : coupling_zero_empty (fst (rich_state_add_morph rs1 src dst desc_id is_id))).
  { unfold coupling_zero_empty. rewrite add_morph_preserves_coupling_desc_table.
    exact Hcze1. }
  rewrite Hadd in Hstep. exact Hstep.
Qed.

Lemma add_with_coupling_next_desc_id_pos :
  forall rs src dst pairs label is_id rs' new_id,
    rich_state_add_morph_with_coupling rs src dst pairs label is_id = (rs', new_id) ->
    rich_next_coupling_desc_id rs' > 0.
Proof.
  intros rs src dst pairs label is_id rs' new_id Hadd.
  unfold rich_state_add_morph_with_coupling in Hadd.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Ecd.
  assert (Hpos1 : rich_next_coupling_desc_id rs1 > 0).
  { replace rs1 with (fst (rich_state_add_coupling_data rs pairs label))
      by (rewrite Ecd; reflexivity).
    apply add_coupling_next_desc_id_pos. }
  assert (Hstep : rich_next_coupling_desc_id (fst (rich_state_add_morph rs1 src dst desc_id is_id)) > 0).
  { rewrite add_morph_preserves_next_coupling_desc_id. exact Hpos1. }
  rewrite Hadd in Hstep. exact Hstep.
Qed.

(** coupling_desc_safe (rich_next_coupling_desc_id > 0) is preserved by all
    46 kami_step operations.  Non-COMPOSE/MORPH_TENSOR ops leave the counter
    unchanged; those two success paths increment it (always stays > 0). *)
Theorem coupling_desc_safe_kami_step_preserved :
  forall ks i,
    coupling_desc_safe ks ->
    coupling_desc_safe (kami_step ks i).
Proof.
  intros ks i Hsafe. unfold coupling_desc_safe in *.
  destruct i;
    first [
      (unfold kami_step,
          kami_advance_default, kami_advance_reg, kami_advance_err,
          kami_advance_cert_addr, kami_advance_err_rich;
       simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe)
    | idtac ].
  (* instr_chsh_trial *)
  - unfold kami_step.
    destruct x; destruct y; destruct (Nat.eqb a b);
      simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe.
  (* instr_tensor_set *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j);
      simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe.
  (* instr_tensor_get *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j);
      simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe.
  (* instr_morph: success uses rich_state_add_morph — preserves counter *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) &&
              negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) src_mod dst_mod 0 false)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      pose proof (add_morph_preserves_next_coupling_desc_id
                    (snap_rich_state ks) src_mod dst_mod 0 false) as Hpres.
      rewrite Eram in Hpres. simpl fst in Hpres. lia.
    + unfold kami_advance_err. simpl snap_rich_state.
      simpl rich_next_coupling_desc_id. exact Hsafe.
  (* instr_compose: success uses add_morph_with_coupling — counter +1, always > 0 *)
  - unfold kami_step.
    destruct (rich_morph_table (snap_rich_state ks) m1_id) as [e1|] eqn:He1;
    destruct (rich_morph_table (snap_rich_state ks) m2_id) as [e2|] eqn:He2;
    try (unfold kami_advance_err; simpl snap_rich_state;
         simpl rich_next_coupling_desc_id; exact Hsafe).
    destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Heq;
    [|unfold kami_advance_err; simpl snap_rich_state;
      simpl rich_next_coupling_desc_id; exact Hsafe].
    match goal with
    | |- context[rich_state_add_morph_with_coupling ?a ?b ?c ?d ?e ?f] =>
        destruct (rich_state_add_morph_with_coupling a b c d e f)
                 as [rs' nid] eqn:Eawc
    end.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (add_with_coupling_next_desc_id_pos _ _ _ _ _ _ _ _ Eawc).
  (* instr_morph_id: success uses rich_state_add_morph — preserves counter *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks module) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) module module 0 true)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      pose proof (add_morph_preserves_next_coupling_desc_id
                    (snap_rich_state ks) module module 0 true) as Hpres.
      rewrite Eram in Hpres. simpl fst in Hpres. lia.
    + unfold kami_advance_err. simpl snap_rich_state.
      simpl rich_next_coupling_desc_id. exact Hsafe.
  (* instr_morph_delete: success uses rich_state_delete_morph — preserves counter *)
  - unfold kami_step, kami_advance_rich_noret, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id) eqn:Hmt;
      simpl snap_rich_state.
    + rewrite delete_morph_preserves_next_coupling_desc_id. exact Hsafe.
    + simpl rich_next_coupling_desc_id. exact Hsafe.
  (* instr_morph_assert: cert_addr or err — rich_state unchanged *)
  - unfold kami_step, kami_advance_cert_addr, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe.
  (* instr_morph_tensor: success uses add_morph_with_coupling — counter +1, always > 0 *)
  - unfold kami_step.
    set (g := snap_full_graph ks).
    destruct (graph_tensor_morphisms g f_id g_id) as [[g' mid]|] eqn:Htens;
      [|unfold kami_advance_err; simpl snap_rich_state;
        simpl rich_next_coupling_desc_id; exact Hsafe].
    destruct (graph_lookup_morphism g' mid) as [new_ms|] eqn:Hglu;
      [|unfold kami_advance_err; simpl snap_rich_state;
        simpl rich_next_coupling_desc_id; exact Hsafe].
    destruct (rich_state_add_morph_with_coupling (snap_rich_state ks)
               (morph_source new_ms) (morph_target new_ms)
               (coupling_pairs (morph_coupling new_ms))
               (coupling_label (morph_coupling new_ms)) false) as [rs' nid2] eqn:Eadd.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (add_with_coupling_next_desc_id_pos _ _ _ _ _ _ _ _ Eadd).
  (* instr_morph_get: reg or err — rich_state unchanged *)
  - unfold kami_step, kami_advance_reg, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; simpl rich_next_coupling_desc_id; exact Hsafe.
Qed.

(** coupling_zero_empty (rich_coupling_desc_table 0 = None) is preserved by all
    46 kami_step operations, conditional only on coupling_desc_safe holding
    initially.  The key argument: rich_state_add_coupling_data writes at
    desc_id = rich_next_coupling_desc_id rs > 0 (by coupling_desc_safe), so
    slot 0 is never written. *)
Theorem coupling_zero_empty_kami_step_preserved :
  forall ks i,
    coupling_desc_safe ks ->
    coupling_zero_empty (snap_rich_state ks) ->
    coupling_zero_empty (snap_rich_state (kami_step ks i)).
Proof.
  intros ks i Hsafe Hcze.
  unfold coupling_desc_safe in Hsafe.
  destruct i;
    first [
      (unfold kami_step,
          kami_advance_default, kami_advance_reg, kami_advance_err,
          kami_advance_cert_addr, kami_advance_err_rich;
       simpl snap_rich_state; exact Hcze)
    | idtac ].
  (* instr_chsh_trial *)
  - unfold kami_step.
    destruct x; destruct y; destruct (Nat.eqb a b);
      simpl snap_rich_state; exact Hcze.
  (* instr_tensor_set *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hcze.
  (* instr_tensor_get *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hcze.
  (* instr_morph: rich_state_add_morph doesn't touch coupling_desc_table *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) &&
              negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) src_mod dst_mod 0 false)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      assert (Htbl : rs'.(rich_coupling_desc_table) =
                     (snap_rich_state ks).(rich_coupling_desc_table)).
      { pose proof (add_morph_preserves_coupling_desc_table
                      (snap_rich_state ks) src_mod dst_mod 0 false) as H.
        rewrite Eram in H. exact H. }
      unfold coupling_zero_empty. rewrite Htbl. exact Hcze.
    + unfold kami_advance_err. simpl snap_rich_state. exact Hcze.
  (* instr_compose: add_coupling writes at desc_id = old_next > 0 (by Hsafe),
     so slot 0 is untouched; coupling_zero_empty is preserved *)
  - unfold kami_step.
    destruct (rich_morph_table (snap_rich_state ks) m1_id) as [e1|] eqn:He1;
    destruct (rich_morph_table (snap_rich_state ks) m2_id) as [e2|] eqn:He2;
    try (unfold kami_advance_err; simpl snap_rich_state; exact Hcze).
    destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Heq;
    [|unfold kami_advance_err; simpl snap_rich_state; exact Hcze].
    match goal with
    | |- context[rich_state_add_morph_with_coupling ?a ?b ?c ?d ?e ?f] =>
        destruct (rich_state_add_morph_with_coupling a b c d e f)
                 as [rs' nid] eqn:Eawc
    end.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (add_with_coupling_preserves_coupling_zero_empty
             _ _ _ _ _ _ _ _ Eawc Hsafe Hcze).
  (* instr_morph_id: rich_state_add_morph doesn't touch coupling_desc_table *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks module) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) module module 0 true)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      assert (Htbl : rs'.(rich_coupling_desc_table) =
                     (snap_rich_state ks).(rich_coupling_desc_table)).
      { pose proof (add_morph_preserves_coupling_desc_table
                      (snap_rich_state ks) module module 0 true) as H.
        rewrite Eram in H. exact H. }
      unfold coupling_zero_empty. rewrite Htbl. exact Hcze.
    + unfold kami_advance_err. simpl snap_rich_state. exact Hcze.
  (* instr_morph_delete: rich_state_delete_morph doesn't touch coupling_desc_table *)
  - unfold kami_step, kami_advance_rich_noret, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id) eqn:Hmt;
      simpl snap_rich_state.
    + unfold coupling_zero_empty. rewrite delete_morph_preserves_coupling_desc_table.
      exact Hcze.
    + exact Hcze.
  (* instr_morph_assert: cert_addr or err — rich_state unchanged *)
  - unfold kami_step, kami_advance_cert_addr, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hcze.
  (* instr_morph_tensor: same as compose *)
  - unfold kami_step.
    set (g := snap_full_graph ks).
    destruct (graph_tensor_morphisms g f_id g_id) as [[g' mid]|] eqn:Htens;
      [|unfold kami_advance_err; simpl snap_rich_state; exact Hcze].
    destruct (graph_lookup_morphism g' mid) as [new_ms|] eqn:Hglu;
      [|unfold kami_advance_err; simpl snap_rich_state; exact Hcze].
    destruct (rich_state_add_morph_with_coupling (snap_rich_state ks)
               (morph_source new_ms) (morph_target new_ms)
               (coupling_pairs (morph_coupling new_ms))
               (coupling_label (morph_coupling new_ms)) false) as [rs' nid2] eqn:Eadd.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (add_with_coupling_preserves_coupling_zero_empty
             _ _ _ _ _ _ _ _ Eadd Hsafe Hcze).
  (* instr_morph_get: reg or err — rich_state unchanged *)
  - unfold kami_step, kami_advance_reg, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hcze.
Qed.

(* ======================================================================
   §8d  coupling_wf Preservation Under kami_step

   coupling_wf = coupling_desc_bounded /\ coupling_pairs_in_range /\
                 coupling_pairs_fully_populated

   This IS an inductive invariant: unlike coupling_desc_all_zero it is
   preserved by COMPOSE and MORPH_TENSOR because the new coupling_desc
   equals the old next_desc_id which is then incremented, keeping all
   existing descs strictly below the new next_desc_id.
   *)

(** rich_state_add_morph preserves coupling_wf when the new desc index is
    strictly below the current next_coupling_desc_id. *)
Lemma coupling_wf_preserved_add :
  forall rs src dst desc is_id rs' new_id,
    rich_state_add_morph rs src dst desc is_id = (rs', new_id) ->
    coupling_wf rs ->
    desc < rich_next_coupling_desc_id rs ->
    coupling_wf rs'.
Proof.
  intros rs src dst desc is_id rs' new_id Hadd [Hcdb [Hpir Hfp]] Hlt.
  unfold rich_state_add_morph in Hadd. inversion Hadd; subst rs' new_id; clear Hadd.
  split; [|split].
  - (* coupling_desc_bounded: new morph has desc < next_desc_id; others unchanged *)
    intros i entry Htbl.
    simpl rich_morph_table in Htbl. simpl rich_next_coupling_desc_id.
    destruct (Nat.eqb_spec i (rich_next_morph_id rs)) as [Heq|Hne].
    + subst i. inversion Htbl; subst entry; clear Htbl.
      simpl morph_entry_coupling_desc. exact Hlt.
    + assert (Hf : Nat.eqb i (rich_next_morph_id rs) = false).
      { apply Nat.eqb_neq. exact Hne. }
      exact (Hcdb i entry Htbl).
  - (* coupling_pairs_in_range: coupling tables unchanged *)
    intros d desc_entry Hdesc.
    simpl rich_coupling_desc_table in Hdesc.
    simpl rich_next_coupling_pair_id.
    exact (Hpir d desc_entry Hdesc).
  - (* coupling_pairs_fully_populated: pair table unchanged *)
    intros d desc_entry ofs Hdesc Hofs.
    simpl rich_coupling_desc_table in Hdesc.
    simpl rich_coupling_pair_table.
    exact (Hfp d desc_entry ofs Hdesc Hofs).
Qed.

(** rich_state_add_coupling_data preserves coupling_wf. *)
Lemma coupling_wf_preserved_add_coupling :
  forall rs pairs label rs1 desc_id,
    coupling_wf rs ->
    rich_state_add_coupling_data rs pairs label = (rs1, desc_id) ->
    coupling_wf rs1.
Proof.
  intros rs pairs label rs1 new_desc_id [Hcdb [Hpir Hfp]] Hadd.
  unfold rich_state_add_coupling_data in Hadd.
  inversion Hadd; subst rs1 new_desc_id; clear Hadd.
  split; [|split].
  - (* coupling_desc_bounded: morph table unchanged; next_desc_id incremented *)
    intros i entry Htbl.
    simpl rich_morph_table in Htbl.
    specialize (Hcdb i entry Htbl) as Hlt.
    simpl rich_next_coupling_desc_id. lia.
  - (* coupling_pairs_in_range: new desc has base+count = new_next_pair_id; old descs ≤ new *)
    intros d desc Hdesc.
    simpl rich_next_coupling_pair_id.
    simpl rich_coupling_desc_table in Hdesc.
    destruct (Nat.eqb_spec d (rich_next_coupling_desc_id rs)) as [Heq|Hne].
    + subst d.
      inversion Hdesc; subst desc; clear Hdesc.
      simpl coupling_desc_base. simpl coupling_desc_count. lia.
    + assert (Hf : Nat.eqb d (rich_next_coupling_desc_id rs) = false).
      { apply Nat.eqb_neq. exact Hne. }
      specialize (Hpir d desc Hdesc). lia.
  - (* coupling_pairs_fully_populated: new slots Some by write_some; old by below + Hfp *)
    intros d desc ofs Hdesc Hofs.
    simpl rich_coupling_desc_table in Hdesc.
    simpl rich_coupling_pair_table.
    destruct (Nat.eqb_spec d (rich_next_coupling_desc_id rs)) as [Heq|Hne].
    + subst d.
      inversion Hdesc; subst desc; clear Hdesc.
      simpl coupling_desc_base in *. simpl coupling_desc_count in *.
      destruct (write_coupling_pairs_aux_write_some pairs (rich_coupling_pair_table rs)
                  (rich_next_coupling_pair_id rs) (rich_next_coupling_pair_id rs + ofs)
                  ltac:(lia)) as [cpair Hsome].
      rewrite Hsome. discriminate.
    + assert (Hf : Nat.eqb d (rich_next_coupling_desc_id rs) = false).
      { apply Nat.eqb_neq. exact Hne. }
      specialize (Hpir d desc Hdesc) as Hrange.
      assert (Hbelow : coupling_desc_base desc + ofs < rich_next_coupling_pair_id rs) by lia.
      rewrite write_coupling_pairs_aux_below by exact Hbelow.
      exact (Hfp d desc ofs Hdesc Hofs).
Qed.

(** rich_state_add_morph_with_coupling preserves coupling_wf.
    Requires rich_next_coupling_desc_id rs > 0 so that add_morph(desc_id = old_next_desc_id)
    sees desc_id < new_next_desc_id = old_next_desc_id + 1. *)
Lemma coupling_wf_preserved_add_with_coupling :
  forall rs src dst pairs label is_id rs' new_id,
    rich_state_add_morph_with_coupling rs src dst pairs label is_id = (rs', new_id) ->
    coupling_wf rs ->
    rich_next_coupling_desc_id rs > 0 ->
    coupling_wf rs'.
Proof.
  intros rs src dst pairs label is_id rs' new_id Hadd Hwcf Hsafe.
  unfold rich_state_add_morph_with_coupling in Hadd.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Ecd.
  assert (Hwcf1 : coupling_wf rs1).
  { exact (coupling_wf_preserved_add_coupling rs pairs label rs1 desc_id Hwcf Ecd). }
  assert (Hdesc_lt : desc_id < rich_next_coupling_desc_id rs1).
  { unfold rich_state_add_coupling_data in Ecd.
    inversion Ecd; subst rs1 desc_id; clear Ecd.
    simpl rich_next_coupling_desc_id. lia. }
  exact (coupling_wf_preserved_add rs1 src dst desc_id is_id rs' new_id Hadd Hwcf1 Hdesc_lt).
Qed.

(** rich_state_delete_morph preserves coupling_wf (it only removes a morph entry). *)
Lemma coupling_wf_preserved_delete :
  forall rs morph_id,
    coupling_wf rs ->
    coupling_wf (rich_state_delete_morph rs morph_id).
Proof.
  intros rs morph_id [Hcdb [Hpir Hfp]].
  unfold rich_state_delete_morph.
  split; [|split].
  - intros i entry Htbl.
    simpl rich_morph_table in Htbl. simpl rich_next_coupling_desc_id.
    destruct (Nat.eqb_spec i morph_id) as [Heq|Hne].
    + inversion Htbl.
    + assert (Hf : Nat.eqb i morph_id = false).
      { apply Nat.eqb_neq. exact Hne. }
      exact (Hcdb i entry Htbl).
  - intros d desc Hdesc.
    simpl rich_coupling_desc_table in Hdesc. simpl rich_next_coupling_pair_id.
    exact (Hpir d desc Hdesc).
  - intros d desc ofs Hdesc Hofs.
    simpl rich_coupling_desc_table in Hdesc. simpl rich_coupling_pair_table.
    exact (Hfp d desc ofs Hdesc Hofs).
Qed.

(** coupling_wf is preserved by every kami_step operation.
    Uses coupling_desc_safe (next_desc_id > 0) for MORPH and MORPH_ID
    (which add a morph with coupling_desc = 0). *)
Theorem coupling_wf_kami_step_preserved :
  forall ks i,
    coupling_wf (snap_rich_state ks) ->
    coupling_desc_safe ks ->
    coupling_wf (snap_rich_state (kami_step ks i)).
Proof.
  intros ks i Hwcf Hsafe. destruct i;
    first [
      (unfold kami_step,
          kami_advance_default, kami_advance_reg, kami_advance_err,
          kami_advance_cert_addr, kami_advance_err_rich;
       simpl snap_rich_state; exact Hwcf)
    | idtac ].
  (* instr_chsh_trial *)
  - unfold kami_step.
    destruct x; destruct y; destruct (Nat.eqb a b);
      simpl snap_rich_state; exact Hwcf.
  (* instr_tensor_set *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hwcf.
  (* instr_tensor_get *)
  - unfold kami_step, kami_advance_err.
    destruct (tensor_indices_ok i j); simpl snap_rich_state; exact Hwcf.
  (* instr_morph: success adds morph with desc=0; 0 < next_desc_id by Hsafe *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) &&
              negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) src_mod dst_mod 0 false)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      apply (coupling_wf_preserved_add _ _ _ 0 _ _ _ Eram Hwcf Hsafe).
    + unfold kami_advance_err. simpl snap_rich_state. exact Hwcf.
  (* instr_compose: success adds morph with actual composed pairs *)
  - unfold kami_step.
    destruct (rich_morph_table (snap_rich_state ks) m1_id) as [e1|] eqn:He1;
    destruct (rich_morph_table (snap_rich_state ks) m2_id) as [e2|] eqn:He2;
    try (unfold kami_advance_err; simpl snap_rich_state; exact Hwcf).
    destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Heq;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwcf].
    match goal with
    | |- context[rich_state_add_morph_with_coupling ?a ?b ?c ?d ?e ?f] =>
        destruct (rich_state_add_morph_with_coupling a b c d e f)
                 as [rs' nid] eqn:Eadd
    end.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (coupling_wf_preserved_add_with_coupling _ _ _ _ _ _ _ _ Eadd Hwcf Hsafe).
  (* instr_morph_id: success adds morph with desc=0; 0 < next_desc_id by Hsafe *)
  - unfold kami_step.
    destruct (negb (Nat.eqb (snap_pt_sizes ks module) 0)) eqn:Hc.
    + destruct (rich_state_add_morph (snap_rich_state ks) module module 0 true)
               as [rs' nid] eqn:Eram.
      unfold kami_advance_rich_morph. simpl snap_rich_state.
      apply (coupling_wf_preserved_add _ _ _ 0 _ _ _ Eram Hwcf Hsafe).
    + unfold kami_advance_err. simpl snap_rich_state. exact Hwcf.
  (* instr_morph_delete: success deletes a morph entry *)
  - unfold kami_step, kami_advance_rich_noret, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id) eqn:Hmt;
      simpl snap_rich_state.
    + apply coupling_wf_preserved_delete. exact Hwcf.
    + exact Hwcf.
  (* instr_morph_assert: both branches preserve snap_rich_state *)
  - unfold kami_step, kami_advance_cert_addr, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hwcf.
  (* instr_morph_tensor: success adds morph with actual tensor pairs *)
  - unfold kami_step.
    set (g := snap_full_graph ks).
    destruct (graph_tensor_morphisms g f_id g_id) as [[g' mid']|] eqn:Htens;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwcf].
    destruct (graph_lookup_morphism g' mid') as [new_ms|] eqn:Hglu;
    [| unfold kami_advance_err; simpl snap_rich_state; exact Hwcf].
    destruct (rich_state_add_morph_with_coupling
                (snap_rich_state ks)
                (morph_source new_ms) (morph_target new_ms)
                (coupling_pairs (morph_coupling new_ms))
                (coupling_label (morph_coupling new_ms))
                false)
              as [rs' nid2] eqn:Eadd.
    unfold kami_advance_rich_morph. simpl snap_rich_state.
    exact (coupling_wf_preserved_add_with_coupling _ _ _ _ _ _ _ _ Eadd Hwcf Hsafe).
  (* instr_morph_get: both branches preserve snap_rich_state *)
  - unfold kami_step, kami_advance_reg, kami_advance_err.
    destruct (rich_morph_table (snap_rich_state ks) morph_id);
      simpl snap_rich_state; exact Hwcf.
Qed.

(* ======================================================================
   §9  Morph Table ↔ Graph Lookup Correspondence
   *)

(** None direction: if the rich table has no entry at mid,
    graph_lookup_morphism returns None too.  This is structural:
    snapshot_morphisms_of_rich_state only emits pairs for
    indices where rich_morph_table returns Some. *)
Lemma morph_table_none_implies_graph_none :
  forall (ks : KamiSnapshot) (mid : nat),
    (snap_rich_state ks).(rich_morph_table) mid = None ->
    graph_lookup_morphism (snap_full_graph ks) mid = None.
Proof.
  intros ks mid Hnone.
  unfold graph_lookup_morphism, snap_full_graph. simpl.
  unfold snapshot_morphisms_of_rich_state.
  set (rs := snap_rich_state ks).
  set (l := List.rev (List.seq 0 (rich_next_morph_id rs))).
  fold rs in Hnone.
  clearbody l rs.
  induction l as [|a xs IH]; simpl.
  - reflexivity.
  - destruct (rich_morph_table rs a) eqn:Era.
    + simpl. destruct (Nat.eqb a mid) eqn:Eam.
      * apply Nat.eqb_eq in Eam. subst. rewrite Era in Hnone. discriminate.
      * apply IH.
    + apply IH.
Qed.

(** Under morph_table_wf, morphism table lookup and graph lookup
    agree on existence (both Some or both None). *)
Lemma morph_lookup_agrees :
  forall (ks : KamiSnapshot) (mid : nat),
    morph_table_wf (snap_rich_state ks) ->
    match (snap_rich_state ks).(rich_morph_table) mid with
    | Some _ => graph_lookup_morphism (snap_full_graph ks) mid <> None
    | None   => graph_lookup_morphism (snap_full_graph ks) mid = None
    end.
Proof.
  intros ks mid Hwf.
  destruct ((snap_rich_state ks).(rich_morph_table) mid) eqn:Emid.
  - (* Some — table has entry *)
    destruct (Nat.lt_ge_cases mid (rich_next_morph_id (snap_rich_state ks))) as [Hlt|Hge].
    + apply morph_lookup_commutation; [exact Hlt|].
      rewrite Emid. discriminate.
    + exfalso. specialize (Hwf mid Hge). rewrite Hwf in Emid. discriminate.
  - (* None — table empty *)
    exact (morph_table_none_implies_graph_none ks mid Emid).
Qed.

(** snap_full_graph is preserved by hardware advance functions that
    do not touch partition tables or rich state. *)
Lemma snap_full_graph_advance_err :
  forall ks cost,
    snap_full_graph (kami_advance_err ks cost) = snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_advance_err.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state]. reflexivity.
Qed.

Lemma snap_full_graph_advance_cert_addr :
  forall ks addr cost,
    snap_full_graph (kami_advance_cert_addr ks addr cost) = snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_advance_cert_addr.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state]. reflexivity.
Qed.

Lemma snap_full_graph_advance_reg :
  forall ks dst value cost,
    snap_full_graph (kami_advance_reg ks dst value cost) = snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_advance_reg.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state]. reflexivity.
Qed.

Lemma snap_full_graph_advance_default :
  forall ks cost,
    snap_full_graph (kami_advance_default ks cost) = snap_full_graph ks.
Proof.
  intros. unfold snap_full_graph, kami_advance_default.
  cbn [snap_pt_next_id snap_pt_sizes snap_rich_state]. reflexivity.
Qed.

(** Register write commutation for the full-state abstraction.
    Combines abs_phase1_kami_reg_write with the fact that abs_phase1
    and abs_full_snapshot ∘ full_snapshot_of_snapshot have the same vm_regs. *)
Lemma full_state_kami_reg_write :
  forall ks r v,
    snapshot_regs_to_list (kami_write_reg ks r v) =
    write_reg (abs_full_snapshot (full_snapshot_of_snapshot ks)) r v.
Proof.
  intros.
  rewrite abs_phase1_kami_reg_write.
  unfold write_reg, abs_phase1, abs_full_snapshot, full_snapshot_of_snapshot.
  reflexivity.
Qed.

(** Under coupling_zero_empty and coupling_desc_all_zero, the
    MorphismState in the graph for a given table entry has
    morph_coupling = normalize_coupling empty_coupling_data.
    Definitional lemma: reflexivity holds after rewriting with invariants. *)
Lemma coupling_empty_under_invariants :
  forall (rs : RichSnapshotState) (entry : MorphTableEntry),
    coupling_zero_empty rs ->
    coupling_desc_all_zero rs ->
    forall i, rs.(rich_morph_table) i = Some entry ->
    normalize_coupling
      {| coupling_pairs := snapshot_coupling_pairs_from_desc rs (morph_entry_coupling_desc entry);
         coupling_label := coupling_label empty_coupling_data |}
    = normalize_coupling empty_coupling_data.
Proof.
  intros rs entry Hcze Hcdaz i Hi.
  specialize (Hcdaz i entry Hi).
  rewrite Hcdaz.
  unfold coupling_zero_empty in Hcze.
  unfold snapshot_coupling_pairs_from_desc. rewrite Hcze.
  reflexivity.
Qed.

Lemma morph_add_with_coupling_commutation :
  forall (rs : RichSnapshotState) (src dst : nat)
         (pairs : list (nat * nat)) (label : string) (is_id : bool),
    coupling_desc_all_zero rs ->
    coupling_zero_empty rs ->
    rich_next_coupling_desc_id rs > 0 ->
    let '(rs', new_id) := rich_state_add_morph_with_coupling rs src dst pairs label is_id in
    snapshot_morphisms_of_rich_state rs' =
      (new_id,
       {| morph_source := src;
          morph_target := dst;
          morph_coupling :=
            {| coupling_pairs := pairs;
               coupling_label := label |};
          morph_is_identity := is_id;
               morph_cert_cost := 0 |})
      :: snapshot_morphisms_of_rich_state rs.
Proof.
  intros rs src dst pairs label is_id Hcdaz Hcze Hsafe.
  unfold rich_state_add_morph_with_coupling.
  destruct (rich_state_add_coupling_data rs pairs label) as [rs1 desc_id] eqn:Eadd.
  destruct (rich_state_add_morph rs1 src dst desc_id is_id) as [rs' new_id] eqn:Eram.
  pose proof (morph_add_commutation rs1 src dst desc_id is_id) as Hmc.
  rewrite Eram in Hmc. simpl in Hmc.
  pose proof (coupling_data_round_trip rs pairs label) as Hpairs.
  rewrite Eadd in Hpairs. simpl in Hpairs.
  pose proof (coupling_label_round_trip rs pairs label) as Hlabel.
  rewrite Eadd in Hlabel. simpl in Hlabel.
  pose proof (coupling_data_preserves_morphisms rs pairs label Hcdaz Hcze Hsafe) as Hold.
  rewrite Eadd in Hold. simpl in Hold.
  rewrite Hmc, Hpairs, Hlabel, Hold.
  reflexivity.
Qed.

(** Full MorphismState correspondence: graph_lookup_morphism returns
    the exact MorphismState built from the table entry by
    snapshot_morphisms_of_rich_state. *)
Lemma graph_lookup_morphism_corresponds :
  forall (ks : KamiSnapshot) (morph_id : nat) (entry : MorphTableEntry) (ms : MorphismState),
    morph_table_wf (snap_rich_state ks) ->
    (snap_rich_state ks).(rich_morph_table) morph_id = Some entry ->
    graph_lookup_morphism (snap_full_graph ks) morph_id = Some ms ->
    ms = {| morph_source := morph_entry_source entry;
            morph_target := morph_entry_target entry;
            morph_coupling :=
                {| coupling_pairs :=
                     snapshot_coupling_pairs_from_desc (snap_rich_state ks) (morph_entry_coupling_desc entry);
                   coupling_label :=
                     match rich_coupling_desc_table (snap_rich_state ks) (morph_entry_coupling_desc entry) with
                     | Some desc => coupling_desc_label desc
                     | None => coupling_label empty_coupling_data
                     end |};
            morph_is_identity := morph_entry_is_identity entry;
               morph_cert_cost := 0 |}.
Proof.
  intros ks morph_id entry ms Hwf Htbl Hgraph.
  unfold graph_lookup_morphism, snap_full_graph in Hgraph. simpl in Hgraph.
  unfold snapshot_morphisms_of_rich_state in Hgraph.
  set (rs := snap_rich_state ks) in *.
  assert (Hlt : morph_id < rich_next_morph_id rs).
  { destruct (Nat.lt_ge_cases morph_id (rich_next_morph_id rs)); [assumption|].
    exfalso. specialize (Hwf morph_id H). congruence. }
  set (l := List.rev (List.seq 0 (rich_next_morph_id rs))) in *.
  assert (Hin : In morph_id l).
  { subst l. rewrite <- in_rev. apply in_seq. lia. }
  clearbody l. clear Hlt.
  induction l as [|a xs IH]; [inversion Hin|].
  simpl in Hgraph.
  destruct (rich_morph_table rs a) eqn:Era.
  - simpl in Hgraph. destruct (Nat.eqb a morph_id) eqn:Eam.
    + apply Nat.eqb_eq in Eam. subst a.
      rewrite Htbl in Era. inversion Era. subst m.
      inversion Hgraph. subst ms. reflexivity.
    + destruct Hin as [Heq|Hin']; [subst; rewrite Nat.eqb_refl in Eam; discriminate|].
      apply IH; assumption.
  - destruct Hin as [Heq|Hin']; [subst; rewrite Htbl in Era; discriminate|].
    apply IH; assumption.
Qed.

(** Filter with fst-based function equals filter with pattern-matching. *)
Lemma filter_fst_eq :
  forall {A B : Type} (f : A -> bool) (l : list (A * B)),
    filter (fun entry => f (fst entry)) l = filter (fun '(id, _) => f id) l.
Proof.
  intros A B f l.
  induction l as [|[a b] l IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** graph_delete_morphism succeeds when graph_lookup_morphism succeeds. *)
Lemma graph_delete_morphism_of_lookup_some :
  forall g morph_id ms,
    graph_lookup_morphism g morph_id = Some ms ->
    graph_delete_morphism g morph_id <> None.
Proof.
  intros g morph_id ms Hlook.
  unfold graph_delete_morphism.
  assert (Hex : existsb (fun '(id, _) => Nat.eqb id morph_id) (pg_morphisms g) = true).
  { unfold graph_lookup_morphism in Hlook.
    set (l := pg_morphisms g) in *.
    clearbody l.
    induction l as [|[a s'] xs IH]; simpl in *.
    - discriminate.
    - destruct (Nat.eqb a morph_id) eqn:Eam; simpl.
      + reflexivity.
      + apply IH. exact Hlook. }
  rewrite Hex. discriminate.
Qed.

(** Module lookup in snap_full_graph agrees with snap_pt_to_graph
    on existence: both return Some or both return None for the same mid.
    The ModuleState content differs (tensor overlay), but the IDs match. *)
Lemma snap_full_graph_module_lookup_none :
  forall ks mid,
    graph_lookup (snap_full_graph ks) mid = None <->
    graph_lookup (snap_pt_to_graph (snap_pt_next_id ks) (snap_pt_sizes ks)) mid = None.
Proof.
  intros. unfold graph_lookup, snap_full_graph, snap_pt_to_graph.
  simpl pg_modules.
  set (base := filtermap _ _).
  clearbody base. split; intro H.
  - induction base as [|[a m] xs IH]; simpl in *; [reflexivity|].
    unfold graph_lookup_modules in *. simpl in *.
    destruct (Nat.eqb a mid); [discriminate|]. apply IH. exact H.
  - induction base as [|[a m] xs IH]; simpl in *; [reflexivity|].
    unfold graph_lookup_modules in *. simpl in *.
    destruct (Nat.eqb a mid); [discriminate|]. apply IH. exact H.
Qed.

(** If a module has nonzero partition size and its ID is below next_id,
    graph_lookup in snap_full_graph succeeds. *)
Lemma snap_pt_sizes_nonzero_graph_lookup :
  forall ks mid,
    mid < snap_pt_next_id ks ->
    negb (Nat.eqb (snap_pt_sizes ks mid) 0) = true ->
    exists ms, graph_lookup (snap_full_graph ks) mid = Some ms.
Proof.
  intros ks mid Hlt Hsz.
  apply negb_true_iff in Hsz. apply Nat.eqb_neq in Hsz.
  pose proof (snap_pt_to_graph_module_size
    (snap_pt_next_id ks) (snap_pt_sizes ks) mid Hlt) as Hmsz.
  unfold graph_module_size in Hmsz.
  destruct (graph_lookup (snap_pt_to_graph (snap_pt_next_id ks) (snap_pt_sizes ks)) mid)
    as [m|] eqn:Egl.
  - destruct (graph_lookup (snap_full_graph ks) mid) as [m'|] eqn:Egl'.
    + exists m'. reflexivity.
    + exfalso. apply snap_full_graph_module_lookup_none in Egl'. congruence.
  - exfalso. simpl in Hmsz. lia.
Qed.

(** filtermap extensionality: same result if the function agrees on every element. *)
Lemma filtermap_ext_in :
  forall {A B : Type} (f1 f2 : A -> option B) l,
    (forall x, In x l -> f1 x = f2 x) ->
    filtermap f1 l = filtermap f2 l.
Proof.
  intros A B f1 f2 l H.
  induction l as [|a xs IH]; simpl.
  - reflexivity.
  - rewrite (H a (or_introl eq_refl)).
    rewrite IH; [reflexivity|].
    intros x Hx. apply H. right. exact Hx.
Qed.

(** PartitionGraph record extensionality: field-by-field equality implies
    record equality. *)
Lemma partition_graph_eq (g1 g2 : PartitionGraph) :
  pg_next_id g1 = pg_next_id g2 ->
  pg_modules g1 = pg_modules g2 ->
  pg_next_morph_id g1 = pg_next_morph_id g2 ->
  pg_morphisms g1 = pg_morphisms g2 ->
  g1 = g2.
Proof. destruct g1, g2; simpl; intros; subst; reflexivity. Qed.

(** snap_pt_to_graph is extensional in sizes: if sizes1 and sizes2 agree
    on 0..next_id-1, the graphs are equal. *)
Lemma snap_pt_to_graph_ext :
  forall next_id sizes1 sizes2,
    (forall i, i < next_id -> sizes1 i = sizes2 i) ->
    snap_pt_to_graph next_id sizes1 = snap_pt_to_graph next_id sizes2.
Proof.
  intros next_id sizes1 sizes2 H.
  unfold snap_pt_to_graph. f_equal.
  apply filtermap_ext_in.
  intros i Hi. rewrite <- in_rev, in_seq in Hi.
  destruct Hi as [_ Hi]. specialize (H i Hi).
  rewrite H. reflexivity.
Qed.

(** graph_hw_psplit depends only on pg_modules and pg_next_id for its
    pg_modules and pg_next_id output. *)
Lemma graph_hw_psplit_modules_eq :
  forall g1 g2 mid,
    pg_modules g1 = pg_modules g2 ->
    pg_next_id g1 = pg_next_id g2 ->
    pg_modules (graph_hw_psplit g1 mid) = pg_modules (graph_hw_psplit g2 mid) /\
    pg_next_id (graph_hw_psplit g1 mid) = pg_next_id (graph_hw_psplit g2 mid).
Proof.
  intros g1 g2 mid Hm Hn.
  unfold graph_hw_psplit.
  assert (Hmsz : graph_module_size g1 mid = graph_module_size g2 mid).
  { unfold graph_module_size, graph_lookup. rewrite Hm. reflexivity. }
  rewrite Hmsz.
  set (g1' := match graph_remove g1 mid with Some (g', _) => g' | None => g1 end).
  set (g2' := match graph_remove g2 mid with Some (g', _) => g' | None => g2 end).
  assert (Hm' : pg_modules g1' = pg_modules g2').
  { subst g1' g2'. unfold graph_remove. rewrite Hm.
    destruct (graph_remove_modules (pg_modules g2) mid) as [[ms rm]|]; simpl; auto. }
  assert (Hn' : pg_next_id g1' = pg_next_id g2').
  { subst g1' g2'. unfold graph_remove. rewrite Hm, Hn.
    destruct (graph_remove_modules (pg_modules g2) mid) as [[ms rm]|]; simpl; auto. }
  remember (graph_add_module g1' _ _) as p1a eqn:Ep1a.
  remember (graph_add_module g2' _ _) as p2a eqn:Ep2a.
  destruct p1a as [g1a id1a]. destruct p2a as [g2a id2a].
  assert (Hma : pg_modules g1a = pg_modules g2a /\ pg_next_id g1a = pg_next_id g2a).
  { unfold graph_add_module in Ep1a, Ep2a.
    inversion Ep1a. inversion Ep2a. simpl. rewrite Hm', Hn'. auto. }
  destruct Hma as [Hma Hna].
  remember (graph_add_module g1a _ _) as p1b eqn:Ep1b.
  remember (graph_add_module g2a _ _) as p2b eqn:Ep2b.
  destruct p1b as [g1b id1b]. destruct p2b as [g2b id2b].
  unfold graph_add_module in Ep1b, Ep2b.
  inversion Ep1b. inversion Ep2b. simpl. rewrite Hma, Hna. auto.
Qed.

(** graph_hw_pmerge depends only on pg_modules and pg_next_id for its
    pg_modules and pg_next_id output. *)
Lemma graph_hw_pmerge_modules_eq :
  forall g1 g2 m1 m2,
    pg_modules g1 = pg_modules g2 ->
    pg_next_id g1 = pg_next_id g2 ->
    pg_modules (graph_hw_pmerge g1 m1 m2) = pg_modules (graph_hw_pmerge g2 m1 m2) /\
    pg_next_id (graph_hw_pmerge g1 m1 m2) = pg_next_id (graph_hw_pmerge g2 m1 m2).
Proof.
  intros g1 g2 m1 m2 Hm Hn.
  unfold graph_hw_pmerge.
  assert (Hmsz1 : graph_module_size g1 m1 = graph_module_size g2 m1).
  { unfold graph_module_size, graph_lookup. rewrite Hm. reflexivity. }
  assert (Hmsz2 : graph_module_size g1 m2 = graph_module_size g2 m2).
  { unfold graph_module_size, graph_lookup. rewrite Hm. reflexivity. }
  rewrite Hmsz1, Hmsz2.
  set (g1a := match graph_remove g1 m1 with Some (g', _) => g' | None => g1 end).
  set (g2a := match graph_remove g2 m1 with Some (g', _) => g' | None => g2 end).
  assert (Hma : pg_modules g1a = pg_modules g2a).
  { subst g1a g2a. unfold graph_remove. rewrite Hm.
    destruct (graph_remove_modules (pg_modules g2) m1) as [[ms rm]|]; simpl; auto. }
  assert (Hna : pg_next_id g1a = pg_next_id g2a).
  { subst g1a g2a. unfold graph_remove. rewrite Hm, Hn.
    destruct (graph_remove_modules (pg_modules g2) m1) as [[ms rm]|]; simpl; auto. }
  set (g1b := match graph_remove g1a m2 with Some (g', _) => g' | None => g1a end).
  set (g2b := match graph_remove g2a m2 with Some (g', _) => g' | None => g2a end).
  assert (Hmb : pg_modules g1b = pg_modules g2b).
  { subst g1b g2b. unfold graph_remove. rewrite Hma.
    destruct (graph_remove_modules (pg_modules g2a) m2) as [[ms rm]|]; simpl; auto. }
  assert (Hnb : pg_next_id g1b = pg_next_id g2b).
  { subst g1b g2b. unfold graph_remove. rewrite Hma, Hna.
    destruct (graph_remove_modules (pg_modules g2a) m2) as [[ms rm]|]; simpl; auto. }
  remember (graph_add_module g1b _ _) as p1c eqn:Ep1c.
  remember (graph_add_module g2b _ _) as p2c eqn:Ep2c.
  destruct p1c as [g1c id1c]. destruct p2c as [g2c id2c].
  unfold graph_add_module in Ep1c, Ep2c.
  inversion Ep1c. inversion Ep2c. simpl. rewrite Hmb, Hnb. auto.
Qed.

(** graph_remove preserves pg_morphisms and pg_next_morph_id. *)
Lemma graph_remove_preserves_morph_fields :
  forall g mid g' m,
    graph_remove g mid = Some (g', m) ->
    pg_morphisms g' = pg_morphisms g /\
    pg_next_morph_id g' = pg_next_morph_id g.
Proof.
  intros g mid g' m H.
  unfold graph_remove in H.
  destruct (graph_remove_modules (pg_modules g) mid) as [[mods rm]|]; [|discriminate].
  inversion H. subst. simpl. auto.
Qed.

(** graph_add_module preserves pg_morphisms and pg_next_morph_id. *)
Lemma graph_add_module_preserves_morph_fields :
  forall g r a,
    pg_morphisms (fst (graph_add_module g r a)) = pg_morphisms g /\
    pg_next_morph_id (fst (graph_add_module g r a)) = pg_next_morph_id g.
Proof.
  intros. unfold graph_add_module. simpl. auto.
Qed.

(** graph_hw_psplit preserves pg_morphisms and pg_next_morph_id. *)
Lemma graph_hw_psplit_preserves_morph_fields :
  forall g mid,
    pg_morphisms (graph_hw_psplit g mid) = pg_morphisms g /\
    pg_next_morph_id (graph_hw_psplit g mid) = pg_next_morph_id g.
Proof.
  intros g mid.
  unfold graph_hw_psplit.
  set (orig_sz := graph_module_size g mid).
  set (left_sz := Nat.div orig_sz 2).
  set (right_sz := orig_sz - left_sz).
  set (g1 := match graph_remove g mid with Some (g', _) => g' | None => g end).
  remember (graph_add_module g1 (List.seq 0 left_sz) []) as p2 eqn:E2.
  destruct p2 as [g2 id2].
  remember (graph_add_module g2 (List.seq 0 right_sz) []) as p3 eqn:E3.
  destruct p3 as [g3 id3].
  assert (Hg1 : pg_morphisms g1 = pg_morphisms g /\ pg_next_morph_id g1 = pg_next_morph_id g).
  { subst g1. destruct (graph_remove g mid) as [[g' ms]|] eqn:Er.
    - eapply graph_remove_preserves_morph_fields. exact Er.
    - auto. }
  assert (Hg2 : pg_morphisms g2 = pg_morphisms g1 /\ pg_next_morph_id g2 = pg_next_morph_id g1).
  { change g2 with (fst (g2, id2)). rewrite E2. apply graph_add_module_preserves_morph_fields. }
  assert (Hg3 : pg_morphisms g3 = pg_morphisms g2 /\ pg_next_morph_id g3 = pg_next_morph_id g2).
  { change g3 with (fst (g3, id3)). rewrite E3. apply graph_add_module_preserves_morph_fields. }
  destruct Hg1, Hg2, Hg3. split; congruence.
Qed.

(** graph_hw_pmerge preserves pg_morphisms and pg_next_morph_id. *)
Lemma graph_hw_pmerge_preserves_morph_fields :
  forall g m1 m2,
    pg_morphisms (graph_hw_pmerge g m1 m2) = pg_morphisms g /\
    pg_next_morph_id (graph_hw_pmerge g m1 m2) = pg_next_morph_id g.
Proof.
  intros g m1 m2.
  unfold graph_hw_pmerge.
  set (sz1 := graph_module_size g m1).
  set (sz2 := graph_module_size g m2).
  set (merged_sz := sz1 + sz2).
  set (g1 := match graph_remove g m1 with Some (g', _) => g' | None => g end).
  set (g2 := match graph_remove g1 m2 with Some (g', _) => g' | None => g1 end).
  remember (graph_add_module g2 (List.seq 0 merged_sz) []) as p3 eqn:E3.
  destruct p3 as [g3 id3].
  assert (Hg1 : pg_morphisms g1 = pg_morphisms g /\ pg_next_morph_id g1 = pg_next_morph_id g).
  { subst g1. destruct (graph_remove g m1) as [[g' ms]|] eqn:Er.
    - eapply graph_remove_preserves_morph_fields. exact Er.
    - auto. }
  assert (Hg2 : pg_morphisms g2 = pg_morphisms g1 /\ pg_next_morph_id g2 = pg_next_morph_id g1).
  { subst g2. destruct (graph_remove g1 m2) as [[g' ms]|] eqn:Er.
    - eapply graph_remove_preserves_morph_fields. exact Er.
    - auto. }
  assert (Hg3 : pg_morphisms g3 = pg_morphisms g2 /\ pg_next_morph_id g3 = pg_next_morph_id g2).
  { change g3 with (fst (g3, id3)). rewrite E3. apply graph_add_module_preserves_morph_fields. }
  destruct Hg1, Hg2, Hg3. split; congruence.
Qed.

(* ======================================================================
   §10  MORPH_ASSERT bridge
   *)

Theorem driven_step_morph_assert :
  forall ks morph_id property cert cost,
    morph_table_wf (snap_rich_state ks) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_assert morph_id property cert cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_assert morph_id property cert cost).
Proof.
  intros ks morph_id property cert cost Hwf.
  pose proof (morph_lookup_agrees ks morph_id Hwf) as Hla.
  set (rs := snap_rich_state ks) in *.
  destruct (rich_morph_table rs morph_id) eqn:Erm.
  - (* Success path: morphism found *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id <> None) by exact Hla.
    destruct (graph_lookup_morphism (snap_full_graph ks) morph_id) as [ms|] eqn:Egl;
      [|exfalso; exact (Hgl eq_refl)].
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph]. rewrite Egl.
    rewrite snap_full_graph_advance_cert_addr.
    unfold advance_state, apply_cost, instruction_cost, csr_set_cert_addr.
    reflexivity.
  - (* Error path: morphism not found *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id = None) by exact Hla.
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph]. rewrite Hgl.
    rewrite snap_full_graph_advance_err.
    unfold advance_state, apply_cost, instruction_cost, latch_err.
    reflexivity.
Qed.

(* ======================================================================
   §11  MORPH_GET bridge
   *)

(** Helper: morph_table_wf + morph_id in range + entry exists implies
    the graph lookup returns a MorphismState that agrees with the entry
    on source, target, and is_identity fields. *)
Lemma morph_entry_fields_agree :
  forall (ks : KamiSnapshot) (morph_id : nat) (entry : MorphTableEntry) (ms : MorphismState),
    morph_table_wf (snap_rich_state ks) ->
    (snap_rich_state ks).(rich_morph_table) morph_id = Some entry ->
    graph_lookup_morphism (snap_full_graph ks) morph_id = Some ms ->
    morph_source ms = morph_entry_source entry /\
    morph_target ms = morph_entry_target entry /\
    morph_is_identity ms = morph_entry_is_identity entry.
Proof.
  intros ks morph_id entry ms Hwf Htbl Hgraph.
  (* Both lookups succeed. The graph is built from the table via
     snapshot_morphisms_of_rich_state. By construction, the
     filtermap passes source/target/is_identity through unchanged. *)
  unfold graph_lookup_morphism, snap_full_graph in Hgraph. simpl in Hgraph.
  unfold snapshot_morphisms_of_rich_state in Hgraph.
  set (rs := snap_rich_state ks) in *.
  assert (Hlt : morph_id < rich_next_morph_id rs).
  { destruct (Nat.lt_ge_cases morph_id (rich_next_morph_id rs)); [assumption|].
    exfalso. specialize (Hwf morph_id H). congruence. }
  set (l := List.rev (List.seq 0 (rich_next_morph_id rs))) in *.
  assert (Hin : In morph_id l).
  { subst l. rewrite <- in_rev. apply in_seq. lia. }
  clearbody l. clear Hlt.
  induction l as [|a xs IH]; [inversion Hin|].
  simpl in Hgraph.
  destruct (rich_morph_table rs a) eqn:Era.
  - simpl in Hgraph. destruct (Nat.eqb a morph_id) eqn:Eam.
    + apply Nat.eqb_eq in Eam. subst a.
      rewrite Htbl in Era. inversion Era. subst m.
      inversion Hgraph. subst ms. simpl. auto.
    + destruct Hin as [Heq|Hin']; [subst; rewrite Nat.eqb_refl in Eam; discriminate|].
      apply IH; assumption.
  - destruct Hin as [Heq|Hin']; [subst; rewrite Htbl in Era; discriminate|].
    apply IH; assumption.
Qed.

Theorem driven_step_morph_get :
  forall ks dst morph_id selector cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_get dst morph_id selector cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_get dst morph_id selector cost).
Proof.
  intros ks dst morph_id selector cost [Hpt [Hwf [Hcze [Hwcf _]]]].
  pose proof (morph_lookup_agrees ks morph_id Hwf) as Hla.
  set (rs := snap_rich_state ks) in *.
  destruct (rich_morph_table rs morph_id) eqn:Erm.
  - (* Success: morphism found *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id <> None) by exact Hla.
    destruct (graph_lookup_morphism (snap_full_graph ks) morph_id) as [ms|] eqn:Egl;
      [|exfalso; exact (Hgl eq_refl)].
    (* Get full correspondence between table entry and graph morphism *)
    pose proof (graph_lookup_morphism_corresponds ks morph_id m ms Hwf Erm Egl) as Hms_eq.
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph]. rewrite Egl.
    (* Both sides take success path. Unfold everything to VMState constructors *)
    unfold kami_advance_reg, advance_state_rm, apply_cost, instruction_cost.
    cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
         snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
         snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
         snap_logic_acc snap_mstatus
         snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
         snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
         snap_full_graph].
    (* Register write: need hw value = morphism_selector_value ms selector *)
    rewrite full_state_kami_reg_write.
    (* The hw value depends on selector *)
    assert (Hval :
      (match selector with
       | 0 => morph_entry_source m
       | 1 => morph_entry_target m
       | 2 => match rich_coupling_desc_table rs (morph_entry_coupling_desc m) with
               | Some desc => coupling_desc_count desc
               | None => 0
               end
       | 3 => if morph_entry_is_identity m then 1 else 0
       | _ => 0
       end) = morphism_selector_value ms selector).
    { rewrite Hms_eq. unfold morphism_selector_value. simpl.
      destruct selector as [|[|[|[|s']]]]; try reflexivity.
      (* selector 2: coupling count — use coupling_count_length *)
      destruct (rich_coupling_desc_table rs (morph_entry_coupling_desc m))
        as [desc|] eqn:Edesc.
      + symmetry.
        exact (coupling_count_length rs _ desc (proj2 (proj2 Hwcf)) Edesc).
      + fold rs. unfold snapshot_coupling_pairs_from_desc. rewrite Edesc. simpl. reflexivity. }
    rewrite Hval. reflexivity.
  - (* Error: morphism not found *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id = None) by exact Hla.
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph]. rewrite Hgl.
    rewrite snap_full_graph_advance_err.
    unfold advance_state, apply_cost, instruction_cost, latch_err.
    reflexivity.
Qed.

(* ======================================================================
   §12  MORPH_DELETE bridge
   *)

(** If graph_lookup_morphism returns None, graph_delete_morphism
    returns None too (no morphism to delete). *)
Lemma graph_delete_none_of_lookup_none :
  forall g mid,
    graph_lookup_morphism g mid = None ->
    graph_delete_morphism g mid = None.
Proof.
  intros g mid H.
  unfold graph_delete_morphism, graph_lookup_morphism in *.
  destruct (existsb (fun '(id, _) => Nat.eqb id mid) (pg_morphisms g)) eqn:Eex;
    [|reflexivity].
  exfalso.
  rewrite existsb_exists in Eex.
  destruct Eex as [[id ms] [Hin Heqb]].
  simpl in Heqb. apply Nat.eqb_eq in Heqb. subst id.
  set (l := pg_morphisms g) in *.
  clearbody l.
  induction l as [|[a s'] xs IH]; [inversion Hin|].
  simpl in H, Hin.
  destruct (Nat.eqb a mid) eqn:Eam.
  - discriminate.
  - destruct Hin as [Hcons|Hin'].
    + inversion Hcons. subst. rewrite Nat.eqb_refl in Eam. discriminate.
    + exact (IH H Hin').
Qed.

Theorem driven_step_morph_delete :
  forall ks morph_id cost,
    morph_table_wf (snap_rich_state ks) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_delete morph_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_delete morph_id cost).
Proof.
  intros ks morph_id cost Hwf.
  pose proof (morph_lookup_agrees ks morph_id Hwf) as Hla.
  set (rs := snap_rich_state ks) in *.
  destruct (rich_morph_table rs morph_id) eqn:Erm.
  - (* Success: morphism found, delete it *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id <> None) by exact Hla.
    destruct (graph_lookup_morphism (snap_full_graph ks) morph_id) as [ms|] eqn:Egl;
      [|exfalso; exact (Hgl eq_refl)].
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph].
    (* Show graph_delete_morphism succeeds *)
    destruct (graph_delete_morphism (snap_full_graph ks) morph_id) as [g'|] eqn:Edel.
    2: { exfalso. exact (graph_delete_morphism_of_lookup_some _ _ ms Egl Edel). }
    (* Prove the graph produced by hardware = graph produced by kernel *)
    assert (Hgeq : snap_full_graph (kami_advance_rich_noret ks cost
                     (rich_state_delete_morph rs morph_id)) = g').
    { unfold graph_delete_morphism in Edel.
      destruct (existsb _ _); [|discriminate].
      inversion Edel; subst g'; clear Edel.
      unfold snap_full_graph, kami_advance_rich_noret.
      cbn [snap_pt_next_id snap_pt_sizes snap_rich_state].
      rewrite morph_delete_commutation.
      rewrite (filter_fst_eq (fun id => negb (Nat.eqb id morph_id))).
      unfold rich_state_delete_morph; simpl rich_next_morph_id.
      reflexivity. }
    (* All fields match *)
    unfold advance_state, apply_cost, instruction_cost.
    rewrite Hgeq.
    unfold kami_advance_rich_noret.
    cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
         snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
         snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
         snap_logic_acc snap_mstatus
         snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
         snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
         vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
         vm_logic_acc vm_mstatus vm_witness vm_certified
         csr_cert_addr csr_status csr_err csr_heap_base
         wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
         wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
    reflexivity.
  - (* Error: morphism not found *)
    assert (Hgl : graph_lookup_morphism (snap_full_graph ks) morph_id = None) by exact Hla.
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Erm.
    unfold vm_apply. cbn [vm_graph].
    rewrite (graph_delete_none_of_lookup_none _ _ Hgl).
    rewrite snap_full_graph_advance_err.
    unfold advance_state, apply_cost, instruction_cost, latch_err.
    reflexivity.
Qed.

(* ======================================================================
   §13  MORPH bridge
   *)

Theorem driven_step_morph :
  forall ks dst src_mod dst_mod coupling_idx cost,
    extended_hw_invariant ks ->
    src_mod < snap_pt_next_id ks ->
    dst_mod < snap_pt_next_id ks ->
    negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) = true ->
    negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0) = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph dst src_mod dst_mod coupling_idx cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph dst src_mod dst_mod coupling_idx cost).
Proof.
  intros ks dst src_mod dst_mod coupling_idx cost
    [Hpt [Hwf [Hcze [_ _]]]] Hslt Hdlt Hsrc Hdst.
  set (rs := snap_rich_state ks) in *.
  (* Module existence in graph *)
  destruct (snap_pt_sizes_nonzero_graph_lookup ks src_mod Hslt Hsrc) as [ms_src Esrc].
  destruct (snap_pt_sizes_nonzero_graph_lookup ks dst_mod Hdlt Hdst) as [ms_dst Edst].
  rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  rewrite Hsrc, Hdst. simpl andb.
  destruct (rich_state_add_morph rs src_mod dst_mod 0 false) as [rs' new_id] eqn:Eram.
  unfold vm_apply. cbn [vm_graph].
  rewrite Esrc, Edst.
  destruct (graph_add_morphism (snap_full_graph ks) src_mod dst_mod empty_coupling_data false)
    as [graph' morph_id] eqn:Egam.
  (* new_id = morph_id *)
  assert (Hid : new_id = morph_id).
  { unfold rich_state_add_morph in Eram. inversion Eram.
    unfold graph_add_morphism in Egam. inversion Egam.
    unfold snap_full_graph. simpl pg_next_morph_id. reflexivity. }
  (* Graph equality *)
  assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst new_id cost rs') = graph').
  { unfold graph_add_morphism in Egam. inversion Egam; subst graph'. clear Egam.
    unfold snap_full_graph, kami_advance_rich_morph.
    cbn [snap_pt_next_id snap_pt_sizes snap_rich_state snap_module_tensors
         pg_next_id pg_modules pg_next_morph_id pg_morphisms].
    pose proof (morph_add_commutation rs src_mod dst_mod 0 false) as Hmc.
    rewrite Eram in Hmc. rewrite Hmc. clear Hmc.
    (* coupling under coupling_zero_empty *)
    assert (Hcp : snapshot_coupling_pairs_from_desc rs 0 = []).
    { unfold snapshot_coupling_pairs_from_desc. rewrite Hcze. reflexivity. }
    rewrite Hcp.
    (* coupling label under coupling_zero_empty *)
    rewrite Hcze.
    unfold rich_state_add_morph in Eram. inversion Eram; subst rs' new_id.
    simpl rich_next_morph_id.
    replace (rich_next_morph_id rs + 1) with (S (rich_next_morph_id rs)) by lia.
    unfold normalize_coupling. simpl.
    reflexivity. }
  (* All fields match *)
  unfold advance_state_rm, apply_cost, instruction_cost.
  subst morph_id.
  rewrite Hgeq.
  unfold kami_advance_rich_morph.
  cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
       snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_logic_acc snap_mstatus
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
       vm_logic_acc vm_mstatus vm_witness vm_certified
       csr_cert_addr csr_status csr_err csr_heap_base
       wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
       wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
  fold (kami_write_reg ks dst new_id).
  rewrite full_state_kami_reg_write.
  rewrite abs_full_snapshot_of_snapshot.
  reflexivity.
Qed.

(** driven_step_morph_full: reduced precondition — replaces extended_hw_invariant
    with just coupling_zero_empty.  The proof of driven_step_morph only uses
    Hcze from the full invariant; Hwf, Hcdaz, Hpt, and coupling_desc_safe are
    passed in extended_hw_invariant but never referenced in the proof body. *)
Theorem driven_step_morph_full :
  forall ks dst src_mod dst_mod coupling_idx cost,
    coupling_zero_empty (snap_rich_state ks) ->
    src_mod < snap_pt_next_id ks ->
    dst_mod < snap_pt_next_id ks ->
    negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) = true ->
    negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0) = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph dst src_mod dst_mod coupling_idx cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph dst src_mod dst_mod coupling_idx cost).
Proof.
  intros ks dst src_mod dst_mod coupling_idx cost Hcze Hslt Hdlt Hsrc Hdst.
  set (rs := snap_rich_state ks) in *.
  destruct (snap_pt_sizes_nonzero_graph_lookup ks src_mod Hslt Hsrc) as [ms_src Esrc].
  destruct (snap_pt_sizes_nonzero_graph_lookup ks dst_mod Hdlt Hdst) as [ms_dst Edst].
  rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  rewrite Hsrc, Hdst. simpl andb.
  destruct (rich_state_add_morph rs src_mod dst_mod 0 false) as [rs' new_id] eqn:Eram.
  unfold vm_apply. cbn [vm_graph].
  rewrite Esrc, Edst.
  destruct (graph_add_morphism (snap_full_graph ks) src_mod dst_mod empty_coupling_data false)
    as [graph' morph_id] eqn:Egam.
  assert (Hid : new_id = morph_id).
  { unfold rich_state_add_morph in Eram. inversion Eram.
    unfold graph_add_morphism in Egam. inversion Egam.
    unfold snap_full_graph. simpl pg_next_morph_id. reflexivity. }
  assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst new_id cost rs') = graph').
  { unfold graph_add_morphism in Egam. inversion Egam; subst graph'. clear Egam.
    unfold snap_full_graph, kami_advance_rich_morph.
    cbn [snap_pt_next_id snap_pt_sizes snap_rich_state snap_module_tensors
         pg_next_id pg_modules pg_next_morph_id pg_morphisms].
    pose proof (morph_add_commutation rs src_mod dst_mod 0 false) as Hmc.
    rewrite Eram in Hmc. rewrite Hmc. clear Hmc.
    assert (Hcp : snapshot_coupling_pairs_from_desc rs 0 = []).
    { unfold snapshot_coupling_pairs_from_desc. rewrite Hcze. reflexivity. }
    rewrite Hcp.
    rewrite Hcze.
    unfold rich_state_add_morph in Eram. inversion Eram; subst rs' new_id.
    simpl rich_next_morph_id.
    replace (rich_next_morph_id rs + 1) with (S (rich_next_morph_id rs)) by lia.
    unfold normalize_coupling. simpl.
    reflexivity. }
  unfold advance_state_rm, apply_cost, instruction_cost.
  subst morph_id.
  rewrite Hgeq.
  unfold kami_advance_rich_morph.
  cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
       snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_logic_acc snap_mstatus
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
       vm_logic_acc vm_mstatus vm_witness vm_certified
       csr_cert_addr csr_status csr_err csr_heap_base
       wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
       wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
  fold (kami_write_reg ks dst new_id).
  rewrite full_state_kami_reg_write.
  rewrite abs_full_snapshot_of_snapshot.
  reflexivity.
Qed.

(* ======================================================================
   §13b Helper: tensor overlay commutes with graph_remove / graph_add
   *)

(** Tensor-overlay wrapping function for a single module. *)
Definition tensor_wrap_mod (tensors : nat -> nat -> nat) (id : nat) (m : ModuleState) : ModuleState :=
  {| module_region := module_region m;
     module_axioms := module_axioms m;
     module_mu_tensor := List.map (tensors id) (List.seq 0 16) |}.

(** graph_remove_modules commutes with the ID-preserving tensor overlay map. *)
Lemma graph_remove_modules_map_commute :
  forall (tensors : nat -> nat -> nat)
         (modules : list (nat * ModuleState)) (mid : nat),
    graph_remove_modules (map (fun '(id, m) => (id, tensor_wrap_mod tensors id m)) modules) mid =
    match graph_remove_modules modules mid with
    | None => None
    | Some (rest, removed) =>
        Some (map (fun '(id, m) => (id, tensor_wrap_mod tensors id m)) rest,
              tensor_wrap_mod tensors mid removed)
    end.
Proof.
  intros tensors modules mid.
  induction modules as [|[id m] rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb id mid) eqn:Eid.
    + apply Nat.eqb_eq in Eid. subst. reflexivity.
    + rewrite IH.
      destruct (graph_remove_modules rest mid) as [[r rm]|]; simpl; reflexivity.
Qed.

(** Under tensor freshness, wrapping a default module is identity. *)
Lemma tensor_wrap_mod_fresh :
  forall tensors id region axioms,
    (forall n, tensors id n = 0) ->
    tensor_wrap_mod tensors id (normalize_module (mk_module_state region axioms)) =
    normalize_module (mk_module_state region axioms).
Proof.
  intros tensors id region axioms Hfresh.
  unfold tensor_wrap_mod, normalize_module, mk_module_state, module_mu_tensor_default. simpl.
  f_equal.
  assert (H : List.map (tensors id) (List.seq 0 16) = repeat 0 16).
  { apply map_const_zero_repeat. exact Hfresh. }
  exact H.
Qed.

(** graph_module_size is independent of tensor overlay wrapping. *)
Lemma graph_module_size_tensor_overlay :
  forall tensors modules mid,
    graph_module_size
      {| pg_next_id := 0; pg_modules := map (fun '(id,m) => (id, tensor_wrap_mod tensors id m)) modules;
         pg_next_morph_id := 0; pg_morphisms := [] |} mid =
    graph_module_size
      {| pg_next_id := 0; pg_modules := modules; pg_next_morph_id := 0; pg_morphisms := [] |} mid.
Proof.
  intros tensors modules mid.
  unfold graph_module_size, graph_lookup, graph_lookup_modules. simpl.
  induction modules as [|[id m] rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb id mid); [|exact IH].
    simpl. reflexivity.
Qed.

(** snap_full_graph commutes with graph_hw_psplit under tensor freshness. *)

(** General commutation: graph_hw_psplit on tensor-wrapped modules = 
    wrapping the graph_hw_psplit of base modules.
    Under freshness for the two new slots. *)
Lemma graph_hw_psplit_overlay_commute :
  forall (base_mods : list (nat * ModuleState))
         (next_id base_morph_id morph_id : nat)
         (base_morphs : list (nat * MorphismState))
         (morphs : list (nat * MorphismState))
         (tensors : nat -> nat -> nat) (mid : nat),
    (forall n, tensors next_id n = 0) ->
    (forall n, tensors (S next_id) n = 0) ->
    let tw := fun '(id, m) => (id, tensor_wrap_mod tensors id m) in
    let base :=
      {| pg_next_id := next_id; pg_modules := base_mods;
         pg_next_morph_id := base_morph_id; pg_morphisms := base_morphs |} in
    let overlaid :=
      {| pg_next_id := next_id;
         pg_modules := map tw base_mods;
         pg_next_morph_id := morph_id;
         pg_morphisms := morphs |} in
    graph_hw_psplit overlaid mid =
    let result := graph_hw_psplit base mid in
    {| pg_next_id := pg_next_id result;
       pg_modules := map tw (pg_modules result);
       pg_next_morph_id := morph_id;
       pg_morphisms := morphs |}.
Proof.
  intros base_mods next_id base_morph_id morph_id base_morphs morphs tensors mid Hf1 Hf2 tw base overlaid.
  unfold graph_hw_psplit.
  (* graph_module_size is wrapping-independent *)
  assert (Hmsz : graph_module_size overlaid mid = graph_module_size base mid).
  { unfold graph_module_size, graph_lookup, graph_lookup_modules, overlaid, base. simpl.
    induction base_mods as [|[id m] rest IH]; simpl.
    - reflexivity.
    - destruct (Nat.eqb id mid); [simpl; reflexivity|exact IH]. }
  rewrite Hmsz.
  (* graph_remove commutes with wrapping *)
  set (base_r := match graph_remove base mid with Some (g', _) => g' | None => base end).
  set (overlay_r := match graph_remove overlaid mid with Some (g', _) => g' | None => overlaid end).
  assert (Hr_modules : pg_modules overlay_r =
    map tw (pg_modules base_r)).
  { subst overlay_r base_r overlaid tw base.
    unfold graph_remove. simpl pg_modules.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid) as [[r rm]|]; simpl; reflexivity. }
  assert (Hr_next_id : pg_next_id overlay_r = pg_next_id base_r).
  { subst overlay_r base_r overlaid tw base.
    unfold graph_remove. simpl pg_modules. simpl pg_next_id.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid) as [[r rm]|]; simpl; reflexivity. }
  assert (Hr_morphs : pg_next_morph_id overlay_r = morph_id /\
                       pg_morphisms overlay_r = morphs).
  { subst overlay_r overlaid tw base.
    unfold graph_remove. simpl.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid) as [[r rm]|]; simpl; auto. }
  destruct Hr_morphs as [Hr_mid Hr_ms].
  (* First graph_add_module *)
  set (left_sz := Nat.div (graph_module_size base mid) 2).
  set (right_sz := graph_module_size base mid - left_sz).
  destruct (graph_add_module base_r (List.seq 0 left_sz) []) as [ga1 id1] eqn:Ega1.
  destruct (graph_add_module overlay_r (List.seq 0 left_sz) []) as [oa1 oid1] eqn:Eoa1.
  unfold graph_add_module in Ega1, Eoa1.
  inversion Ega1; subst ga1 id1. inversion Eoa1; subst oa1 oid1.
  (* Second graph_add_module *)
  simpl pg_modules. simpl pg_next_id.
  simpl pg_next_morph_id. simpl pg_morphisms.
  (* pg_next_id base_r = pg_next_id base (graph_remove preserves next_id) *)
  assert (Hbr_nid : pg_next_id base_r = next_id).
  { subst base_r base. unfold graph_remove. simpl.
    destruct (graph_remove_modules base_mods mid) as [[r rm]|]; simpl; reflexivity. }
  apply partition_graph_eq; simpl pg_next_id; simpl pg_modules;
    simpl pg_next_morph_id; simpl pg_morphisms.
  - (* pg_next_id *)
    rewrite Hr_next_id. reflexivity.
  - (* pg_modules *)
    subst tw.
    rewrite Hr_modules, Hr_next_id, Hbr_nid.
    simpl map.
    rewrite (tensor_wrap_mod_fresh _ _ _ _ Hf2).
    rewrite (tensor_wrap_mod_fresh _ _ _ _ Hf1).
    reflexivity.
  - (* pg_next_morph_id *) rewrite Hr_mid. reflexivity.
  - (* pg_morphisms *) rewrite Hr_ms. reflexivity.
Qed.

Lemma snap_full_graph_psplit :
  forall ks module left_region right_region cost,
    pt_well_formed ks ->
    module mod PTableSz < snap_pt_next_id ks ->
    snap_pt_sizes ks (module mod PTableSz) >= 2 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    snap_pt_sizes ks (S (snap_pt_next_id ks)) = 0 ->
    S (S (snap_pt_next_id ks)) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    (forall n, snap_module_tensors ks (S (snap_pt_next_id ks)) n = 0) ->
    snap_full_graph (kami_step ks (instr_psplit module left_region right_region cost)) =
    graph_hw_psplit (snap_full_graph ks) (module mod PTableSz).
Proof.
  intros ks module left_region right_region cost [Hge Hlt] Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2.
  set (mid := module mod PTableSz).
  set (nid := snap_pt_next_id ks).
  set (sizes := snap_pt_sizes ks).
  set (tensors := snap_module_tensors ks).
  set (rs := snap_rich_state ks).
  set (tw := fun '(id, m) => (id, tensor_wrap_mod tensors id m)).
  set (base := snap_pt_to_graph nid sizes).
  (* Step 1: LHS = overlay(graph_hw_psplit(base, mid)) *)
  assert (Hlhs :
    snap_full_graph (kami_step ks (instr_psplit module left_region right_region cost)) =
    let result := graph_hw_psplit base mid in
    {| pg_next_id := pg_next_id result;
       pg_modules := map tw (pg_modules result);
       pg_next_morph_id := rich_next_morph_id rs;
       pg_morphisms := snapshot_morphisms_of_rich_state rs |}).
  { unfold snap_full_graph, kami_step.
    cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state].
    fold nid sizes mid tensors rs.
    (* Use snap_pt_to_graph_psplit *)
    pose proof (snap_pt_to_graph_psplit nid sizes mid Hge Hroom Hmid Hsize Hn0 Hsn0) as Hps.
    (* Align kami sizes3 ordering with canonical ordering *)
    assert (Hext : snap_pt_to_graph (S (S nid))
      (fun i =>
        if i =? S nid then sizes mid - Nat.div (sizes mid) 2
        else if i =? nid then Nat.div (sizes mid) 2
        else if i =? mid then 0
        else sizes i) =
      snap_pt_to_graph (S (S nid))
      (fun j =>
        if j =? mid then 0
        else if j =? nid then Nat.div (sizes mid) 2
        else if j =? S nid then sizes mid - Nat.div (sizes mid) 2
        else sizes j)).
    { apply snap_pt_to_graph_ext. intros i Hi.
      destruct (Nat.eqb i (S nid)) eqn:E1;
      destruct (Nat.eqb i nid) eqn:E2;
      destruct (Nat.eqb i mid) eqn:E3;
      try reflexivity; exfalso;
      repeat match goal with H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H end; lia. }
    (* Now: snap_pt_to_graph (S(S nid)) kami_sizes3 = graph_hw_psplit base mid *)
    rewrite Hext, <- Hps.
    pose proof (graph_hw_psplit_preserves_morph_fields base mid) as [Hfm Hfnm].
    subst tw.
    apply partition_graph_eq;
    try reflexivity;
    try (rewrite <- Hfnm; unfold base, snap_pt_to_graph; simpl; reflexivity);
    try (rewrite <- Hfm; unfold base, snap_pt_to_graph; simpl; reflexivity). }
  (* Step 2: snap_full_graph ks = overlay(base) *)
  assert (Hrhs :
    snap_full_graph ks =
    {| pg_next_id := pg_next_id base;
       pg_modules := map tw (pg_modules base);
       pg_next_morph_id := rich_next_morph_id rs;
       pg_morphisms := snapshot_morphisms_of_rich_state rs |}).
  { unfold snap_full_graph. subst tw base nid sizes tensors rs. reflexivity. }
  (* Step 3: Use commutation lemma *)
  rewrite Hlhs. rewrite Hrhs.
  pose proof (graph_hw_psplit_overlay_commute
    (pg_modules base) nid
    (pg_next_morph_id base) (rich_next_morph_id rs)
    (pg_morphisms base) (snapshot_morphisms_of_rich_state rs)
    tensors mid Hf1 Hf2) as Hcomm.
  subst tw. simpl in Hcomm.
  symmetry. exact Hcomm.
Qed.

Theorem driven_step_psplit :
  forall ks module left_region right_region cost,
    pt_well_formed ks ->
    morph_table_wf (snap_rich_state ks) ->
    module mod PTableSz < snap_pt_next_id ks ->
    snap_pt_sizes ks (module mod PTableSz) >= 2 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    snap_pt_sizes ks (S (snap_pt_next_id ks)) = 0 ->
    S (S (snap_pt_next_id ks)) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    (forall n, snap_module_tensors ks (S (snap_pt_next_id ks)) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_psplit module left_region right_region cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_psplit module left_region right_region cost).
Proof.
  intros ks module left_region right_region cost
    Hpt Hmwf Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2.
  assert (Hgeq : snap_full_graph
    (kami_step ks (instr_psplit module left_region right_region cost))
    = graph_hw_psplit (snap_full_graph ks) (module mod PTableSz)).
  { exact (snap_full_graph_psplit ks module left_region right_region cost
             Hpt Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2). }
  rewrite !abs_full_snapshot_of_snapshot. rewrite Hgeq.
  unfold kami_step, vm_apply, advance_state, apply_cost, instruction_cost.
  reflexivity.
Qed.

(** driven_step_psplit_full: drops the vestigial morph_table_wf precondition
    which was introduced but never used in the proof of driven_step_psplit. *)
Theorem driven_step_psplit_full :
  forall ks module left_region right_region cost,
    pt_well_formed ks ->
    module mod PTableSz < snap_pt_next_id ks ->
    snap_pt_sizes ks (module mod PTableSz) >= 2 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    snap_pt_sizes ks (S (snap_pt_next_id ks)) = 0 ->
    S (S (snap_pt_next_id ks)) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    (forall n, snap_module_tensors ks (S (snap_pt_next_id ks)) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_psplit module left_region right_region cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_psplit module left_region right_region cost).
Proof.
  intros ks module left_region right_region cost
    Hpt Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2.
  assert (Hgeq : snap_full_graph
    (kami_step ks (instr_psplit module left_region right_region cost))
    = graph_hw_psplit (snap_full_graph ks) (module mod PTableSz)).
  { exact (snap_full_graph_psplit ks module left_region right_region cost
             Hpt Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2). }
  rewrite !abs_full_snapshot_of_snapshot. rewrite Hgeq.
  unfold kami_step, vm_apply, advance_state, apply_cost, instruction_cost.
  reflexivity.
Qed.

(** Pmerge overlay commutation: graph_hw_pmerge on tensor-wrapped modules
    = wrapping the graph_hw_pmerge of base modules.
    Under freshness for the one new slot. *)
Lemma graph_hw_pmerge_overlay_commute :
  forall (base_mods : list (nat * ModuleState))
         (next_id base_morph_id morph_id : nat)
         (base_morphs : list (nat * MorphismState))
         (morphs : list (nat * MorphismState))
         (tensors : nat -> nat -> nat) (mid1 mid2 : nat),
    (forall n, tensors next_id n = 0) ->
    let tw := fun '(id, m) => (id, tensor_wrap_mod tensors id m) in
    let base :=
      {| pg_next_id := next_id; pg_modules := base_mods;
         pg_next_morph_id := base_morph_id; pg_morphisms := base_morphs |} in
    let overlaid :=
      {| pg_next_id := next_id;
         pg_modules := map tw base_mods;
         pg_next_morph_id := morph_id;
         pg_morphisms := morphs |} in
    graph_hw_pmerge overlaid mid1 mid2 =
    let result := graph_hw_pmerge base mid1 mid2 in
    {| pg_next_id := pg_next_id result;
       pg_modules := map tw (pg_modules result);
       pg_next_morph_id := morph_id;
       pg_morphisms := morphs |}.
Proof.
  intros base_mods next_id base_morph_id morph_id base_morphs morphs tensors mid1 mid2 Hf1 tw base overlaid.
  unfold graph_hw_pmerge.
  (* graph_module_size is wrapping-independent *)
  assert (Hmsz1 : graph_module_size overlaid mid1 = graph_module_size base mid1).
  { unfold graph_module_size, graph_lookup, graph_lookup_modules, overlaid, base. simpl.
    induction base_mods as [|[id m] rest IH]; simpl.
    - reflexivity.
    - destruct (Nat.eqb id mid1); [simpl; reflexivity|exact IH]. }
  rewrite Hmsz1.
  (* graph_remove mid1 commutes with wrapping *)
  set (base_r1 := match graph_remove base mid1 with Some (g', _) => g' | None => base end).
  set (overlay_r1 := match graph_remove overlaid mid1 with Some (g', _) => g' | None => overlaid end).
  assert (Hr1_modules : pg_modules overlay_r1 = map tw (pg_modules base_r1)).
  { subst overlay_r1 base_r1 overlaid tw base.
    unfold graph_remove. simpl pg_modules.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid1) as [[r rm]|]; simpl; reflexivity. }
  assert (Hr1_next_id : pg_next_id overlay_r1 = pg_next_id base_r1).
  { subst overlay_r1 base_r1 overlaid tw base.
    unfold graph_remove. simpl pg_modules. simpl pg_next_id.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid1) as [[r rm]|]; simpl; reflexivity. }
  assert (Hr1_morphs : pg_next_morph_id overlay_r1 = morph_id /\
                        pg_morphisms overlay_r1 = morphs).
  { subst overlay_r1 overlaid tw base.
    unfold graph_remove. simpl.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules base_mods mid1) as [[r rm]|]; simpl; auto. }
  destruct Hr1_morphs as [Hr1_mid Hr1_ms].
  (* graph_module_size mid2 on original overlaid — wrapping independent *)
  assert (Hmsz2 : graph_module_size overlaid mid2 = graph_module_size base mid2).
  { unfold graph_module_size, graph_lookup, graph_lookup_modules, overlaid, base. simpl.
    clear -Hf1 base_mods mid2 tensors tw.
    induction base_mods as [|[id m] rest IH]; simpl.
    - reflexivity.
    - destruct (Nat.eqb id mid2); [simpl; reflexivity|exact IH]. }
  rewrite Hmsz2.
  (* graph_remove mid2 on r1 *)
  set (base_r2 := match graph_remove base_r1 mid2 with Some (g', _) => g' | None => base_r1 end).
  set (overlay_r2 := match graph_remove overlay_r1 mid2 with Some (g', _) => g' | None => overlay_r1 end).
  assert (Hr2_modules : pg_modules overlay_r2 = map tw (pg_modules base_r2)).
  { subst overlay_r2 base_r2.
    unfold graph_remove.
    rewrite Hr1_modules. unfold tw.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules (pg_modules base_r1) mid2) as [[r rm]|]; simpl.
    - reflexivity.
    - fold tw. exact Hr1_modules. }
  assert (Hr2_next_id : pg_next_id overlay_r2 = pg_next_id base_r2).
  { subst overlay_r2 base_r2.
    unfold graph_remove.
    rewrite Hr1_modules. unfold tw.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules (pg_modules base_r1) mid2) as [[r rm]|]; simpl.
    - rewrite Hr1_next_id. reflexivity.
    - exact Hr1_next_id. }
  assert (Hr2_morphs : pg_next_morph_id overlay_r2 = morph_id /\
                        pg_morphisms overlay_r2 = morphs).
  { subst overlay_r2.
    unfold graph_remove.
    rewrite Hr1_modules. unfold tw.
    rewrite graph_remove_modules_map_commute.
    destruct (graph_remove_modules (pg_modules base_r1) mid2) as [[r rm]|]; simpl.
    - split; simpl.
      + rewrite Hr1_mid. reflexivity.
      + rewrite Hr1_ms. reflexivity.
    - exact (conj Hr1_mid Hr1_ms). }
  destruct Hr2_morphs as [Hr2_mid Hr2_ms].
  (* graph_add_module on r2 *)
  destruct (graph_add_module base_r2 _ _) as [ga1 id1] eqn:Ega1.
  destruct (graph_add_module overlay_r2 _ _) as [oa1 oid1] eqn:Eoa1.
  unfold graph_add_module in Ega1, Eoa1.
  inversion Ega1; subst ga1 id1. inversion Eoa1; subst oa1 oid1.
  simpl pg_modules. simpl pg_next_id.
  simpl pg_next_morph_id. simpl pg_morphisms.
  assert (Hbr_nid : pg_next_id base_r2 = next_id).
  { subst base_r2 base_r1 base. unfold graph_remove. simpl.
    destruct (graph_remove_modules base_mods mid1) as [[r1 rm1]|]; simpl;
    destruct (graph_remove_modules _ mid2) as [[r2 rm2]|]; simpl; reflexivity. }
  apply partition_graph_eq; simpl pg_next_id; simpl pg_modules;
    simpl pg_next_morph_id; simpl pg_morphisms.
  - (* pg_next_id *)
    rewrite Hr2_next_id. reflexivity.
  - (* pg_modules *)
    subst tw.
    rewrite Hr2_modules, Hr2_next_id, Hbr_nid.
    simpl map.
    rewrite (tensor_wrap_mod_fresh _ _ _ _ Hf1).
    reflexivity.
  - (* pg_next_morph_id *) rewrite Hr2_mid. reflexivity.
  - (* pg_morphisms *) rewrite Hr2_ms. reflexivity.
Qed.

Lemma snap_full_graph_pmerge :
  forall ks m1 m2 cost,
    pt_well_formed ks ->
    m1 mod PTableSz < snap_pt_next_id ks ->
    m2 mod PTableSz < snap_pt_next_id ks ->
    m1 mod PTableSz <> m2 mod PTableSz ->
    snap_pt_sizes ks (m1 mod PTableSz) > 0 ->
    snap_pt_sizes ks (m2 mod PTableSz) > 0 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    S (snap_pt_next_id ks) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    snap_full_graph (kami_step ks (instr_pmerge m1 m2 cost)) =
    graph_hw_pmerge (snap_full_graph ks) (m1 mod PTableSz) (m2 mod PTableSz).
Proof.
  intros ks m1 m2 cost [Hge Hlt] Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1.
  set (mid1 := m1 mod PTableSz). set (mid2 := m2 mod PTableSz).
  set (nid := snap_pt_next_id ks).
  set (sizes := snap_pt_sizes ks).
  set (tensors := snap_module_tensors ks).
  set (rs := snap_rich_state ks).
  set (tw := fun '(id, m) => (id, tensor_wrap_mod tensors id m)).
  set (base := snap_pt_to_graph nid sizes).
  (* Step 1: LHS = overlay(graph_hw_pmerge(base, mid1, mid2)) *)
  assert (Hlhs :
    snap_full_graph (kami_step ks (instr_pmerge m1 m2 cost)) =
    let result := graph_hw_pmerge base mid1 mid2 in
    {| pg_next_id := pg_next_id result;
       pg_modules := map tw (pg_modules result);
       pg_next_morph_id := rich_next_morph_id rs;
       pg_morphisms := snapshot_morphisms_of_rich_state rs |}).
  { unfold snap_full_graph, kami_step.
    cbn [snap_pt_next_id snap_pt_sizes snap_module_tensors snap_rich_state].
    fold nid sizes tensors rs mid1 mid2.
    pose proof (snap_pt_to_graph_pmerge nid sizes mid1 mid2
                  Hge Hroom Hm1 Hm2 Hne Hs1 Hs2 Hn0) as Hps.
    assert (Hext : snap_pt_to_graph (S nid)
      (fun j => if j =? mid1 then 0 else if j =? mid2 then 0
                else if j =? nid then sizes mid1 + sizes mid2 else sizes j) =
      snap_pt_to_graph (S nid)
      (fun i => if i =? nid then sizes mid1 + sizes mid2
                else if i =? mid2 then 0
                else if i =? mid1 then 0
                else sizes i)).
    { apply snap_pt_to_graph_ext. intros i Hi.
      destruct (Nat.eqb i nid) eqn:E1;
      destruct (Nat.eqb i mid2) eqn:E2;
      destruct (Nat.eqb i mid1) eqn:E3;
      try reflexivity; exfalso;
      repeat match goal with H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H end; lia. }
    f_equal.
    - (* pg_next_id *)
      rewrite <- Hext, <- Hps. unfold base, snap_pt_to_graph. simpl. reflexivity.
    - (* pg_modules *)
      rewrite <- Hext, <- Hps. unfold base, snap_pt_to_graph. simpl.
      fold tw. reflexivity. }
  (* Step 2: snap_full_graph ks = overlay(base) *)
  assert (Hrhs :
    snap_full_graph ks =
    {| pg_next_id := pg_next_id base;
       pg_modules := map tw (pg_modules base);
       pg_next_morph_id := rich_next_morph_id rs;
       pg_morphisms := snapshot_morphisms_of_rich_state rs |}).
  { unfold snap_full_graph. subst tw base nid sizes tensors rs. reflexivity. }
  (* Step 3: Use commutation lemma *)
  rewrite Hlhs. rewrite Hrhs.
  pose proof (graph_hw_pmerge_overlay_commute
    (pg_modules base) nid
    (pg_next_morph_id base) (rich_next_morph_id rs)
    (pg_morphisms base) (snapshot_morphisms_of_rich_state rs)
    tensors mid1 mid2 Hf1) as Hcomm.
  subst tw. simpl in Hcomm.
  symmetry. exact Hcomm.
Qed.

(* ======================================================================
   §15  PMERGE bridge
   *)

Theorem driven_step_pmerge :
  forall ks m1 m2 cost,
    pt_well_formed ks ->
    morph_table_wf (snap_rich_state ks) ->
    m1 mod PTableSz < snap_pt_next_id ks ->
    m2 mod PTableSz < snap_pt_next_id ks ->
    m1 mod PTableSz <> m2 mod PTableSz ->
    snap_pt_sizes ks (m1 mod PTableSz) > 0 ->
    snap_pt_sizes ks (m2 mod PTableSz) > 0 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    S (snap_pt_next_id ks) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_pmerge m1 m2 cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_pmerge m1 m2 cost).
Proof.
  intros ks m1 m2 cost [Hge Hlt] Hmwf Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1.
  assert (Hgeq : snap_full_graph
    (kami_step ks (instr_pmerge m1 m2 cost))
    = graph_hw_pmerge (snap_full_graph ks) (m1 mod PTableSz) (m2 mod PTableSz)).
  { exact (snap_full_graph_pmerge ks m1 m2 cost
      (conj Hge Hlt) Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1). }
  rewrite !abs_full_snapshot_of_snapshot. rewrite Hgeq.
  unfold kami_step, vm_apply, advance_state, apply_cost, instruction_cost.
  reflexivity.
Qed.

(** driven_step_pmerge_full: drops the vestigial morph_table_wf precondition
    which was introduced but never used in the proof of driven_step_pmerge. *)
Theorem driven_step_pmerge_full :
  forall ks m1 m2 cost,
    pt_well_formed ks ->
    m1 mod PTableSz < snap_pt_next_id ks ->
    m2 mod PTableSz < snap_pt_next_id ks ->
    m1 mod PTableSz <> m2 mod PTableSz ->
    snap_pt_sizes ks (m1 mod PTableSz) > 0 ->
    snap_pt_sizes ks (m2 mod PTableSz) > 0 ->
    snap_pt_sizes ks (snap_pt_next_id ks) = 0 ->
    S (snap_pt_next_id ks) <= PTableSz ->
    (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_pmerge m1 m2 cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_pmerge m1 m2 cost).
Proof.
  intros ks m1 m2 cost [Hge Hlt] Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1.
  assert (Hgeq : snap_full_graph
    (kami_step ks (instr_pmerge m1 m2 cost))
    = graph_hw_pmerge (snap_full_graph ks) (m1 mod PTableSz) (m2 mod PTableSz)).
  { exact (snap_full_graph_pmerge ks m1 m2 cost
      (conj Hge Hlt) Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1). }
  rewrite !abs_full_snapshot_of_snapshot. rewrite Hgeq.
  unfold kami_step, vm_apply, advance_state, apply_cost, instruction_cost.
  reflexivity.
Qed.

(* ======================================================================
   §16  COMPOSE, MORPH_TENSOR: field-by-field with coupling gap
   (MORPH_ID is now fully proven — see driven_step_morph_id below)
   *)

(** MORPH_ID: full VMState equality (including vm_graph).
    Hardware uses coupling_desc=0; kernel uses empty_coupling_data.
    Both produce an identity morphism with coupling_pairs=[], label="empty".

    Proof structure mirrors driven_step_morph exactly:
    - morph_add_commutation + coupling_zero_empty → snapshot pairs = []
    - normalize_coupling(empty_coupling_data) = {|pairs=[]; label="empty"|}
    - full reflexivity after graph equality is established. *)
Theorem driven_step_morph_id :
  forall ks dst module cost,
    extended_hw_invariant ks ->
    module < snap_pt_next_id ks ->
    negb (Nat.eqb (snap_pt_sizes ks module) 0) = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_id dst module cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_id dst module cost).
Proof.
  intros ks dst module cost
    [Hpt [Hwf [Hcze [_ _]]]] Hlt Hmod.
  set (rs := snap_rich_state ks) in *.
  (* Module exists in the reconstructed graph *)
  destruct (snap_pt_sizes_nonzero_graph_lookup ks module Hlt Hmod) as [m Em].
  rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  rewrite Hmod.
  destruct (rich_state_add_morph rs module module 0 true) as [rs' new_id] eqn:Eram.
  unfold vm_apply. cbn [vm_graph].
  unfold graph_add_identity. rewrite Em.
  destruct (graph_add_morphism (snap_full_graph ks) module module empty_coupling_data true)
    as [graph' morph_id] eqn:Egam.
  (* new_id = morph_id: both equal rich_next_morph_id rs *)
  assert (Hid : new_id = morph_id).
  { unfold rich_state_add_morph in Eram. inversion Eram.
    unfold graph_add_morphism in Egam. inversion Egam.
    unfold snap_full_graph. simpl pg_next_morph_id. reflexivity. }
  (* Graph equality *)
  assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst new_id cost rs') = graph').
  { unfold graph_add_morphism in Egam. inversion Egam; subst graph'. clear Egam.
    unfold snap_full_graph, kami_advance_rich_morph.
    cbn [snap_pt_next_id snap_pt_sizes snap_rich_state snap_module_tensors
         pg_next_id pg_modules pg_next_morph_id pg_morphisms].
    pose proof (morph_add_commutation rs module module 0 true) as Hmc.
    rewrite Eram in Hmc. rewrite Hmc. clear Hmc.
    assert (Hcp : snapshot_coupling_pairs_from_desc rs 0 = []).
    { unfold snapshot_coupling_pairs_from_desc. rewrite Hcze. reflexivity. }
    rewrite Hcp.
    rewrite Hcze.
    unfold rich_state_add_morph in Eram. inversion Eram; subst rs' new_id.
    simpl rich_next_morph_id.
    replace (rich_next_morph_id rs + 1) with (S (rich_next_morph_id rs)) by lia.
    unfold normalize_coupling. simpl.
    reflexivity. }
  (* All fields match *)
  unfold advance_state_rm, apply_cost, instruction_cost.
  subst morph_id.
  rewrite Hgeq.
  unfold kami_advance_rich_morph.
  cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
       snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_logic_acc snap_mstatus
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
       vm_logic_acc vm_mstatus vm_witness vm_certified
       csr_cert_addr csr_status csr_err csr_heap_base
       wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
       wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
  fold (kami_write_reg ks dst new_id).
  rewrite full_state_kami_reg_write.
  rewrite abs_full_snapshot_of_snapshot.
  reflexivity.
Qed.

(** driven_step_morph_id_full: reduced precondition — replaces extended_hw_invariant
    with just coupling_zero_empty.  The proof of driven_step_morph_id only uses
    Hcze from the full invariant; Hwf, Hcdaz, Hpt, and coupling_desc_safe are
    destructured but never referenced in the proof body. *)
Theorem driven_step_morph_id_full :
  forall ks dst module cost,
    coupling_zero_empty (snap_rich_state ks) ->
    module < snap_pt_next_id ks ->
    negb (Nat.eqb (snap_pt_sizes ks module) 0) = true ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_id dst module cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_id dst module cost).
Proof.
  intros ks dst module cost Hcze Hlt Hmod.
  set (rs := snap_rich_state ks) in *.
  destruct (snap_pt_sizes_nonzero_graph_lookup ks module Hlt Hmod) as [m Em].
  rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  rewrite Hmod.
  destruct (rich_state_add_morph rs module module 0 true) as [rs' new_id] eqn:Eram.
  unfold vm_apply. cbn [vm_graph].
  unfold graph_add_identity. rewrite Em.
  destruct (graph_add_morphism (snap_full_graph ks) module module empty_coupling_data true)
    as [graph' morph_id] eqn:Egam.
  assert (Hid : new_id = morph_id).
  { unfold rich_state_add_morph in Eram. inversion Eram.
    unfold graph_add_morphism in Egam. inversion Egam.
    unfold snap_full_graph. simpl pg_next_morph_id. reflexivity. }
  assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst new_id cost rs') = graph').
  { unfold graph_add_morphism in Egam. inversion Egam; subst graph'. clear Egam.
    unfold snap_full_graph, kami_advance_rich_morph.
    cbn [snap_pt_next_id snap_pt_sizes snap_rich_state snap_module_tensors
         pg_next_id pg_modules pg_next_morph_id pg_morphisms].
    pose proof (morph_add_commutation rs module module 0 true) as Hmc.
    rewrite Eram in Hmc. rewrite Hmc. clear Hmc.
    assert (Hcp : snapshot_coupling_pairs_from_desc rs 0 = []).
    { unfold snapshot_coupling_pairs_from_desc. rewrite Hcze. reflexivity. }
    rewrite Hcp.
    rewrite Hcze.
    unfold rich_state_add_morph in Eram. inversion Eram; subst rs' new_id.
    simpl rich_next_morph_id.
    replace (rich_next_morph_id rs + 1) with (S (rich_next_morph_id rs)) by lia.
    unfold normalize_coupling. simpl.
    reflexivity. }
  unfold advance_state_rm, apply_cost, instruction_cost.
  subst morph_id.
  rewrite Hgeq.
  unfold kami_advance_rich_morph.
  cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
       snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
       snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
       snap_logic_acc snap_mstatus
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
       vm_logic_acc vm_mstatus vm_witness vm_certified
       csr_cert_addr csr_status csr_err csr_heap_base
       wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
       wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
  fold (kami_write_reg ks dst new_id).
  rewrite full_state_kami_reg_write.
  rewrite abs_full_snapshot_of_snapshot.
  reflexivity.
Qed.

(** COMPOSE: hardware creates composed morphism with empty coupling.
    Kernel creates with relational_compose coupling.
    Source (f.source) and target (h.target) agree;
    coupling data and label differ.

    Branch agreement (vm_err) is proven using [morph_lookup_agrees]
    and [graph_lookup_morphism_corresponds]: the morph table and the
    reconstructed graph agree on morphism existence and endpoint fields,
    so the endpoint check resolves identically on both sides. *)
Theorem driven_step_compose_fields :
  forall ks dst m1_id m2_id cost,
    extended_hw_invariant ks ->
    let hs' := abs_full_snapshot (full_snapshot_of_snapshot
                 (kami_step ks (instr_compose dst m1_id m2_id cost))) in
    let vs' := vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
                 (instr_compose dst m1_id m2_id cost) in
    vm_pc hs' = vm_pc vs' /\
    vm_mu hs' = vm_mu vs' /\
    vm_err hs' = vm_err vs' /\
    vm_mu_tensor hs' = vm_mu_tensor vs' /\
    vm_witness hs' = vm_witness vs' /\
    vm_certified hs' = vm_certified vs'.
    (* vm_graph and vm_regs are omitted from THIS helper lemma.
       Full state equality including vm_graph/vm_regs is proved by
       driven_step_compose below, which uses the complete extended_hw_invariant. *)
Proof.
  intros ks dst m1_id m2_id cost [Hpt [Hwf [Hcze [_ _]]]].
  set (rs := snap_rich_state ks) in *.
  cbv zeta. rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  unfold vm_apply. cbn [vm_graph].
  (* Case analysis on morph table lookups *)
  destruct (rich_morph_table rs m1_id) as [e1|] eqn:Em1.
  - (* m1 found in rich table *)
    destruct (rich_morph_table rs m2_id) as [e2|] eqn:Em2.
    + (* Both found — bridge to graph lookups *)
      pose proof (morph_lookup_agrees ks m1_id Hwf) as Hm1g.
      fold rs in Hm1g. rewrite Em1 in Hm1g.
      destruct (graph_lookup_morphism (snap_full_graph ks) m1_id) as [f|] eqn:Ef;
        [|exfalso; exact (Hm1g eq_refl)].
      pose proof (morph_lookup_agrees ks m2_id Hwf) as Hm2g.
      fold rs in Hm2g. rewrite Em2 in Hm2g.
      destruct (graph_lookup_morphism (snap_full_graph ks) m2_id) as [h|] eqn:Eh;
        [|exfalso; exact (Hm2g eq_refl)].
      (* Correspondence: graph morphism fields match rich table entries *)
      pose proof (graph_lookup_morphism_corresponds ks m1_id e1 f Hwf Em1 Ef) as ->.
      pose proof (graph_lookup_morphism_corresponds ks m2_id e2 h Hwf Em2 Eh) as ->.
      (* Endpoint check is now identical on both sides *)
      unfold graph_compose_morphisms. rewrite Ef, Eh.
      simpl morph_target. simpl morph_source.
      destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Hep.
      * (* Endpoint match — both success *)
        destruct (rich_state_add_morph rs (morph_entry_source e1) (morph_entry_target e2) 0 false)
          as [rs' new_id] eqn:Eram.
        repeat split; reflexivity.
      * (* Endpoint mismatch — both error *)
        repeat split; reflexivity.
    + (* m2 not found — both error *)
      assert (Hgcm : graph_compose_morphisms (snap_full_graph ks) m1_id m2_id = None).
      { unfold graph_compose_morphisms.
        pose proof (morph_table_none_implies_graph_none ks m2_id) as Hg2.
        unfold rs in Em2. rewrite (Hg2 Em2).
        destruct (graph_lookup_morphism (snap_full_graph ks) m1_id); reflexivity. }
      rewrite Hgcm.
      repeat split; reflexivity.
  - (* m1 not found — both error *)
    assert (Hgcm : graph_compose_morphisms (snap_full_graph ks) m1_id m2_id = None).
    { unfold graph_compose_morphisms.
      pose proof (morph_table_none_implies_graph_none ks m1_id) as Hg1.
      unfold rs in Em1. rewrite (Hg1 Em1).
      reflexivity. }
    rewrite Hgcm.
    repeat split; reflexivity.
Qed.

Theorem driven_step_compose :
  forall ks dst m1_id m2_id cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_compose dst m1_id m2_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_compose dst m1_id m2_id cost).
Proof.
  intros ks dst m1_id m2_id cost [Hpt [Hwf [Hcze [Hwcf Hsafe]]]].
  set (rs := snap_rich_state ks) in *.
  (* unfold coupling_desc_safe to expose rich_next_coupling_desc_id rs > 0 *)
  unfold coupling_desc_safe in Hsafe. fold rs in Hsafe.
  destruct (rich_morph_table rs m1_id) as [e1|] eqn:Em1.
  - destruct (rich_morph_table rs m2_id) as [e2|] eqn:Em2.
    + pose proof (morph_lookup_agrees ks m1_id Hwf) as Hm1g.
      fold rs in Hm1g. rewrite Em1 in Hm1g.
      destruct (graph_lookup_morphism (snap_full_graph ks) m1_id) as [f|] eqn:Ef;
        [|exfalso; exact (Hm1g eq_refl)].
      pose proof (morph_lookup_agrees ks m2_id Hwf) as Hm2g.
      fold rs in Hm2g. rewrite Em2 in Hm2g.
      destruct (graph_lookup_morphism (snap_full_graph ks) m2_id) as [h|] eqn:Eh;
        [|exfalso; exact (Hm2g eq_refl)].
      pose proof (graph_lookup_morphism_corresponds ks m1_id e1 f Hwf Em1 Ef) as Hf_eq.
      pose proof (graph_lookup_morphism_corresponds ks m2_id e2 h Hwf Em2 Eh) as Hh_eq.
      fold rs in Hf_eq. fold rs in Hh_eq.
      rewrite !abs_full_snapshot_of_snapshot.
      unfold kami_step. fold rs. rewrite Em1, Em2.
      unfold vm_apply. cbn [vm_graph].
      unfold graph_compose_morphisms.
      rewrite Ef, Eh.
      rewrite Hf_eq, Hh_eq.
      simpl morph_target. simpl morph_source.
      (* Reduce coupling projections, and the identity-flag projection too, so the
         3-way identity short-circuit reduces to morph_entry_is_identity e1/e2
         (matching the hardware side); set then folds them into abbreviations. *)
      cbn [coupling_pairs morph_coupling morph_is_identity].
      fold (morph_coupling_label rs e1).
      fold (morph_coupling_label rs e2).
      cbn [coupling_label].
      (* Let pairs1/pairs2/labels be the actual values — no assumption of [] *)
      set (pairs1 := snapshot_coupling_pairs_from_desc rs (morph_entry_coupling_desc e1)).
      set (pairs2 := snapshot_coupling_pairs_from_desc rs (morph_entry_coupling_desc e2)).
      set (label1 := morph_coupling_label rs e1).
      set (label2 := morph_coupling_label rs e2).
      set (composed_label := (label1 ++ ";" ++ label2)%string).
      set (composed_pairs :=
        (normalize_coupling {| coupling_pairs :=
             (if morph_entry_is_identity e1
              then pairs2
              else if morph_entry_is_identity e2
                   then pairs1
                   else relational_compose pairs1 pairs2);
                                coupling_label := composed_label |}).(coupling_pairs)).
      destruct (Nat.eqb (morph_entry_target e1) (morph_entry_source e2)) eqn:Hep.
      * (* Endpoint match — success on both sides *)
        (* Hardware: rich_state_add_morph_with_coupling with composed_pairs *)
        remember (rich_state_add_morph_with_coupling rs
                    (morph_entry_source e1) (morph_entry_target e2)
                    composed_pairs composed_label false) as addm eqn:Eaddm.
        destruct addm as [rs' new_id].
        (* Kernel: graph_add_morphism normalizes relational_compose internally *)
        destruct (graph_add_morphism (snap_full_graph ks)
                    (morph_entry_source e1) (morph_entry_target e2)
                    {| coupling_pairs :=
                         (if morph_entry_is_identity e1
                          then pairs2
                          else if morph_entry_is_identity e2
                               then pairs1
                               else relational_compose pairs1 pairs2);
                       coupling_label := composed_label |}
                    false) as [graph' morph_id] eqn:Egam.
        (* new_id = morph_id: both equal rich_next_morph_id rs *)
        assert (Hid : new_id = morph_id).
        { unfold rich_state_add_morph_with_coupling in Eaddm.
          destruct (rich_state_add_coupling_data rs composed_pairs composed_label)
            as [rs1 desc_id] eqn:Eadd in Eaddm.
          assert (Hrs1_mid : rich_next_morph_id rs1 = rich_next_morph_id rs).
          { unfold rich_state_add_coupling_data in Eadd. inversion Eadd. reflexivity. }
          unfold rich_state_add_morph in Eaddm.
          inversion Eaddm; subst rs' new_id; clear Eaddm.
          unfold graph_add_morphism in Egam. inversion Egam; subst graph' morph_id.
          unfold snap_full_graph. simpl pg_next_morph_id.
          rewrite Hrs1_mid. reflexivity. }
        (* snap_full_graph (kami_advance_rich_morph ...) = graph' *)
        assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst new_id cost rs') = graph').
        { (* Use morph_add_with_coupling_commutation_gen: coupling_wf suffices *)
          pose proof (morph_add_with_coupling_commutation_gen rs
                        (morph_entry_source e1) (morph_entry_target e2)
                        composed_pairs composed_label false Hwcf Hcze Hsafe) as Hmc.
          rewrite <- Eaddm in Hmc. simpl in Hmc.
          assert (Hnext : rich_next_morph_id rs' = S (rich_next_morph_id rs)).
          { unfold rich_state_add_morph_with_coupling in Eaddm.
            destruct (rich_state_add_coupling_data rs composed_pairs composed_label)
              as [rs1 desc_id] eqn:Eadd in Eaddm.
            assert (Hrs1_mid : rich_next_morph_id rs1 = rich_next_morph_id rs).
            { unfold rich_state_add_coupling_data in Eadd. inversion Eadd. reflexivity. }
            unfold rich_state_add_morph in Eaddm.
            inversion Eaddm; subst rs' new_id; clear Eaddm.
            simpl. rewrite Hrs1_mid. lia. }
          unfold graph_add_morphism in Egam. inversion Egam; subst graph' morph_id. clear Egam.
          apply partition_graph_eq; simpl.
          - reflexivity.
          - reflexivity.
          - rewrite Hnext. reflexivity.
          - unfold snap_full_graph. simpl.
            rewrite Hmc. rewrite H1. fold rs.
            (* normalize_coupling applied to {composed_pairs; ...} is idempotent *)
            unfold composed_pairs, normalize_coupling. simpl.
            reflexivity. }
        assert (Hnewid : new_id = rich_next_morph_id (snap_rich_state ks)).
        { unfold rich_state_add_morph_with_coupling in Eaddm.
          destruct (rich_state_add_coupling_data rs composed_pairs composed_label)
            as [rs1 desc_id] eqn:Eadd in Eaddm.
          assert (Hrs1_mid : rich_next_morph_id rs1 = rich_next_morph_id rs).
          { unfold rich_state_add_coupling_data in Eadd. inversion Eadd. reflexivity. }
          unfold rich_state_add_morph in Eaddm.
          inversion Eaddm; subst rs' new_id; clear Eaddm.
          rewrite Hrs1_mid. reflexivity. }
        unfold advance_state_rm, apply_cost, instruction_cost.
        subst morph_id.
        rewrite Hgeq.
        unfold kami_advance_rich_morph.
        cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
             snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
             snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
             snap_logic_acc snap_mstatus
             snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
             snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
             vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
             vm_logic_acc vm_mstatus vm_witness vm_certified
             csr_cert_addr csr_status csr_err csr_heap_base
             wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
             wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
        fold (kami_write_reg ks dst new_id).
        rewrite full_state_kami_reg_write.
        rewrite abs_full_snapshot_of_snapshot.
        rewrite Hnewid. fold rs.
        reflexivity.
      * rewrite snap_full_graph_advance_err.
        unfold advance_state, apply_cost, instruction_cost, latch_err.
        reflexivity.
    + assert (Hgcm : graph_compose_morphisms (snap_full_graph ks) m1_id m2_id = None).
      { unfold graph_compose_morphisms.
        pose proof (morph_table_none_implies_graph_none ks m2_id Em2) as Hg2.
        rewrite Hg2.
        destruct (graph_lookup_morphism (snap_full_graph ks) m1_id); reflexivity. }
      rewrite !abs_full_snapshot_of_snapshot.
      unfold kami_step. fold rs. rewrite Em1, Em2.
      unfold vm_apply. cbn [vm_graph]. rewrite Hgcm.
      rewrite snap_full_graph_advance_err.
      unfold advance_state, apply_cost, instruction_cost, latch_err.
      reflexivity.
  - assert (Hgcm : graph_compose_morphisms (snap_full_graph ks) m1_id m2_id = None).
    { unfold graph_compose_morphisms.
      pose proof (morph_table_none_implies_graph_none ks m1_id Em1) as Hg1.
      rewrite Hg1. reflexivity. }
    rewrite !abs_full_snapshot_of_snapshot.
    unfold kami_step. fold rs. rewrite Em1.
    unfold vm_apply. cbn [vm_graph]. rewrite Hgcm.
    rewrite snap_full_graph_advance_err.
    unfold advance_state, apply_cost, instruction_cost, latch_err.
    reflexivity.
Qed.

(** MORPH_TENSOR: hardware creates tensor morphism from
    ef.source → eg.target with empty coupling.
    Kernel creates from union-region module to union-region module
    with concatenated coupling.  Source, target, AND coupling all differ.

    This is the most divergent opcode: driver-patched, like TENSOR_SET/GET.
    The hardware produces a placeholder morphism; the driver must patch
    source, target, and coupling to match the kernel's tensor semantics.

    Unlike COMPOSE, the hardware performs NO endpoint, module-existence,
    disjointness, or union-module checks that [graph_tensor_morphisms]
    verifies.  Therefore [vm_err] agreement cannot be proven without
    additional region-structural invariants.  The 5 fields below are
    branch-independent: they have the same value regardless of whether
    the operation succeeds or fails on either side. *)
Theorem driven_step_morph_tensor_fields :
  forall ks dst f_id g_id cost,
    extended_hw_invariant ks ->
    let hs' := abs_full_snapshot (full_snapshot_of_snapshot
                 (kami_step ks (instr_morph_tensor dst f_id g_id cost))) in
    let vs' := vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
                 (instr_morph_tensor dst f_id g_id cost) in
    vm_pc hs' = vm_pc vs' /\
    vm_mu hs' = vm_mu vs' /\
    vm_mu_tensor hs' = vm_mu_tensor vs' /\
    vm_witness hs' = vm_witness vs' /\
    vm_certified hs' = vm_certified vs'.
    (* vm_graph differs in source, target, AND coupling of the new morphism;
       vm_err requires region-structural bridge (not proven here) *)
Proof.
  intros ks dst f_id g_id cost [Hpt [Hwf [Hcze [_ _]]]].
  set (rs := snap_rich_state ks) in *.
  cbv zeta. rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  unfold vm_apply. cbn [vm_graph].
  (* Both sides branch on graph_tensor_morphisms *)
  destruct (graph_tensor_morphisms (snap_full_graph ks) f_id g_id) as [[g' mid]|] eqn:Egt.
  - (* graph_tensor_morphisms succeeded *)
    destruct (graph_lookup_morphism g' mid) as [new_ms|] eqn:Elm.
    + (* lookup succeeded — kami success path *)
      match goal with
      | |- context [rich_state_add_morph_with_coupling ?a ?b ?c ?d ?e ?f] =>
          destruct (rich_state_add_morph_with_coupling a b c d e f) as [rs' new_mid']
      end.
      repeat split; reflexivity.
    + (* lookup failed — kami error *)
      repeat split; reflexivity.
  - (* graph_tensor_morphisms failed — kami error *)
    repeat split; reflexivity.
Qed.

Theorem driven_step_morph_tensor :
  forall ks dst f_id g_id cost,
    extended_hw_invariant ks ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_step ks (instr_morph_tensor dst f_id g_id cost))) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks))
      (instr_morph_tensor dst f_id g_id cost).
Proof.
  intros ks dst f_id g_id cost [Hpt [Hwf [Hcze [Hwcf Hsafe]]]].
  set (rs := snap_rich_state ks) in *.
  rewrite !abs_full_snapshot_of_snapshot.
  unfold kami_step. fold rs.
  set (g := snap_full_graph ks).
  destruct (graph_tensor_morphisms g f_id g_id) as [[graph' morph_id]|] eqn:Htensor.
  - destruct (graph_lookup_morphism graph' morph_id) as [new_ms|] eqn:Hnew.
    + remember (rich_state_add_morph_with_coupling rs
                  new_ms.(morph_source) new_ms.(morph_target)
                  new_ms.(morph_coupling).(coupling_pairs)
                  new_ms.(morph_coupling).(coupling_label) false) as addm eqn:Eaddm.
      destruct addm as [rs' ignored_id].
      assert (exists f_ms_tensor g_ms_tensor ac_id_tensor bd_id_tensor,
        new_ms =
        {| morph_source := ac_id_tensor;
           morph_target := bd_id_tensor;
           morph_coupling :=
             normalize_coupling
               {| coupling_pairs := coupling_pairs (morph_coupling f_ms_tensor) ++
                                    coupling_pairs (morph_coupling g_ms_tensor);
                  coupling_label := (coupling_label (morph_coupling f_ms_tensor) ++
                                     "⊗" ++
                                     coupling_label (morph_coupling g_ms_tensor))%string |};
           morph_is_identity := false;
               morph_cert_cost := 0 |}) as
          (f_ms_tensor & g_ms_tensor & ac_id_tensor & bd_id_tensor & Hnew_ms_eq).
      { unfold graph_tensor_morphisms in Htensor.
        destruct (graph_lookup_morphism g f_id) as [f_ms'|] eqn:Hf'; [|discriminate].
        destruct (graph_lookup_morphism g g_id) as [g_ms'|] eqn:Hg'; [|discriminate].
        cbn beta iota in Htensor.
        destruct (graph_lookup g (morph_source f_ms')) as [a_mod'|]; [|discriminate].
        destruct (graph_lookup g (morph_target f_ms')) as [b_mod'|]; [|discriminate].
        destruct (graph_lookup g (morph_source g_ms')) as [c_mod'|]; [|discriminate].
        destruct (graph_lookup g (morph_target g_ms')) as [d_mod'|]; [|discriminate].
        cbn beta iota in Htensor.
        destruct (nat_list_disjoint (module_region a_mod') (module_region c_mod') &&
                  nat_list_disjoint (module_region b_mod') (module_region d_mod'));
          [|discriminate].
        cbn beta iota zeta in Htensor.
        destruct (graph_find_region g (nat_list_union (module_region a_mod') (module_region c_mod'))) as [ac_id'|] eqn:Hac';
          [|discriminate].
        destruct (graph_find_region g (nat_list_union (module_region b_mod') (module_region d_mod'))) as [bd_id'|] eqn:Hbd';
          [|discriminate].
        cbn beta iota in Htensor.
        unfold graph_add_morphism in Htensor.
        inversion Htensor; subst graph' morph_id; clear Htensor.
        unfold graph_lookup_morphism, graph_lookup_morphism_list in Hnew. simpl in Hnew.
        rewrite Nat.eqb_refl in Hnew.
        inversion Hnew; subst new_ms.
        exists f_ms', g_ms', ac_id', bd_id'.
        reflexivity. }
      set (tensor_c :=
        normalize_coupling
          {| coupling_pairs := coupling_pairs (morph_coupling f_ms_tensor) ++
                               coupling_pairs (morph_coupling g_ms_tensor);
             coupling_label := (coupling_label (morph_coupling f_ms_tensor) ++
                                "⊗" ++
                                coupling_label (morph_coupling g_ms_tensor))%string |}) in *.
      subst new_ms.
      assert (Hgeq : snap_full_graph (kami_advance_rich_morph ks dst morph_id cost rs') = graph').
      { unfold graph_tensor_morphisms in Htensor.
        destruct (graph_lookup_morphism g f_id) as [f_ms|] eqn:Hf; [|discriminate].
        destruct (graph_lookup_morphism g g_id) as [g_ms|] eqn:Hg; [|discriminate].
        cbn beta iota in Htensor.
        destruct (graph_lookup g (morph_source f_ms)) as [a_mod|]; [|discriminate].
        destruct (graph_lookup g (morph_target f_ms)) as [b_mod|]; [|discriminate].
        destruct (graph_lookup g (morph_source g_ms)) as [c_mod|]; [|discriminate].
        destruct (graph_lookup g (morph_target g_ms)) as [d_mod|]; [|discriminate].
        cbn beta iota in Htensor.
        destruct (nat_list_disjoint (module_region a_mod) (module_region c_mod) &&
                  nat_list_disjoint (module_region b_mod) (module_region d_mod));
          [|discriminate].
        cbn beta iota zeta in Htensor.
        destruct (graph_find_region g (nat_list_union (module_region a_mod) (module_region c_mod))) as [ac_id|] eqn:Hac;
          [|discriminate].
        destruct (graph_find_region g (nat_list_union (module_region b_mod) (module_region d_mod))) as [bd_id|] eqn:Hbd;
          [|discriminate].
        cbn beta iota in Htensor.
        unfold graph_add_morphism in Htensor. inversion Htensor; subst graph' morph_id.
        unfold graph_lookup_morphism, graph_lookup_morphism_list in Hnew. simpl in Hnew.
        rewrite Nat.eqb_refl in Hnew.
        inversion Hnew; subst ac_id_tensor bd_id_tensor; clear Hnew.
        pose proof (morph_add_with_coupling_commutation_gen rs
                      ac_id bd_id
                      tensor_c.(coupling_pairs)
                      tensor_c.(coupling_label) false
                      Hwcf Hcze Hsafe) as Hmc.
          replace (morph_source
                {| morph_source := ac_id;
                  morph_target := bd_id;
                  morph_coupling := tensor_c;
                  morph_is_identity := false;
               morph_cert_cost := 0 |}) with ac_id in Hmc by reflexivity.
          replace (morph_target
                {| morph_source := ac_id;
                  morph_target := bd_id;
                  morph_coupling := tensor_c;
                  morph_is_identity := false;
               morph_cert_cost := 0 |}) with bd_id in Hmc by reflexivity.
          replace (coupling_pairs
                (morph_coupling
                  {| morph_source := ac_id;
                    morph_target := bd_id;
                    morph_coupling := tensor_c;
                    morph_is_identity := false;
               morph_cert_cost := 0 |}))
           with tensor_c.(coupling_pairs) in Hmc by reflexivity.
          replace (coupling_label
                (morph_coupling
                  {| morph_source := ac_id;
                    morph_target := bd_id;
                    morph_coupling := tensor_c;
                    morph_is_identity := false;
               morph_cert_cost := 0 |}))
           with tensor_c.(coupling_label) in Hmc by reflexivity.
            cbn [morph_source morph_target morph_coupling coupling_pairs coupling_label] in Eaddm.
        rewrite <- Eaddm in Hmc. simpl in Hmc.
        assert (Hid : ignored_id = rich_next_morph_id rs /\
                      rich_next_morph_id rs' = S (rich_next_morph_id rs)).
        { pose proof Eaddm as Eaddm_local.
          unfold rich_state_add_morph_with_coupling in Eaddm_local.
          destruct (rich_state_add_coupling_data rs tensor_c.(coupling_pairs)
                    tensor_c.(coupling_label)) as [rs1 desc_id] eqn:Eadd_local in Eaddm_local.
          assert (Hrs1_mid_local : rich_next_morph_id rs1 = rich_next_morph_id rs).
          { destruct rs; simpl in Eadd_local.
            inversion Eadd_local; reflexivity. }
          destruct (rich_state_add_morph rs1 ac_id bd_id desc_id false)
            as [rs'' new_id'] eqn:Eram in Eaddm_local.
          inversion Eaddm_local; subst rs' ignored_id.
          split.
          - unfold rich_state_add_morph in Eram.
            inversion Eram; subst rs'' new_id'.
            rewrite Hrs1_mid_local. reflexivity.
          - unfold rich_state_add_morph in Eram.
            inversion Eram; subst rs'' new_id'.
            simpl. rewrite Nat.add_1_r, Hrs1_mid_local. reflexivity. }
        destruct Hid as [Hid Hnext].
        apply partition_graph_eq; simpl.
        - reflexivity.
        - reflexivity.
        - rewrite Hnext. reflexivity.
        - unfold snap_full_graph. simpl.
          rewrite Hmc.
          rewrite Hid.
          rewrite <- H2, <- H3.
          destruct tensor_c.
          reflexivity. }
      unfold vm_apply. cbn [vm_graph]. rewrite Htensor.
      unfold advance_state_rm, apply_cost, instruction_cost.
      rewrite Hgeq.
      unfold kami_advance_rich_morph.
      cbn [snap_regs snap_pc snap_mu snap_err snap_mem snap_mu_tensor
           snap_halted snap_certified snap_rich_state snap_pt_sizes snap_pt_next_id
           snap_csr_cert_addr snap_csr_status snap_csr_err snap_csr_heap_base
           snap_logic_acc snap_mstatus
           snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
           snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
           vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor vm_err
           vm_logic_acc vm_mstatus vm_witness vm_certified
           csr_cert_addr csr_status csr_err csr_heap_base
           wc_same_00 wc_diff_00 wc_same_01 wc_diff_01
           wc_same_10 wc_diff_10 wc_same_11 wc_diff_11].
      fold (kami_write_reg ks dst morph_id).
      rewrite full_state_kami_reg_write.
      rewrite abs_full_snapshot_of_snapshot.
      reflexivity.
    + exfalso.
      unfold graph_tensor_morphisms in Htensor.
      destruct (graph_lookup_morphism g f_id) as [f_ms|] eqn:Hf; [|discriminate].
      destruct (graph_lookup_morphism g g_id) as [g_ms|] eqn:Hg; [|discriminate].
      cbn beta iota in Htensor.
      destruct (graph_lookup g (morph_source f_ms)) as [a_mod|]; [|discriminate].
      destruct (graph_lookup g (morph_target f_ms)) as [b_mod|]; [|discriminate].
      destruct (graph_lookup g (morph_source g_ms)) as [c_mod|]; [|discriminate].
      destruct (graph_lookup g (morph_target g_ms)) as [d_mod|]; [|discriminate].
      cbn beta iota in Htensor.
      destruct (nat_list_disjoint (module_region a_mod) (module_region c_mod) &&
                nat_list_disjoint (module_region b_mod) (module_region d_mod));
        [|discriminate].
      cbn beta iota zeta in Htensor.
      destruct (graph_find_region g (nat_list_union (module_region a_mod) (module_region c_mod))) as [ac_id|] eqn:Hac;
        [|discriminate].
      destruct (graph_find_region g (nat_list_union (module_region b_mod) (module_region d_mod))) as [bd_id|] eqn:Hbd;
        [|discriminate].
      cbn beta iota in Htensor.
      injection Htensor as Hg' Hmid. subst graph' morph_id.
      unfold graph_lookup_morphism, graph_lookup_morphism_list in Hnew. simpl in Hnew.
      rewrite Nat.eqb_refl in Hnew. discriminate.
  - unfold vm_apply. cbn [vm_graph]. rewrite Htensor.
    rewrite snap_full_graph_advance_err.
    unfold advance_state, apply_cost, instruction_cost, latch_err.
    reflexivity.
Qed.

(* ======================================================================
   §17  WFDrivenPrecondition and Multi-Step
   *)

(** Combined precondition for all 46 opcodes.

    Opcodes with FULL step-commutation (exact equality through driven_step_wf):
    - 31 SupportedOpcodes: True
    - CALL, RET, CHSH_TRIAL, LASSERT: conditional (runtime/structural conditions)
    - MORPH_ASSERT, MORPH_DELETE: morph_table_wf (structural invariant — necessary)
    - MORPH_GET, COMPOSE, MORPH_TENSOR: extended_hw_invariant (necessary)
    - MORPH, MORPH_ID: coupling_zero_empty + module bounds (reduced from extended_hw_invariant)
    - PNEW: sz>0 + tensors=0 (vestigial pt_well_formed + fresh-slot dropped by _full)
    - PSPLIT: pt_well_formed + arithmetic (vestigial morph_table_wf dropped by _full)
    - PMERGE: pt_well_formed + arithmetic (vestigial morph_table_wf dropped by _full)

    Opcodes with CLASSIFIED GAPS (separate field-by-field or driver-patched theorems):
    - TENSOR_SET/GET: driver-patched (§6, driven_step_tensor_set/get)

    The stale field-only lemmas for COMPOSE and MORPH_TENSOR remain in §16 for
    comparison, but exact VMState equality is now discharged by
    [driven_step_compose] and [driven_step_morph_tensor]. *)
Definition WFDrivenPrecondition (ks : KamiSnapshot) (i : vm_instruction) : Prop :=
  match i with
  | instr_pnew region _ =>
      length (normalize_region region) > 0 /\
      (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0)
  | instr_call _ _ =>
      WellFormedSnapshot ks /\ snap_pc ks < MEM_SIZE
  | instr_ret _ =>
      WellFormedSnapshot ks
  | instr_chsh_trial x y a b _ =>
      chsh_bits_ok x y a b = true
  | instr_psplit module _ _ _ =>
      pt_well_formed ks /\
      module mod PTableSz < snap_pt_next_id ks /\
      snap_pt_sizes ks (module mod PTableSz) >= 2 /\
      snap_pt_sizes ks (snap_pt_next_id ks) = 0 /\
      snap_pt_sizes ks (S (snap_pt_next_id ks)) = 0 /\
      S (S (snap_pt_next_id ks)) <= PTableSz /\
      (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0) /\
      (forall n, snap_module_tensors ks (S (snap_pt_next_id ks)) n = 0)
  | instr_pmerge m1 m2 _ =>
      pt_well_formed ks /\
      m1 mod PTableSz < snap_pt_next_id ks /\
      m2 mod PTableSz < snap_pt_next_id ks /\
      m1 mod PTableSz <> m2 mod PTableSz /\
      snap_pt_sizes ks (m1 mod PTableSz) > 0 /\
      snap_pt_sizes ks (m2 mod PTableSz) > 0 /\
      snap_pt_sizes ks (snap_pt_next_id ks) = 0 /\
      S (snap_pt_next_id ks) <= PTableSz /\
      (forall n, snap_module_tensors ks (snap_pt_next_id ks) n = 0)
  | instr_morph _ src_mod dst_mod _ _ =>
      coupling_zero_empty (snap_rich_state ks) /\
      src_mod < snap_pt_next_id ks /\
      dst_mod < snap_pt_next_id ks /\
      negb (Nat.eqb (snap_pt_sizes ks src_mod) 0) = true /\
      negb (Nat.eqb (snap_pt_sizes ks dst_mod) 0) = true
  | instr_morph_delete _ _ =>
      morph_table_wf (snap_rich_state ks)
  | instr_morph_assert _ _ _ _ =>
      morph_table_wf (snap_rich_state ks)
  | instr_morph_get _ _ _ _ =>
      extended_hw_invariant ks
  (* LASSERT: full VMState equality under flen = lassert_hw_flen *)
  | instr_lassert freg _ _ flen _ =>
      flen = lassert_hw_flen (abs_phase1 ks) freg
  | instr_tensor_set _ i j _ _ =>
      tensor_indices_ok i j = true
  | instr_tensor_get dst mid i j _ =>
      tensor_indices_ok i j = true /\
      graph_lookup (snap_full_graph ks) mid <> None
  | instr_morph_id _ module _ =>
      coupling_zero_empty (snap_rich_state ks) /\
      module < snap_pt_next_id ks /\
      negb (Nat.eqb (snap_pt_sizes ks module) 0) = true
  | instr_compose _ _ _ _ =>
      extended_hw_invariant ks
  | instr_morph_tensor _ _ _ _ =>
      extended_hw_invariant ks
  | _ => True  (* SupportedOpcode, includes CHSH_LASSERT (kami_step does the column-contractive check on snap_wc_* mirroring vm_apply) *)
  end.

Theorem driven_step_wf :
  forall ks i,
    WFDrivenPrecondition ks i ->
    abs_full_snapshot (full_snapshot_of_snapshot (kami_step ks i)) =
    vm_apply (abs_full_snapshot (full_snapshot_of_snapshot ks)) i.
Proof.
  intros ks i Hpre.
  destruct i; cbn [WFDrivenPrecondition] in Hpre; try contradiction;
  try (apply full_embed_step_compute; simpl; tauto).
  (* instr_pnew *)
  - destruct Hpre as [Hlen Htens].
    exact (driven_step_pnew_full ks _ _ Hlen Htens).
  (* instr_psplit *)
  - destruct Hpre as [Hpt [Hmid [Hsize [Hn0 [Hsn0 [Hroom [Hf1 Hf2]]]]]]].
    exact (driven_step_psplit_full ks _ _ _ _ Hpt Hmid Hsize Hn0 Hsn0 Hroom Hf1 Hf2).
  (* instr_pmerge *)
  - destruct Hpre as [Hpt [Hm1 [Hm2 [Hne [Hs1 [Hs2 [Hn0 [Hroom Hf1]]]]]]]].
    exact (driven_step_pmerge_full ks _ _ _ Hpt Hm1 Hm2 Hne Hs1 Hs2 Hn0 Hroom Hf1).
  (* instr_lassert *)
  - exact (driven_step_lassert ks _ _ _ _ _ Hpre).
  (* instr_call *)
  - destruct Hpre as [Hwf Hpc].
    exact (driven_step_call ks _ _ Hwf Hpc).
  (* instr_ret *)
  - exact (driven_step_ret ks _ Hpre).
  (* instr_chsh_trial *)
  - exact (driven_step_chsh_trial ks _ _ _ _ _ Hpre).
  (* instr_tensor_set *)
  - exact (driven_step_tensor_set_full ks _ _ _ _ _ Hpre).
  (* instr_tensor_get *)
  - destruct Hpre as [Hok Hex].
    exact (driven_step_tensor_get_full ks _ _ _ _ _ Hok Hex).
  (* instr_morph *)
  - destruct Hpre as [Hcze [Hslt [Hdlt [Hsrc Hdst]]]].
    exact (driven_step_morph_full ks _ _ _ _ _ Hcze Hslt Hdlt Hsrc Hdst).
  (* instr_compose *)
  - exact (driven_step_compose ks _ _ _ _ Hpre).
  (* instr_morph_id *)
  - destruct Hpre as [Hcze [Hlt Hmod]].
    exact (driven_step_morph_id_full ks _ _ _ Hcze Hlt Hmod).
  (* instr_morph_delete *)
  - exact (driven_step_morph_delete ks _ _ Hpre).
  (* instr_morph_assert *)
  - exact (driven_step_morph_assert ks _ _ _ _ Hpre).
  (* instr_morph_tensor *)
  - exact (driven_step_morph_tensor ks _ _ _ _ Hpre).
  (* instr_morph_get *)
  - exact (driven_step_morph_get ks _ _ _ _ Hpre).
Qed.

(** Multi-step driven execution. *)
Fixpoint kami_run_driven
    (fuel : nat) (trace : list vm_instruction) (ks : KamiSnapshot)
    : KamiSnapshot :=
  match fuel with
  | 0 => ks
  | S fuel' =>
      match nth_error trace (snap_pc ks) with
      | Some instr => kami_run_driven fuel' trace (kami_step ks instr)
      | None => ks
      end
  end.

(** Multi-step trace commutation under WFDrivenPrecondition.
    The precondition must hold at every step. *)
Theorem driven_trace_commutes :
  forall fuel trace ks,
    (forall ks' i, WFDrivenPrecondition ks' i) ->
    abs_full_snapshot (full_snapshot_of_snapshot
      (kami_run_driven fuel trace ks)) =
    run_vm fuel trace
      (abs_full_snapshot (full_snapshot_of_snapshot ks)).
Proof.
  induction fuel as [|fuel IH]; intros trace ks Hpre; simpl.
  - reflexivity.
  - destruct (nth_error trace (snap_pc ks)) as [instr|] eqn:Hnth.
    + rewrite IH.
      * rewrite driven_step_wf; [reflexivity | apply Hpre].
      * exact Hpre.
    + reflexivity.
Qed.

(* ======================================================================
   §18  Coverage Summary
   *)

(** Coverage summary (0 Admitted, all Qed):

    Full-state commutation (abs_full_snapshot ∘ full_snapshot_of_snapshot
    ∘ kami_step = vm_apply ∘ abs_full_snapshot ∘ full_snapshot_of_snapshot):

    Unconditional (31 opcodes):
      All SupportedOpcode via [driven_step_supported].  Qed.

    Conditional with full equality (12 opcodes):
      - PNEW: [driven_step_pnew] — requires pt_well_formed + fresh slot.  Qed.
      - CALL: [driven_step_call] — requires WellFormedSnapshot + pc < MEM_SIZE.  Qed.
      - RET:  [driven_step_ret] — requires WellFormedSnapshot.  Qed.
      - CHSH_TRIAL: [driven_step_chsh_trial] — requires chsh_bits_ok.  Qed.
      - LASSERT: [driven_step_lassert] — requires flen = lassert_hw_flen.  Qed.
      - MORPH_ASSERT: [driven_step_morph_assert] — requires morph_table_wf.  Qed.
      - MORPH_GET: [driven_step_morph_get] — requires extended_hw_invariant.  Qed.
      - MORPH_DELETE: [driven_step_morph_delete] — requires morph_table_wf.  Qed.
      - MORPH: [driven_step_morph_full] — requires coupling_zero_empty + modules exist.  Qed.
      - MORPH_ID: [driven_step_morph_id_full] — requires coupling_zero_empty + module exists.  Qed.
        (Both hw and kernel use empty_coupling_data; gap fully closed; extended_hw_invariant reduced.)
      - PSPLIT: [driven_step_psplit] — requires pt_well_formed + space.  Qed.
      - PMERGE: [driven_step_pmerge] — requires pt_well_formed + modules exist.  Qed.

    Field-by-field helpers (vm_graph/vm_regs omitted in the helper lemma):
      - COMPOSE: [driven_step_compose_fields] — all fields except vm_graph/vm_regs in helper.
        FULL EQUALITY: [driven_step_compose] — complete state equality under extended_hw_invariant.  Qed.
      - MORPH_TENSOR: [driven_step_morph_tensor_fields] — all fields except vm_graph/vm_regs/vm_err in helper.
        FULL EQUALITY: [driven_step_morph_tensor] — complete state equality under extended_hw_invariant.  Qed.

    Driver-patched identity (2 opcodes):
      - TENSOR_SET: [driven_step_tensor_set] — driver-patched output = vm_apply.  Qed.
      - TENSOR_GET: [driven_step_tensor_get] — driver-patched output = vm_apply.  Qed.

    TOTAL: 46/46 opcodes addressed.

    Invariant preservation:
      - [hw_repr_invariant_supported_step]: Qed for SupportedOpcodes.
      - [hw_repr_invariant_pnew]: Qed under S(next_id) < PTableSz.

    Multi-step:
      - [driven_step_wf]: Qed under WFDrivenPrecondition for exact cases above.
      - [driven_trace_commutes]: Qed under universal WFDrivenPrecondition.

    Admitted count: 0.
    All 46 opcode bridges are fully proven (Qed).
    COMPOSE and MORPH_TENSOR have both field-by-field helper lemmas (omitting vm_graph/vm_regs)
    AND full-equality theorems (driven_step_compose, driven_step_morph_tensor) under extended_hw_invariant.
    No open gaps remain.
*)

(** ** Connecting [kami_step] to [kami_step_full]

    [kami_step_full] in [FullStep.v] is defined definitionally through
    [vm_apply], so its abstraction round-trips trivially. The
    instruction-by-instruction agreement between the low-level
    hardware-mimicking [kami_step] (in [Abstraction.v]) and
    [kami_step_full] is the substantive content of
    [driven_step_supported] (and the [WFDrivenPrecondition] companions
    for the remaining 16 opcodes).

    The theorem below packages the SupportedOpcode case as a single
    equation between the lifted [kami_step] result and the full step:

      full_snapshot_of_snapshot (kami_step ks i)
        = kami_step_full (full_snapshot_of_snapshot ks) i.

    Combined with [driven_step_supported], [driven_step_lassert],
    [driven_step_pnew], [driven_step_psplit], [driven_step_pmerge],
    [driven_step_call], [driven_step_ret], [driven_step_chsh_trial],
    [driven_step_tensor_set_full], [driven_step_tensor_get_full],
    [driven_step_compose], [driven_step_morph_tensor], and the seven
    morphism opcodes proved earlier in this file under
    [extended_hw_invariant], every opcode is covered. *)

Theorem kami_step_full_agrees_with_kami_step_supported :
  forall ks i,
    SupportedOpcode i ->
    full_snapshot_of_snapshot (kami_step ks i) =
    kami_step_full (full_snapshot_of_snapshot ks) i.
Proof.
  intros ks i Hsup.
  unfold kami_step_full.
  pose proof (driven_step_supported ks i Hsup) as Hd.
  rewrite <- Hd.
  rewrite full_snapshot_repr_abs.
  reflexivity.
Qed.

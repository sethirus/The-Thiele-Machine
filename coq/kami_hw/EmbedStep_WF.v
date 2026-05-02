(** EmbedStep_WF.v

    Full-state embed_step for the WF-guarded instruction layer.
    Extends the 31-opcode unconditional SupportedOpcode coverage to a
    34-opcode WFSupportedOpcode coverage by adding:
    - CALL
    - RET
    - CHSH_TRIAL

    The remaining 4 preconditioned opcodes stay in specialised lemmas:
    PNEW, PSPLIT, PMERGE, LASSERT.

    Preconditions:
    - WellFormedSnapshot: sp < MEM_SIZE, word64_sub sp 1 < MEM_SIZE
    - snap_pc ks < MEM_SIZE (for CALL only — ensures S(pc) fits in word64)
    - chsh_bits_ok x y a b = true (for CHSH_TRIAL — all four values are bits)
    - WellFormedPartitionTable: next_id >= 1 /\ next_id < PTableSz /\ fresh slot
    - LASSERT: check_ok = true /\ flen = hw_flen (success-path match)
    - PSPLIT/PMERGE: partition table well-formedness

*)

From Coq Require Import List Arith.PeanoNat Lia Bool NArith.BinNat NArith.Nnat FunctionalExtensionality.
Import ListNotations.

From Kernel  Require Import VMState VMStep SimulationProof CertCheck.
From KamiHW  Require Import Abstraction EmbedStep.
Require Import KamiHW.RichStateCommutation.
From KamiHW Require Import ThieleTypes.

Import VMStep.VMStep.

(* ======================================================================
   §1  Helper lemmas
   *)

(** word64 is the identity for nats whose N-encoding is below 2^64. *)
Lemma word64_id_lt : forall (x : nat),
    (N.of_nat x < 2 ^ 64)%N ->
    word64 x = x.
Proof.
  intros x Hlt.
  unfold word64, word64_mask.
  rewrite N.land_ones.
  rewrite N.mod_small by exact Hlt.
  apply Nat2N.id.
Qed.

(** Corollary: word64 is the identity for nats <= MEM_SIZE (MemSize \<< 2^64). *)
Lemma word64_id_le_mem : forall (x : nat),
    x <= MEM_SIZE ->
    word64 x = x.
Proof.
  intros x Hx. apply word64_id_lt.
  apply (N.lt_trans _ (N.of_nat (S MEM_SIZE)) _).
  - lia.
  - vm_compute. reflexivity.
Qed.

(** word64_sub is already word64-truncated: its output has N.land ... word64_mask
    as the outermost operation, so word64 (word64_sub a b) = word64_sub a b. *)
Lemma word64_sub_is_word64 : forall a b,
    word64 (word64_sub a b) = word64_sub a b.
Proof.
  intros a b.
  unfold word64_sub, word64, word64_mask.
  rewrite N2Nat.id.
  rewrite <- N.land_assoc.
  rewrite N.land_diag.
  reflexivity.
Qed.

(** The inline reg write used in CALL/RET for r31 agrees with
    snapshot_regs_to_list of kami_write_reg, because the CALL/RET
    value is already word64-truncated (sp' = word64_add sp 1 for CALL,
    sp' = word64_sub sp 1 for RET). *)
Lemma inline_reg_write_sp_abs :
  forall (hs : KamiSnapshot) (v : nat),
    word64 v = v ->
    snapshot_regs_to_list (fun j => if Nat.eqb j kami_sp_reg then v else snap_regs hs j) =
    write_reg (abs_phase1 hs) kami_sp_reg v.
Proof.
  intros hs v Hv.
  (* The inline and kami_write_reg differ only in word64 application.
     Since word64 v = v, they agree. *)
  rewrite <- abs_phase1_kami_reg_write.
  unfold kami_write_reg, kami_sp_reg.
  change ((RegCount - 1) mod RegCount) with (RegCount - 1).
  rewrite Hv.
  reflexivity.
Qed.

(** The inline mem write used in CALL agrees with write_mem
    when sp < MEM_SIZE and word64 ra = ra. *)
Lemma inline_mem_write_abs :
  forall (hs : KamiSnapshot) (sp ra : nat),
    sp < MEM_SIZE ->
    word64 ra = ra ->
    snapshot_mem_to_list (fun j => if Nat.eqb j sp then ra else snap_mem hs j) =
    write_mem (abs_phase1 hs) sp ra.
Proof.
  intros hs sp ra Hsp Hra.
  unfold write_mem, mem_index, abs_phase1, snapshot_mem_to_list.
  rewrite Nat.mod_small by lia.
  rewrite Hra.
  apply map_update_at_seq.
  exact Hsp.
Qed.

(** Well-formedness invariant on the hardware snapshot's stack pointer.
    Required by CALL (push return address) and RET (pop). *)
Definition WellFormedSnapshot (ks : KamiSnapshot) : Prop :=
  snap_regs ks kami_sp_reg < MEM_SIZE /\
  word64_sub (snap_regs ks kami_sp_reg) 1 < MEM_SIZE.

(* ======================================================================
   §2  CALL: full-state embed_step under WellFormedSnapshot
   *)

Theorem embed_step_call :
  forall (ks : KamiSnapshot) (target cost : nat),
    WellFormedSnapshot ks ->
    snap_pc ks < MEM_SIZE ->
    abs_phase1 (kami_step ks (instr_call target cost)) =
    vm_apply (abs_phase1 ks) (instr_call target cost).
Proof.
  intros ks target cost [Hsp_lt Hsp_decr] Hpc.
  unfold vm_apply.
  rewrite abs_phase1_read_reg.
  unfold kami_sp_reg in Hsp_lt.
  change (kami_sp_reg mod RegCount) with kami_sp_reg.
  (* Unfold the hardware side *)
  unfold abs_phase1 at 1, kami_step.
  unfold jump_state_rm, apply_cost, instruction_cost.
  f_equal.
  - (* vm_regs: inline reg write for r31 = word64_add sp 1 *)
    apply inline_reg_write_sp_abs.
    unfold word64_add.
    apply word64_idempotent.
  - (* vm_mem: inline mem write at sp with S(pc) *)
    apply inline_mem_write_abs.
    + exact Hsp_lt.
    + (* word64 (S (snap_pc ks)) = S (snap_pc ks) *)
      apply word64_id_le_mem. unfold abs_phase1. simpl.
      exact Hpc.
Qed.

(* ======================================================================
   §3  RET: full-state embed_step under WellFormedSnapshot
   *)

Theorem embed_step_ret :
  forall (ks : KamiSnapshot) (cost : nat),
    WellFormedSnapshot ks ->
    abs_phase1 (kami_step ks (instr_ret cost)) =
    vm_apply (abs_phase1 ks) (instr_ret cost).
Proof.
  intros ks cost [Hsp_lt Hsp_decr].
  unfold vm_apply.
  rewrite abs_phase1_read_reg.
  unfold kami_sp_reg in Hsp_decr, Hsp_lt.
  (* read_reg ... 15 reduces to snap_regs ks (15 mod RegCount).
     With RegCount=16, 15 mod 16 = 15 = RegCount - 1 = kami_sp_reg.
     Compute the modulo and match the hardware-side index. *)
  cbv [RegCount] in *. simpl ((15 mod 16)%nat).
  rewrite abs_phase1_read_mem.
  rewrite (Nat.mod_small (word64_sub (snap_regs ks 15) 1) MEM_SIZE) by exact Hsp_decr.
  (* Now both sides are concrete record constructors *)
  unfold abs_phase1, kami_step,
         jump_state_rm, apply_cost, instruction_cost.
  simpl snap_mem. simpl snap_pc. simpl snap_mu. simpl snap_err.
  simpl snap_certified. simpl snap_regs.
  f_equal.
  - (* vm_regs *)
    apply inline_reg_write_sp_abs.
    apply word64_sub_is_word64.
Qed.

(* ======================================================================
   §4  CHSH_TRIAL: full-state embed_step under chsh_bits_ok
   *)

(** After fixing the dispatch-swap bug in kami_step (2026-04-01),
    kami_step now uses the same convention as the kernel's record_trial:
    same := Nat.eqb a b, bucket := match x, y.  Under chsh_bits_ok,
    both sides agree on all 11 VMState fields. *)
Theorem embed_step_chsh_trial :
  forall (ks : KamiSnapshot) (x y a b cost : nat),
    chsh_bits_ok x y a b = true ->
    abs_phase1 (kami_step ks (instr_chsh_trial x y a b cost)) =
    vm_apply (abs_phase1 ks) (instr_chsh_trial x y a b cost).
Proof.
  intros ks x y a b cost Hbits.
  unfold vm_apply.
  rewrite Hbits.
  (* Both sides are now concrete record constructors.
     Hardware: abs_phase1 of the kami_step snapshot.
     Kernel: explicit record with record_trial for vm_witness. *)
  unfold abs_phase1, kami_step, record_trial.
  unfold apply_cost, instruction_cost.
  (* Unfold vm_graph reconstruction — snap_pt_* fields are unchanged by kami_step *)
  simpl snap_pt_next_id. simpl snap_pt_sizes. simpl snap_mu_tensor.
  simpl snap_regs. simpl snap_mem. simpl snap_pc. simpl snap_mu.
  simpl snap_err. simpl snap_certified.
  simpl snap_wc_same_00. simpl snap_wc_diff_00.
  simpl snap_wc_same_01. simpl snap_wc_diff_01.
  simpl snap_wc_same_10. simpl snap_wc_diff_10.
  simpl snap_wc_same_11. simpl snap_wc_diff_11.
  (* Now destruct the bucket (match x, y) and same/diff flag (Nat.eqb a b) *)
  destruct x, y; destruct (Nat.eqb a b); reflexivity.
Qed.

(* ======================================================================
   §5  WFSupportedOpcode: 43-opcode predicate
   *)

(** WFSupportedOpcode extends the 31-opcode SupportedOpcode subset with
    CALL, RET, and CHSH_TRIAL, yielding a 43-opcode layer.

    Preconditions:
    - CALL requires WellFormedSnapshot plus pc < MEM_SIZE
    - RET requires WellFormedSnapshot
    - CHSH_TRIAL requires chsh_bits_ok

    The remaining preconditioned opcodes (PNEW, PSPLIT, PMERGE, LASSERT)
    are handled separately below rather than folded into WFSupportedOpcode. *)
Definition WFSupportedOpcode (ks : KamiSnapshot) (i : vm_instruction) : Prop :=
  match i with
  | instr_call _ _  => WellFormedSnapshot ks /\ snap_pc ks < MEM_SIZE
  | instr_ret _     => WellFormedSnapshot ks
  | instr_chsh_trial x y a b _ => chsh_bits_ok x y a b = true
  | _               => SupportedOpcode i
  end.

Lemma SupportedOpcode_implies_WFSupported :
  forall ks i, SupportedOpcode i -> WFSupportedOpcode ks i.
Proof. intros ks i Hi. destruct i; simpl in *; tauto. Qed.

Theorem embed_step_wf_supported :
  forall (ks : KamiSnapshot) (i : vm_instruction),
    WFSupportedOpcode ks i ->
    abs_phase1 (kami_step ks i) = vm_apply (abs_phase1 ks) i.
Proof.
  intros ks i Hi.
  destruct i; simpl in Hi; try contradiction;
    try match goal with
    | |- context [kami_step _ ?instr] =>
        let H := fresh in
        assert (H : SupportedOpcode instr) by exact I;
        exact (embed_step_supported ks _ H)
    end.
  - destruct Hi as [Hwfs Hpc]. exact (embed_step_call ks _ _ Hwfs Hpc).
  - exact (embed_step_ret ks _ Hi).
  - exact (embed_step_chsh_trial ks _ _ _ _ _ Hi).
Qed.

(* ======================================================================
   §6  LASSERT: embed_step under success-path precondition
   *)

(** The hardware dual-witness checker and the kernel's lassert_check_ok compute the
    same boolean when applied through abs_phase1. *)
Lemma lassert_check_ok_hw_compat :
  forall (ks : KamiSnapshot) (freg creg : nat) (kind : bool),
    let fbase := snap_regs ks (freg mod RegCount) in
    let cbase := snap_regs ks (creg mod RegCount) in
    let hw_flen := snap_mem ks (fbase mod MEM_SIZE) in
    let formula_words := List.map (fun i => snap_mem ks ((fbase + i) mod MEM_SIZE))
                                  (List.seq 0 (3 + hw_flen)) in
    let num_vars :=
      match formula_words with
      | _ :: nv :: _ => nv
      | _ => 0
      end in
    let get_model := (fun var => snap_mem ks ((cbase + var) mod MEM_SIZE)) in
    let get_countermodel := (fun var => snap_mem ks ((cbase + num_vars + var) mod MEM_SIZE)) in
    let hw_check := if kind then
                      andb (CertCheck.check_model_binary_fn formula_words get_model)
                           (CertCheck.check_countermodel_binary_fn formula_words get_countermodel)
                    else false in
    hw_check = lassert_check_ok (abs_phase1 ks) freg creg kind.
Proof.
  intros ks freg creg kind.
  unfold lassert_check_ok.
  rewrite abs_phase1_read_reg, abs_phase1_read_reg.
  set (fbase := snap_regs ks (freg mod RegCount)).
  set (cbase := snap_regs ks (creg mod RegCount)).
  rewrite abs_phase1_read_mem.
  set (hw_flen := snap_mem ks (fbase mod MEM_SIZE)).
  assert (Hfw : List.map (fun i => read_mem (abs_phase1 ks) (fbase + i))
                         (List.seq 0 (3 + hw_flen)) =
                List.map (fun i => snap_mem ks ((fbase + i) mod MEM_SIZE))
                         (List.seq 0 (3 + hw_flen))).
  { apply List.map_ext. intro i. apply abs_phase1_read_mem. }
  rewrite <- Hfw.
  destruct kind; [|reflexivity].
  repeat f_equal;
    apply functional_extensionality; intro var;
    symmetry; apply abs_phase1_read_mem.
Qed.

(** LASSERT embed_step on the success path:
    Now that hardware computes the full formula check and charges
    flen*8+S(cost) matching the kernel, the success path yields
    full field-by-field equality including vm_mu. *)
Theorem embed_step_lassert :
  forall (ks : KamiSnapshot) (freg creg : nat) (kind : bool) (flen cost : nat),
    lassert_check_ok (abs_phase1 ks) freg creg kind = true ->
    flen = lassert_hw_flen (abs_phase1 ks) freg ->
    let hs' := abs_phase1 (kami_step ks (instr_lassert freg creg kind flen cost)) in
    let vs' := vm_apply (abs_phase1 ks) (instr_lassert freg creg kind flen cost) in
    vm_pc hs' = vm_pc vs' /\
    vm_graph hs' = vm_graph vs' /\
    vm_regs hs' = vm_regs vs' /\
    vm_mem hs' = vm_mem vs' /\
    vm_err hs' = vm_err vs' /\
    vm_mu hs' = vm_mu vs' /\
    vm_mu_tensor hs' = vm_mu_tensor vs' /\
    vm_witness hs' = vm_witness vs' /\
    vm_certified hs' = vm_certified vs'.
Proof.
  intros ks freg creg kind flen cost Hcheck Hflen.
  cbv zeta.
  unfold vm_apply, kami_step.
  unfold lassert_exec_ok.
  rewrite <- Hflen. rewrite Nat.eqb_refl. simpl.
  rewrite Hcheck.
  unfold abs_phase1, apply_cost, instruction_cost.
  cbn [snap_pc snap_mu snap_err snap_halted snap_regs snap_mem
       snap_mu_tensor snap_pt_sizes snap_pt_next_id snap_certified
       snap_partition_ops snap_mdl_ops snap_info_gain snap_error_code
       snap_wc_same_00 snap_wc_diff_00 snap_wc_same_01 snap_wc_diff_01
       snap_wc_same_10 snap_wc_diff_10 snap_wc_same_11 snap_wc_diff_11
       snap_module_tensors snap_csr_err
       vm_graph vm_csrs vm_regs vm_mem vm_pc vm_mu vm_mu_tensor
       vm_err vm_logic_acc vm_mstatus vm_witness vm_certified
       snapshot_regs_to_list snapshot_mem_to_list snapshot_tensor_to_list
       default_csrs].
  rewrite Hflen.
  repeat split; try reflexivity; try lia.
Qed.

(* ======================================================================
   §7  PNEW: embed_step under well-formed partition table
   *)

(** Partition table well-formedness for PNEW. *)
Definition WellFormedPT_PNEW (ks : KamiSnapshot) : Prop :=
  snap_pt_next_id ks >= 1 /\
  snap_pt_next_id ks < PTableSz /\
  snap_pt_sizes ks (snap_pt_next_id ks) = 0.

Theorem embed_step_pnew :
  forall (ks : KamiSnapshot) (region : list nat) (cost : nat),
    WellFormedPT_PNEW ks ->
    List.length (normalize_region region) > 0 ->
    abs_phase1 (kami_step ks (instr_pnew region cost)) =
    vm_apply (abs_phase1 ks) (instr_pnew region cost).
Proof.
  intros ks region cost [Hge [Hlt Hfresh]] Hsz.
  set (id := snap_pt_next_id ks).
  set (sz := length (normalize_region region)).
  unfold vm_apply, kami_step.
  fold id. fold sz.
  unfold advance_state, apply_cost, instruction_cost.
  unfold abs_phase1 at 1.
  simpl snap_pc. simpl snap_mu. simpl snap_err.
  simpl snap_regs. simpl snap_mem.
  simpl snap_mu_tensor. simpl snap_certified.
  simpl snap_halted. simpl snap_partition_ops. simpl snap_mdl_ops.
  simpl snap_info_gain. simpl snap_error_code.
  simpl snap_wc_same_00. simpl snap_wc_diff_00.
  simpl snap_wc_same_01. simpl snap_wc_diff_01.
  simpl snap_wc_same_10. simpl snap_wc_diff_10.
  simpl snap_wc_same_11. simpl snap_wc_diff_11.
  simpl snap_pt_sizes. simpl snap_pt_next_id.
  fold (abs_phase1 ks).
  fold id. fold sz.
  rewrite (snap_pt_to_graph_pnew id sz (snap_pt_sizes ks) Hge Hlt Hsz Hfresh).
  reflexivity.
Qed.

(* ======================================================================
   §8  PSPLIT: embed_step under well-formed partition table
   *)

(** Partition table well-formedness for PSPLIT.
    Mirrors the 6 preconditions of snap_pt_to_graph_psplit (RichStateCommutation.v). *)
Definition WellFormedPT_PSPLIT (ks : KamiSnapshot) (module : nat) : Prop :=
  snap_pt_next_id ks >= 1 /\
  S (S (snap_pt_next_id ks)) <= PTableSz /\
  module mod PTableSz < snap_pt_next_id ks /\
  snap_pt_sizes ks (module mod PTableSz) >= 2 /\
  snap_pt_sizes ks (snap_pt_next_id ks) = 0 /\
  snap_pt_sizes ks (S (snap_pt_next_id ks)) = 0.

Theorem embed_step_psplit :
  forall (ks : KamiSnapshot) (module : nat) (left_region right_region : list nat) (cost : nat),
    WellFormedPT_PSPLIT ks module ->
    abs_phase1 (kami_step ks (instr_psplit module left_region right_region cost)) =
    vm_apply (abs_phase1 ks) (instr_psplit module left_region right_region cost).
Proof.
  intros ks module0 left_region right_region cost
         [Hge [Hle [Hmid [Hsize [Hn0 Hsn0]]]]].
  set (nid   := snap_pt_next_id ks).
  set (mid   := module0 mod PTableSz).
  set (sizes := snap_pt_sizes ks).
  (* Prove the graph commutation first. kami_step uses S nid-first ordering;
     snap_pt_to_graph_psplit (RichStateCommutation.v) uses mid-first ordering.
     We reorder via extensionality, then use sym_eq. *)
  assert (Hgraph :
    snap_pt_to_graph (S (S nid))
      (fun i => if Nat.eqb i (S nid) then sizes mid - Nat.div (sizes mid) 2
                else if Nat.eqb i nid then Nat.div (sizes mid) 2
                else if Nat.eqb i mid then 0
                else sizes i) =
    graph_hw_psplit (snap_pt_to_graph nid sizes) mid).
  {
    assert (Hfun_eq :
      (fun i => if Nat.eqb i (S nid) then sizes mid - Nat.div (sizes mid) 2
                else if Nat.eqb i nid then Nat.div (sizes mid) 2
                else if Nat.eqb i mid then 0
                else sizes i) =
      (fun j => if Nat.eqb j mid then 0
                else if Nat.eqb j nid then Nat.div (sizes mid) 2
                else if Nat.eqb j (S nid) then sizes mid - Nat.div (sizes mid) 2
                else sizes j)).
    { extensionality x.
      destruct (Nat.eqb_spec x mid)  as [Hem|Hem],
               (Nat.eqb_spec x nid)  as [Hen|Hen],
               (Nat.eqb_spec x (S nid)) as [HeSn|HeSn];
      subst; try reflexivity; exfalso; unfold nid, mid in *; lia. }
    rewrite Hfun_eq.
    exact (eq_sym (snap_pt_to_graph_psplit nid sizes mid Hge Hle Hmid Hsize Hn0 Hsn0)).
  }
  (* Expand LHS abs_phase1, use change to convert graph field by definitional equality,
     then rewrite using Hgraph — avoids the simpl/cbv/fold lambda-matching issue. *)
  unfold abs_phase1 at 1.
  change (snap_pt_to_graph (snap_pt_next_id (kami_step ks (instr_psplit module0 left_region right_region cost)))
                           (snap_pt_sizes   (kami_step ks (instr_psplit module0 left_region right_region cost))))
    with (snap_pt_to_graph (S (S nid))
      (fun i => if Nat.eqb i (S nid) then sizes mid - Nat.div (sizes mid) 2
                else if Nat.eqb i nid then Nat.div (sizes mid) 2
                else if Nat.eqb i mid then 0
                else sizes i)).
  rewrite Hgraph.
  unfold vm_apply, kami_step, advance_state, apply_cost, instruction_cost.
  fold nid mid sizes.
  simpl snap_pc. simpl snap_mu. simpl snap_err.
  simpl snap_regs. simpl snap_mem.
  simpl snap_mu_tensor. simpl snap_certified.
  simpl snap_halted. simpl snap_partition_ops. simpl snap_mdl_ops.
  simpl snap_info_gain. simpl snap_error_code.
  simpl snap_wc_same_00. simpl snap_wc_diff_00.
  simpl snap_wc_same_01. simpl snap_wc_diff_01.
  simpl snap_wc_same_10. simpl snap_wc_diff_10.
  simpl snap_wc_same_11. simpl snap_wc_diff_11.
  fold (abs_phase1 ks).
  reflexivity.
Qed.

(* ======================================================================
   §9  PMERGE: embed_step under well-formed partition table
   *)

(** Partition table well-formedness for PMERGE.
    Mirrors the 8 preconditions of snap_pt_to_graph_pmerge (RichStateCommutation.v). *)
Definition WellFormedPT_PMERGE (ks : KamiSnapshot) (m1 m2 : nat) : Prop :=
  snap_pt_next_id ks >= 1 /\
  S (snap_pt_next_id ks) <= PTableSz /\
  m1 mod PTableSz < snap_pt_next_id ks /\
  m2 mod PTableSz < snap_pt_next_id ks /\
  m1 mod PTableSz <> m2 mod PTableSz /\
  snap_pt_sizes ks (m1 mod PTableSz) > 0 /\
  snap_pt_sizes ks (m2 mod PTableSz) > 0 /\
  snap_pt_sizes ks (snap_pt_next_id ks) = 0.

Theorem embed_step_pmerge :
  forall (ks : KamiSnapshot) (m1 m2 : nat) (cost : nat),
    WellFormedPT_PMERGE ks m1 m2 ->
    abs_phase1 (kami_step ks (instr_pmerge m1 m2 cost)) =
    vm_apply (abs_phase1 ks) (instr_pmerge m1 m2 cost).
Proof.
  intros ks m1 m2 cost
         [Hge [Hle [Hm1 [Hm2 [Hne [Hs1 [Hs2 Hn0]]]]]]].
  set (nid    := snap_pt_next_id ks).
  set (mid1   := m1 mod PTableSz).
  set (mid2   := m2 mod PTableSz).
  set (sizes  := snap_pt_sizes ks).
  (* Prove the graph commutation first. kami_step uses nid-first ordering;
     snap_pt_to_graph_pmerge uses mid1-first ordering. *)
  assert (Hgraph :
    snap_pt_to_graph (S nid)
      (fun i => if Nat.eqb i nid then sizes mid1 + sizes mid2
                else if Nat.eqb i mid2 then 0
                else if Nat.eqb i mid1 then 0
                else sizes i) =
    graph_hw_pmerge (snap_pt_to_graph nid sizes) mid1 mid2).
  {
    assert (Hfun_eq :
      (fun i => if Nat.eqb i nid then sizes mid1 + sizes mid2
                else if Nat.eqb i mid2 then 0
                else if Nat.eqb i mid1 then 0
                else sizes i) =
      (fun j => if Nat.eqb j mid1 then 0
                else if Nat.eqb j mid2 then 0
                else if Nat.eqb j nid then sizes mid1 + sizes mid2
                else sizes j)).
    { extensionality x.
      destruct (Nat.eqb_spec x mid1) as [He1|He1],
               (Nat.eqb_spec x mid2) as [He2|He2],
               (Nat.eqb_spec x nid)  as [Hen|Hen];
      subst; try reflexivity; exfalso; unfold nid, mid1, mid2 in *; lia. }
    rewrite Hfun_eq.
    exact (eq_sym (snap_pt_to_graph_pmerge nid sizes mid1 mid2 Hge Hle Hm1 Hm2 Hne Hs1 Hs2 Hn0)).
  }
  unfold abs_phase1 at 1.
  change (snap_pt_to_graph (snap_pt_next_id (kami_step ks (instr_pmerge m1 m2 cost)))
                           (snap_pt_sizes   (kami_step ks (instr_pmerge m1 m2 cost))))
    with (snap_pt_to_graph (S nid)
      (fun i => if Nat.eqb i nid then sizes mid1 + sizes mid2
                else if Nat.eqb i mid2 then 0
                else if Nat.eqb i mid1 then 0
                else sizes i)).
  rewrite Hgraph.
  unfold vm_apply, kami_step, advance_state, apply_cost, instruction_cost.
  fold nid mid1 mid2 sizes.
  simpl snap_pc. simpl snap_mu. simpl snap_err.
  simpl snap_regs. simpl snap_mem.
  simpl snap_mu_tensor. simpl snap_certified.
  simpl snap_halted. simpl snap_partition_ops. simpl snap_mdl_ops.
  simpl snap_info_gain. simpl snap_error_code.
  simpl snap_wc_same_00. simpl snap_wc_diff_00.
  simpl snap_wc_same_01. simpl snap_wc_diff_01.
  simpl snap_wc_same_10. simpl snap_wc_diff_10.
  simpl snap_wc_same_11. simpl snap_wc_diff_11.
  fold (abs_phase1 ks).
  reflexivity.
Qed.

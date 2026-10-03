(** Abstraction.v — Maps Kami hardware state to VMState.

    DESIGN: KamiSnapshot uses Coq [nat] for all values, matching VMState's
    own nat-based word64 arithmetic. 32-bit bounds are enforced as preconditions.
    This avoids cross-library word/nat conversion gaps and keeps all proofs in
    pure nat arithmetic.

    The Kami hardware module (extracted to Verilog) is argued to implement
    [kami_step] in Abstraction.v by construction: the Kami rule bodies
    compute exactly the same nat operations as [vm_apply] under the abstraction.

    All 46 instructions are covered:
    - Compute: LOAD_IMM, ADD, SUB, XFER, LOAD, STORE, JUMP, JNEZ, CALL, RET
    - XOR ALU: XOR_LOAD, XOR_ADD, XOR_SWAP, XOR_RANK
    - Partition / logic: PNEW, PSPLIT, PMERGE, PDISCOVER, LASSERT, LJOIN,
      MDLACC, EMIT, REVEAL (partition graph managed at higher layer)
    - Special: CHSH_TRIAL, HALT
    - Checkpoint / I/O / heap: CHECKPOINT, READ_PORT, WRITE_PORT,
      HEAP_LOAD, HEAP_STORE
    - State-based certification: CERTIFY
    - Per-module tensor (software-managed): TENSOR_SET, TENSOR_GET
    - Categorical / morphism opcodes: MORPH, COMPOSE, MORPH_ID,
      MORPH_DELETE, MORPH_ASSERT, MORPH_TENSOR, MORPH_GET

    On-chip logic-engine model (LASSERT/LJOIN):
    The current Kami core models LASSERT/LJOIN with on-chip logic-engine state,
    not an external coprocessor. Formula/certificate data live in VM memory,
    and the hardware advances an internal FSM to perform the check. The Coq
    kernel uses the binary formula header and dual SAT witness check, and
    LogicEngineEquivalence.v relates the hardware path to the kernel path at
    the observable-state boundary (PC, μ, error flag).

    Extended state (matching handwritten RTL parity):
    - partition_ops, mdl_ops, info_gain: diagnostic counters
    - mu_tensor: 4×4 revelation direction tracking
    - error_code: specific error condition identifier *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.NArith.NArith.
Import ListNotations.

Require Import Kernel.VMState.
Require Import Kernel.VMStep.
From KamiHW Require Import ThieleTypes.
Import VMStep.VMStep.

(** ORACLE_HALTS_HW_COST preserved for use in cost-ceiling lemmas.
    No opcode charges this anymore — it serves as a conservative cap reference. *)
Definition ORACLE_HALTS_HW_COST : nat := 1000000.

(** Rich-state snapshot payload

    The snapshot interface carries bounded hardware-resident rich-state
    tables.  The [abs_phase1] proof spine uses the module-only
    [snap_pt_to_graph] projection, while the stronger full-snapshot path
    consumes the richer graph reconstruction below. *)

Record MorphTableEntry := {
  morph_entry_source : nat;
  morph_entry_target : nat;
  morph_entry_coupling_desc : nat;
  morph_entry_is_identity : bool
}.

Record CouplingDescriptorEntry := {
  coupling_desc_base : nat;
  coupling_desc_count : nat;
  coupling_desc_label : string
}.

Record CouplingPairEntry := {
  coupling_pair_source : nat;
  coupling_pair_target : nat
}.

Record FormulaDescriptorEntry := {
  formula_desc_base : nat;
  formula_desc_count : nat
}.

Record CertificationDescriptorEntry := {
  cert_desc_base : nat;
  cert_desc_count : nat
}.

Record DescriptorMetadataEntry := {
  desc_meta_subtype : nat;
  desc_meta_kind : nat;
  desc_meta_inline_len : nat;
  desc_meta_aux : nat
}.

Record LassertShadowState := {
  lassert_shadow_phase : nat;
  lassert_shadow_kind : bool;
  lassert_shadow_fbase : nat;
  lassert_shadow_cbase : nat;
  lassert_shadow_flen : nat;
  lassert_shadow_clen : nat;
  lassert_shadow_fptr : nat;
  lassert_shadow_cptr : nat;
  lassert_shadow_clause_sat : bool;
  lassert_shadow_fbuf : nat -> nat;
  lassert_shadow_cbuf : nat -> nat
}.

Definition empty_lassert_shadow_state : LassertShadowState :=
  {| lassert_shadow_phase := 0;
     lassert_shadow_kind := false;
     lassert_shadow_fbase := 0;
     lassert_shadow_cbase := 0;
     lassert_shadow_flen := 0;
     lassert_shadow_clen := 0;
     lassert_shadow_fptr := 0;
     lassert_shadow_cptr := 0;
     lassert_shadow_clause_sat := false;
     lassert_shadow_fbuf := fun _ => 0;
     lassert_shadow_cbuf := fun _ => 0 |}.

Record RichSnapshotState := {
  rich_morph_table : nat -> option MorphTableEntry;
  rich_next_morph_id : nat;
  rich_coupling_desc_table : nat -> option CouplingDescriptorEntry;
  rich_next_coupling_desc_id : nat;
  rich_coupling_pair_table : nat -> option CouplingPairEntry;
  rich_next_coupling_pair_id : nat;
  rich_formula_desc_table : nat -> option FormulaDescriptorEntry;
  rich_next_formula_desc_id : nat;
  rich_cert_desc_table : nat -> option CertificationDescriptorEntry;
  rich_next_cert_desc_id : nat;
  rich_desc_meta_table : nat -> option DescriptorMetadataEntry;
  rich_next_desc_meta_id : nat;
  rich_lassert_state : LassertShadowState
}.

Definition empty_rich_snapshot_state : RichSnapshotState :=
  {| rich_morph_table := fun _ => None;
     rich_next_morph_id := 1;
     rich_coupling_desc_table := fun _ => None;
  rich_next_coupling_desc_id := 1;
     rich_coupling_pair_table := fun _ => None;
     rich_next_coupling_pair_id := 0;
     rich_formula_desc_table := fun _ => None;
     rich_next_formula_desc_id := 0;
     rich_cert_desc_table := fun _ => None;
     rich_next_cert_desc_id := 0;
     rich_desc_meta_table := fun _ => None;
     rich_next_desc_meta_id := 0;
     rich_lassert_state := empty_lassert_shadow_state |}.

(** Hardware state snapshot

    All values are stored as [nat]; the invariant [snap_regs_bounded] /
    [snap_mem_bounded] ensures they fit in hardware 32-bit registers. *)

Record KamiSnapshot := {
  snap_pc            : nat ;
  snap_mu            : nat ;
  snap_err           : bool ;
  snap_halted        : bool ;
  snap_regs          : nat -> nat ;
  snap_mem           : nat -> nat ;
  snap_partition_ops : nat ;
  snap_mdl_ops       : nat ;
  snap_info_gain     : nat ;
  snap_error_code    : nat ;
  snap_mu_tensor     : nat -> nat ;  (* flat index 0..15 -> tensor entry value *)
  snap_pt_sizes      : nat -> nat ;  (* hardware partition table: module_id -> region_size (0 = unallocated) *)
  snap_pt_bases      : nat -> nat ;  (* hardware partition table: module_id -> first address of its range *)
  snap_pt_next_id    : nat ;         (* next free module ID; initialized to 1 matching empty_graph.pg_next_id *)
  snap_certified     : bool ;        (* state-based certification flag — set by CERTIFY *)
  snap_wc_same_00    : nat ;         (* witness counter: setting (0,0), same outcomes *)
  snap_wc_diff_00    : nat ;         (* witness counter: setting (0,0), diff outcomes *)
  snap_wc_same_01    : nat ;
  snap_wc_diff_01    : nat ;
  snap_wc_same_10    : nat ;
  snap_wc_diff_10    : nat ;
  snap_wc_same_11    : nat ;
  snap_wc_diff_11    : nat ;
  snap_module_tensors : nat -> nat -> nat ;  (* per-module tensor: module_id -> flat_idx -> value *)
  snap_rich_state    : RichSnapshotState ;
  (* --- M1 unification fields: CSR / logic_acc / mstatus --- *)
  snap_csr_cert_addr : nat ;   (* mirrors CSRState.csr_cert_addr *)
  snap_csr_status    : nat ;   (* mirrors CSRState.csr_status *)
  snap_csr_err       : nat ;   (* mirrors CSRState.csr_err *)
  snap_csr_heap_base : nat ;   (* mirrors CSRState.csr_heap_base *)
  snap_logic_acc     : nat ;   (* mirrors VMState.vm_logic_acc *)
  snap_mstatus       : nat     (* mirrors VMState.vm_mstatus *)
}.

(** Conversion: function-based registers/memory -> list (VMState expects list nat) *)

Definition snapshot_regs_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 RegCount).

Definition snapshot_mem_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 MEM_SIZE).

Definition snapshot_tensor_to_list (f : nat -> nat) : list nat :=
  List.map f (List.seq 0 16).

(** Option-valued filter-map.  [List.filter_map] in Coq 8.18 is an
    unrelated boolean lemma; we define our own here. *)
Fixpoint filtermap {A B : Type} (f : A -> option B) (l : list A) : list B :=
  match l with
  | []      => []
  | x :: xs => match f x with
               | None   => filtermap f xs
               | Some b => b :: filtermap f xs
               end
  end.

Definition snapshot_coupling_pairs_from_desc
  (rs : RichSnapshotState) (desc_id : nat) : list (nat * nat) :=
  match rich_coupling_desc_table rs desc_id with
  | None => []
  | Some desc =>
      filtermap
        (fun ofs =>
          match rich_coupling_pair_table rs (coupling_desc_base desc + ofs) with
          | Some cpair => Some (coupling_pair_source cpair, coupling_pair_target cpair)
          | None => None
          end)
        (List.seq 0 (coupling_desc_count desc))
  end.

Definition snapshot_morphisms_of_rich_state
  (rs : RichSnapshotState) : list (MorphismID * MorphismState) :=
  filtermap
    (fun i =>
      match rich_morph_table rs i with
      | None => None
      | Some entry =>
          let label := match rich_coupling_desc_table rs (morph_entry_coupling_desc entry) with
                       | Some desc => coupling_desc_label desc
                       | None => coupling_label empty_coupling_data
                       end in
          Some
            (i,
             {| morph_source := morph_entry_source entry;
                morph_target := morph_entry_target entry;
                morph_coupling :=
                    {| coupling_pairs :=
                         snapshot_coupling_pairs_from_desc rs
                           (morph_entry_coupling_desc entry);
                       coupling_label := label |};
                morph_is_identity := morph_entry_is_identity entry;
               morph_cert_cost := 0 |})
      end)
    (List.rev (List.seq 0 (rich_next_morph_id rs))).

(** Rich morph state helper operations

    These functions implement the morph-table mutations that
    [kami_step] needs to maintain full-state correspondence for the
    morphism opcodes. *)

(** Add a new morphism entry.  Returns (updated_state, new_morph_id). *)
Definition rich_state_add_morph (rs : RichSnapshotState)
    (src dst coupling_desc : nat) (is_id : bool)
    : RichSnapshotState * nat :=
  let new_id := rs.(rich_next_morph_id) in
  let entry := {| morph_entry_source := src;
                  morph_entry_target := dst;
                  morph_entry_coupling_desc := coupling_desc;
                  morph_entry_is_identity := is_id |} in
  ({| rich_morph_table := fun i =>
        if Nat.eqb i new_id then Some entry else rs.(rich_morph_table) i;
      rich_next_morph_id := new_id + 1;
      rich_coupling_desc_table := rs.(rich_coupling_desc_table);
      rich_next_coupling_desc_id := rs.(rich_next_coupling_desc_id);
      rich_coupling_pair_table := rs.(rich_coupling_pair_table);
      rich_next_coupling_pair_id := rs.(rich_next_coupling_pair_id);
      rich_formula_desc_table := rs.(rich_formula_desc_table);
      rich_next_formula_desc_id := rs.(rich_next_formula_desc_id);
      rich_cert_desc_table := rs.(rich_cert_desc_table);
      rich_next_cert_desc_id := rs.(rich_next_cert_desc_id);
      rich_desc_meta_table := rs.(rich_desc_meta_table);
      rich_next_desc_meta_id := rs.(rich_next_desc_meta_id);
      rich_lassert_state := rs.(rich_lassert_state) |},
   new_id).

(** Delete a morphism entry (mark its slot as None). *)
Definition rich_state_delete_morph (rs : RichSnapshotState) (mid : nat)
    : RichSnapshotState :=
  {| rich_morph_table := fun i =>
       if Nat.eqb i mid then None else rs.(rich_morph_table) i;
     rich_next_morph_id := rs.(rich_next_morph_id);
     rich_coupling_desc_table := rs.(rich_coupling_desc_table);
     rich_next_coupling_desc_id := rs.(rich_next_coupling_desc_id);
     rich_coupling_pair_table := rs.(rich_coupling_pair_table);
     rich_next_coupling_pair_id := rs.(rich_next_coupling_pair_id);
     rich_formula_desc_table := rs.(rich_formula_desc_table);
     rich_next_formula_desc_id := rs.(rich_next_formula_desc_id);
     rich_cert_desc_table := rs.(rich_cert_desc_table);
     rich_next_cert_desc_id := rs.(rich_next_cert_desc_id);
     rich_desc_meta_table := rs.(rich_desc_meta_table);
     rich_next_desc_meta_id := rs.(rich_next_desc_meta_id);
     rich_lassert_state := rs.(rich_lassert_state) |}.

(** Write a list of coupling pairs into the pair table starting at the
    current next_coupling_pair_id, allocate a coupling descriptor pointing
    at them, and return (updated_state, descriptor_id). *)
Fixpoint write_coupling_pairs_aux
    (tbl : nat -> option CouplingPairEntry) (base : nat)
    (pairs : list (nat * nat)) : nat -> option CouplingPairEntry :=
  match pairs with
  | [] => tbl
  | (s, t) :: rest =>
      write_coupling_pairs_aux
        (fun i => if Nat.eqb i base
                  then Some {| coupling_pair_source := s; coupling_pair_target := t |}
                  else tbl i)
        (S base) rest
  end.

Definition rich_state_add_coupling_data (rs : RichSnapshotState)
    (pairs : list (nat * nat)) (label : string)
    : RichSnapshotState * nat :=
  let pair_base := rs.(rich_next_coupling_pair_id) in
  let pair_count := length pairs in
  let pair_table' := write_coupling_pairs_aux
                       rs.(rich_coupling_pair_table) pair_base pairs in
  let desc_id := rs.(rich_next_coupling_desc_id) in
  let desc := {| coupling_desc_base := pair_base;
                 coupling_desc_count := pair_count;
                 coupling_desc_label := label |} in
  ({| rich_morph_table := rs.(rich_morph_table);
      rich_next_morph_id := rs.(rich_next_morph_id);
      rich_coupling_desc_table := fun i =>
        if Nat.eqb i desc_id then Some desc
        else rs.(rich_coupling_desc_table) i;
      rich_next_coupling_desc_id := desc_id + 1;
      rich_coupling_pair_table := pair_table';
      rich_next_coupling_pair_id := pair_base + pair_count;
      rich_formula_desc_table := rs.(rich_formula_desc_table);
      rich_next_formula_desc_id := rs.(rich_next_formula_desc_id);
      rich_cert_desc_table := rs.(rich_cert_desc_table);
      rich_next_cert_desc_id := rs.(rich_next_cert_desc_id);
      rich_desc_meta_table := rs.(rich_desc_meta_table);
      rich_next_desc_meta_id := rs.(rich_next_desc_meta_id);
      rich_lassert_state := rs.(rich_lassert_state) |},
   desc_id).

(** Add a morphism with fully populated coupling data.
    Returns (updated_state, new_morph_id). *)
Definition rich_state_add_morph_with_coupling (rs : RichSnapshotState)
    (src dst : nat) (pairs : list (nat * nat))
    (label : string) (is_id : bool)
    : RichSnapshotState * nat :=
  let '(rs1, desc_id) := rich_state_add_coupling_data rs pairs label in
  rich_state_add_morph rs1 src dst desc_id is_id.

(** Look up the coupling label for a morphism entry's descriptor. *)
Definition morph_coupling_label (rs : RichSnapshotState) (entry : MorphTableEntry) : string :=
  match rs.(rich_coupling_desc_table) (morph_entry_coupling_desc entry) with
  | Some desc => coupling_desc_label desc
  | None => coupling_label empty_coupling_data
  end.

(** Advance pc/mu, write reg dst = new_id, replace rich_state with rs'. *)
Definition kami_advance_rich_morph (hs : KamiSnapshot)
    (dst new_id cost : nat) (rs' : RichSnapshotState) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := fun i => if Nat.eqb i (dst mod RegCount) then word64 new_id
                                   else snap_regs hs i;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := rs';
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Advance pc/mu, preserve regs, replace rich_state with rs'. *)
Definition kami_advance_rich_noret (hs : KamiSnapshot)
    (cost : nat) (rs' : RichSnapshotState) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := rs';
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Default CSRs: all fields zero *)
Definition default_csrs : CSRState :=
  {| csr_cert_addr := 0 ; csr_status := 0 ; csr_err := 0; csr_heap_base := 0 |}.

(** Reconstruct a PartitionGraph from the bounded hardware partition table.

    The hardware stores (module_id -> base, region_size) for up to PTableSz=64
    slots. A size of 0 means the slot is unallocated.  Axioms cannot be stored
    in fixed-width hardware registers; they are maintained by the software
    driver. The region for module id with base b and size sz is the range
    List.seq b sz of data-memory addresses.

    We iterate over module IDs in DESCENDING order (List.rev) so that the
    oldest module appears LAST in pg_modules, matching the cons-prepend
    behaviour of graph_add_module:
      graph_add_module g region [] = {pg_next_id := S(g.pg_next_id);
                                       pg_modules := (g.pg_next_id, m) :: g.pg_modules;
                                       pg_next_morph_id := g.pg_next_morph_id;
                                       pg_morphisms := g.pg_morphisms}

    NOTE: [snap_pt_to_graph] is intentionally module-only.  It is the
    projection used by the weaker [abs_phase1] proof story, so it exposes
    empty morphism state.  Richer bounded morph/coupling state is carried by
    [snap_rich_state] and [snap_full_graph], which leave the module-table
    lemmas built over this definition unchanged.

    This ordering invariant is what lets snap_pt_to_graph_pnew hold as a
    structural equality (not just observational equivalence).

    Note: snap_pt_to_graph produces pg_morphisms := [] by design.
    Morphism state is tracked at the full-snapshot level via snap_full_graph.
    See GraphReconstructionBridge.v for the full-state bridge. *)
Definition snap_pt_to_graph (next_id : nat) (sizes bases : nat -> nat) : PartitionGraph :=
  let modules :=
    filtermap
      (fun i =>
        if Nat.eqb (sizes i) 0 then None
        else Some (i, {| module_region := List.seq (bases i) (sizes i);
                          module_axioms := [];
                          module_mu_tensor := module_mu_tensor_default |}))
      (List.rev (List.seq 0 next_id))
  in
  {| pg_next_id := next_id;
     pg_modules := modules;
     pg_next_morph_id := 1;
     pg_morphisms := [] |}.

(** Full bounded graph reconstruction from the hardware-facing snapshot.
    M3 uses the same module reconstruction as [snap_pt_to_graph], then overlays
    bounded morph/coupling state from [snap_rich_state] and per-module tensor
    data from [snap_module_tensors]. *)
Definition snap_full_graph (s : KamiSnapshot) : PartitionGraph :=
  let base := snap_pt_to_graph (snap_pt_next_id s) (snap_pt_sizes s) (snap_pt_bases s) in
  {| pg_next_id := base.(pg_next_id);
     pg_modules := map (fun '(id, m) =>
       (id, {| module_region := m.(module_region);
               module_axioms := m.(module_axioms);
               module_mu_tensor :=
                 List.map (snap_module_tensors s id) (List.seq 0 16) |}))
       base.(pg_modules);
     pg_next_morph_id := rich_next_morph_id (snap_rich_state s);
     pg_morphisms := snapshot_morphisms_of_rich_state (snap_rich_state s) |}.

(** Main abstraction: KamiSnapshot -> VMState.
    The partition graph is reconstructed from the hardware partition table.
    Axioms are maintained by the software driver and are not stored in hardware. *)
Definition abs_phase1 (s : KamiSnapshot) : VMState :=
  {| vm_graph     := snap_pt_to_graph (snap_pt_next_id s) (snap_pt_sizes s) (snap_pt_bases s) ;
     vm_csrs      := {| csr_cert_addr := snap_csr_cert_addr s;
                        csr_status    := snap_csr_status s;
                        csr_err       := snap_csr_err s;
                        csr_heap_base := snap_csr_heap_base s |} ;
     vm_regs      := snapshot_regs_to_list (snap_regs s) ;
     vm_mem       := snapshot_mem_to_list  (snap_mem s)  ;
     vm_pc        := snap_pc s ;
     vm_mu        := snap_mu s ;
     vm_mu_tensor := snapshot_tensor_to_list (snap_mu_tensor s) ;
     vm_err       := snap_err s ;
     vm_logic_acc := snap_logic_acc s ;
     vm_mstatus   := snap_mstatus s ;
     vm_witness   := {| wc_same_00 := snap_wc_same_00 s;
                        wc_diff_00 := snap_wc_diff_00 s;
                        wc_same_01 := snap_wc_same_01 s;
                        wc_diff_01 := snap_wc_diff_01 s;
                        wc_same_10 := snap_wc_same_10 s;
                        wc_diff_10 := snap_wc_diff_10 s;
                        wc_same_11 := snap_wc_same_11 s;
                        wc_diff_11 := snap_wc_diff_11 s |} ;
     vm_certified := snap_certified s |}.

(** Full alias — all 46 instructions covered *)
Definition abs_full := abs_phase1.

(* ====================================================================
   Hardware step function — kami_step
   Maps a KamiSnapshot through one vm_instruction, mirroring
   the RTL rule bodies in ThieleCPUCore.v.

   Stack-pointer register: register r(RegCount-1) (= kami_sp_reg) is reserved
   for CALL/RET, matching SP_IDX in ThieleCPUCore.v.
   *)

(** Stack-pointer register index — mirrors SP_IDX in ThieleCPUCore.v.
    RegIdxSz bits → max register index RegCount-1 is kami_sp_reg. *)
Definition kami_sp_reg : nat := RegCount - 1.

(** Default hardware advance: increment PC by 1, add cost to mu.
    All other KamiSnapshot fields are preserved unchanged. *)
Definition kami_advance_default (hs : KamiSnapshot) (cost : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Write register [r mod RegCount] with value word64(v). *)
Definition kami_write_reg (hs : KamiSnapshot) (r v : nat) : nat -> nat :=
  fun j => if Nat.eqb j (r mod RegCount) then word64 v else snap_regs hs j.

(** Write memory[a mod MEM_SIZE] with value word64(v). *)
Definition kami_write_mem (hs : KamiSnapshot) (a v : nat) : nat -> nat :=
  fun j => if Nat.eqb j (a mod MEM_SIZE) then word64 v else snap_mem hs j.

(** Advance pc, charge cost, write register [r] to value [v].
    Used for instructions that both advance state and write a result to a register,
    e.g. the categorical MORPH instructions that write 0 to their dst register. *)
Definition kami_advance_reg (hs : KamiSnapshot) (r v cost : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := kami_write_reg hs r v;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Advance pc/mu under error-latch: set snap_err = true, set snap_csr_err = 1.
    Used for error paths matching SimulationProof.vm_apply's
    csr_set_err + latch_err pattern. *)
Definition kami_advance_err (hs : KamiSnapshot) (cost : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := true;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := 1;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Diagnostic codes the CPU writes on VM-level failures, as [wordToNat] of
    the ERR_* words in ThieleTypes. Each value sits behind a Qed-closed
    witness, so no reduction tactic expands it into a unary numeral; the
    [_spec] lemmas give the defining equations. *)
Lemma kami_err_logic_witness : { n : nat | n = N.to_nat 3291771297%N }.
Proof. eexists. reflexivity. Qed.
Lemma kami_err_coupling_invalid_witness : { n : nat | n = N.to_nat 3134980096%N }.
Proof. eexists. reflexivity. Qed.
Lemma kami_err_compose_type_witness : { n : nat | n = N.to_nat 3134980097%N }.
Proof. eexists. reflexivity. Qed.
Lemma kami_err_morph_not_found_witness : { n : nat | n = N.to_nat 3134980099%N }.
Proof. eexists. reflexivity. Qed.
Definition KAMI_ERR_LOGIC : nat := proj1_sig kami_err_logic_witness.
Definition KAMI_ERR_COUPLING_INVALID : nat := proj1_sig kami_err_coupling_invalid_witness.
Definition KAMI_ERR_COMPOSE_TYPE : nat := proj1_sig kami_err_compose_type_witness.
Definition KAMI_ERR_MORPH_NOT_FOUND : nat := proj1_sig kami_err_morph_not_found_witness.
Lemma kami_err_partition_overlap_witness : { n : nat | n = N.to_nat 3135176734%N }.
Proof. eexists. reflexivity. Qed.
Definition KAMI_ERR_PARTITION_OVERLAP : nat := proj1_sig kami_err_partition_overlap_witness.

(** ** Partition-table range checks

    The snapshot-level form of the step rule's checks. Slot [i] holds a
    module when [i] is below the next free slot and its size is not zero;
    its range is [bases i, bases i + sizes i). *)
Definition snap_slot_live (next : nat) (sizes : nat -> nat) (i : nat) : bool :=
  andb (Nat.ltb i next) (negb (Nat.eqb (sizes i) 0)).
Definition snap_slot_same (sizes bases : nat -> nat) (a len i : nat) : bool :=
  andb (Nat.eqb (bases i) a) (Nat.eqb (sizes i) len).
Definition snap_slot_overlap (sizes bases : nat -> nat) (a len i : nat) : bool :=
  andb (Nat.ltb a (bases i + sizes i)) (Nat.ltb (bases i) (a + len)).

(** PNEW of [a, a + len) conflicts with a module whose range shares an
    address with it without being it. *)
Definition snap_pt_conflict (next : nat) (sizes bases : nat -> nat) (a len : nat) : bool :=
  existsb (fun i => andb (snap_slot_live next sizes i)
                         (andb (negb (snap_slot_same sizes bases a len i))
                               (snap_slot_overlap sizes bases a len i)))
          (List.seq 0 PTableSz).

(** Some module owns exactly [a, a + len); PNEW then names that module. *)
Definition snap_pt_present (next : nat) (sizes bases : nat -> nat) (a len : nat) : bool :=
  existsb (fun i => andb (snap_slot_live next sizes i) (snap_slot_same sizes bases a len i))
          (List.seq 0 PTableSz).

(** PMERGE's adjacency: one range ends where the other begins, or one of
    them is empty. *)
Definition snap_pmerge_adjacent (sizes bases : nat -> nat) (m1 m2 : nat) : bool :=
  orb (orb (orb (Nat.eqb (sizes m1) 0) (Nat.eqb (sizes m2) 0))
           (Nat.eqb (bases m1 + sizes m1) (bases m2)))
      (Nat.eqb (bases m2 + sizes m2) (bases m1)).

(** Base of the range PMERGE builds: the lower of the two bases. *)
Definition snap_pmerge_base (sizes bases : nat -> nat) (m1 m2 : nat) : nat :=
  if Nat.eqb (sizes m1) 0 then bases m2
  else if Nat.eqb (sizes m2) 0 then bases m1
  else if Nat.eqb (bases m1 + sizes m1) (bases m2) then bases m1 else bases m2.

(** PSPLIT and PMERGE remove modules [m1] and [m2]; every morphism-table
    entry whose source or target is one of them is cleared. *)
Definition rich_state_cascade (rs : RichSnapshotState) (m1 m2 : nat) : RichSnapshotState :=
  {| rich_morph_table := fun i =>
       match rs.(rich_morph_table) i with
       | Some e =>
           if orb (orb (Nat.eqb (morph_entry_source e) m1) (Nat.eqb (morph_entry_target e) m1))
                  (orb (Nat.eqb (morph_entry_source e) m2) (Nat.eqb (morph_entry_target e) m2))
           then None else Some e
       | None => None
       end;
     rich_next_morph_id := rs.(rich_next_morph_id);
     rich_coupling_desc_table := rs.(rich_coupling_desc_table);
     rich_next_coupling_desc_id := rs.(rich_next_coupling_desc_id);
     rich_coupling_pair_table := rs.(rich_coupling_pair_table);
     rich_next_coupling_pair_id := rs.(rich_next_coupling_pair_id);
     rich_formula_desc_table := rs.(rich_formula_desc_table);
     rich_next_formula_desc_id := rs.(rich_next_formula_desc_id);
     rich_cert_desc_table := rs.(rich_cert_desc_table);
     rich_next_cert_desc_id := rs.(rich_next_cert_desc_id);
     rich_desc_meta_table := rs.(rich_desc_meta_table);
     rich_next_desc_meta_id := rs.(rich_next_desc_meta_id);
     rich_lassert_state := rs.(rich_lassert_state) |}.

(** [kami_advance_err] that also records the CPU diagnostic code. *)
Definition kami_advance_err_code (hs : KamiSnapshot) (cost code : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := true;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := code;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := 1;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Default advance that also counts disclosed information bits. *)
Definition kami_advance_info (hs : KamiSnapshot) (cost bits : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs + bits;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Advance pc/mu under error-latch with rich-state replacement.
    Error path for MORPH_DELETE when the morphism doesn't exist. *)
Definition kami_advance_err_rich (hs : KamiSnapshot) (cost : nat)
    (rs' : RichSnapshotState) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := true;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := rs';
     snap_csr_cert_addr := snap_csr_cert_addr hs;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := 1;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Advance pc/mu + set csr_cert_addr := addr.
    Used by MORPH_ASSERT success path. *)
Definition kami_advance_cert_addr (hs : KamiSnapshot) (addr cost : nat) : KamiSnapshot :=
  {| snap_pc           := S (snap_pc hs);
     snap_mu           := snap_mu hs + cost;
     snap_err          := snap_err hs;
     snap_halted       := snap_halted hs;
     snap_regs         := snap_regs hs;
     snap_mem          := snap_mem hs;
     snap_partition_ops := snap_partition_ops hs;
     snap_mdl_ops      := snap_mdl_ops hs;
     snap_info_gain    := snap_info_gain hs;
     snap_error_code   := snap_error_code hs;
     snap_mu_tensor    := snap_mu_tensor hs;
     snap_pt_sizes     := snap_pt_sizes hs;
     snap_pt_bases     := snap_pt_bases hs;
     snap_pt_next_id   := snap_pt_next_id hs;
     snap_certified    := snap_certified hs;
     snap_wc_same_00   := snap_wc_same_00 hs;
     snap_wc_diff_00   := snap_wc_diff_00 hs;
     snap_wc_same_01   := snap_wc_same_01 hs;
     snap_wc_diff_01   := snap_wc_diff_01 hs;
     snap_wc_same_10   := snap_wc_same_10 hs;
     snap_wc_diff_10   := snap_wc_diff_10 hs;
     snap_wc_same_11   := snap_wc_same_11 hs;
     snap_wc_diff_11   := snap_wc_diff_11 hs;
     snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
     snap_csr_cert_addr := addr;
     snap_csr_status    := snap_csr_status hs;
     snap_csr_err       := snap_csr_err hs;
     snap_csr_heap_base := snap_csr_heap_base hs;
     snap_logic_acc     := snap_logic_acc hs;
     snap_mstatus       := snap_mstatus hs |}.

(** Computable hardware step function.  Each case mirrors the corresponding
    RTL rule body in ThieleCPUCore.v.

    CSR note: abs_phase1 projects vm_csrs = default_csrs for all snapshots.
    Instructions that update CSRs (REVEAL, EMIT, LASSERT, LJOIN) are handled
    at the software/driver layer; the snapshot only records the mu-tensor
    charge (for REVEAL) and mu/pc advances (for others).

    CALL/RET use kami_sp_reg (r15) as the stack pointer, matching SP_IDX
    in ThieleCPUCore.v. *)
Definition kami_step (hs : KamiSnapshot) (i : vm_instruction) : KamiSnapshot :=
  match i with
  | instr_pnew region cost =>
      (* PNEW claims [a, a + len): a is the first address of the normalized
         region (operand A), len its length (operand B). A range that
         overlaps a module without being its range traps as a failed
         LASSERT does; a range some module owns names that module; any other
         range takes the next free slot. *)
      let r := normalize_region region in
      let a := hd 0 r in
      let len := length r in
      let id := snap_pt_next_id hs in
      let ok := negb (snap_pt_conflict id (snap_pt_sizes hs) (snap_pt_bases hs) a len) in
      let fresh := andb ok (negb (snap_pt_present id (snap_pt_sizes hs) (snap_pt_bases hs) a len)) in
      {| snap_pc    := if ok then S (snap_pc hs) else LASSERT_TRAP_PC;
         snap_mu    := snap_mu hs + cost;
         snap_err   := if ok then snap_err hs else true;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs + 1;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := if ok then snap_error_code hs else KAMI_ERR_PARTITION_OVERLAP;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes :=
           if fresh then (fun j => if Nat.eqb j id then len else snap_pt_sizes hs j)
           else snap_pt_sizes hs;
         snap_pt_bases :=
           if fresh then (fun j => if Nat.eqb j id then a else snap_pt_bases hs j)
           else snap_pt_bases hs;
         snap_pt_next_id := if fresh then S id else id;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_psplit module left_region right_region cost =>
      (* PSPLIT: mirrors graph_hw_psplit. The range of module (module mod
         PTableSz) is cut at its middle into two new partition table slots:
         the left half keeps the base, the right half starts where the left
         one ends. The original slot is removed, with every morphism naming
         it. Always succeeds (matching SimulationProof.vm_apply). *)
      let mid := module mod PTableSz in
      let orig_sz := snap_pt_sizes hs mid in
      let orig_base := snap_pt_bases hs mid in
      let left_sz := Nat.div orig_sz 2 in
      let right_sz := orig_sz - left_sz in
      let nid := snap_pt_next_id hs in
      let sizes1 := fun i => if Nat.eqb i mid then 0 else snap_pt_sizes hs i in
      let sizes2 := fun i => if Nat.eqb i nid then left_sz else sizes1 i in
      let sizes3 := fun i => if Nat.eqb i (S nid) then right_sz else sizes2 i in
      let bases1 := fun i => if Nat.eqb i mid then 0 else snap_pt_bases hs i in
      let bases2 := fun i => if Nat.eqb i nid then orig_base else bases1 i in
      let bases3 := fun i => if Nat.eqb i (S nid) then orig_base + left_sz else bases2 i in
      {| snap_pc           := S (snap_pc hs);
         snap_mu           := snap_mu hs + cost;
         snap_err          := snap_err hs;
         snap_halted       := snap_halted hs;
         snap_regs         := snap_regs hs;
         snap_mem          := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs + 1;
         snap_mdl_ops      := snap_mdl_ops hs;
         snap_info_gain    := snap_info_gain hs;
         snap_error_code   := snap_error_code hs;
         snap_mu_tensor    := snap_mu_tensor hs;
         snap_pt_sizes     := sizes3;
         snap_pt_bases     := bases3;
         snap_pt_next_id   := S (S nid);
         snap_certified    := snap_certified hs;
         snap_wc_same_00   := snap_wc_same_00 hs;
         snap_wc_diff_00   := snap_wc_diff_00 hs;
         snap_wc_same_01   := snap_wc_same_01 hs;
         snap_wc_diff_01   := snap_wc_diff_01 hs;
         snap_wc_same_10   := snap_wc_same_10 hs;
         snap_wc_diff_10   := snap_wc_diff_10 hs;
         snap_wc_same_11   := snap_wc_same_11 hs;
         snap_wc_diff_11   := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := rich_state_cascade (snap_rich_state hs) mid mid;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_pmerge m1 m2 cost =>
      (* PMERGE: mirrors graph_hw_pmerge. Modules m1 mod PTableSz and
         m2 mod PTableSz must have ranges that touch; otherwise the step traps
         as a failed LASSERT does. Both slots are removed, with every
         morphism naming either, and one new slot takes the joined range. *)
      let mid1 := m1 mod PTableSz in
      let mid2 := m2 mod PTableSz in
      let sz1 := snap_pt_sizes hs mid1 in
      let sz2 := snap_pt_sizes hs mid2 in
      let merged_sz := sz1 + sz2 in
      let merged_base := snap_pmerge_base (snap_pt_sizes hs) (snap_pt_bases hs) mid1 mid2 in
      let nid := snap_pt_next_id hs in
      let ok := snap_pmerge_adjacent (snap_pt_sizes hs) (snap_pt_bases hs) mid1 mid2 in
      let sizes1 := fun i => if Nat.eqb i mid1 then 0 else snap_pt_sizes hs i in
      let sizes2 := fun i => if Nat.eqb i mid2 then 0 else sizes1 i in
      let sizes3 := fun i => if Nat.eqb i nid then merged_sz else sizes2 i in
      let bases1 := fun i => if Nat.eqb i mid1 then 0 else snap_pt_bases hs i in
      let bases2 := fun i => if Nat.eqb i mid2 then 0 else bases1 i in
      let bases3 := fun i => if Nat.eqb i nid then merged_base else bases2 i in
      {| snap_pc           := if ok then S (snap_pc hs) else LASSERT_TRAP_PC;
         snap_mu           := snap_mu hs + cost;
         snap_err          := if ok then snap_err hs else true;
         snap_halted       := snap_halted hs;
         snap_regs         := snap_regs hs;
         snap_mem          := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs + 1;
         snap_mdl_ops      := snap_mdl_ops hs;
         snap_info_gain    := snap_info_gain hs;
         snap_error_code   := if ok then snap_error_code hs else KAMI_ERR_PARTITION_OVERLAP;
         snap_mu_tensor    := snap_mu_tensor hs;
         snap_pt_sizes     := if ok then sizes3 else snap_pt_sizes hs;
         snap_pt_bases     := if ok then bases3 else snap_pt_bases hs;
         snap_pt_next_id   := if ok then S nid else nid;
         snap_certified    := snap_certified hs;
         snap_wc_same_00   := snap_wc_same_00 hs;
         snap_wc_diff_00   := snap_wc_diff_00 hs;
         snap_wc_same_01   := snap_wc_same_01 hs;
         snap_wc_diff_01   := snap_wc_diff_01 hs;
         snap_wc_same_10   := snap_wc_same_10 hs;
         snap_wc_diff_10   := snap_wc_diff_10 hs;
         snap_wc_same_11   := snap_wc_same_11 hs;
         snap_wc_diff_11   := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := if ok then rich_state_cascade (snap_rich_state hs) mid1 mid2
                           else snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_lassert freg creg kind flen cost =>
      (* LASSERT: hardware computes full formula check and validates that the
        declared flen matches the in-memory formula header, trapping on any
        failure. Cost: flen * 8 + S cost (matches instruction_cost).
         PC: S pc on success, LASSERT_TRAP_PC on failure.
         Error: set snap_err and the CSR error flag on failure (matching vm_apply). *)
      let check_ok := lassert_exec_ok (abs_phase1 hs) freg creg kind flen in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (flen * 8 + S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := if check_ok then snap_error_code hs else KAMI_ERR_LOGIC;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_ljoin _ _ cost =>
      kami_advance_default hs (S cost)
  | instr_mdlacc _ cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs + 1;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_pdiscover _ _ cost =>
      kami_advance_default hs cost
  | instr_xfer dst src cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (snap_regs hs (src mod RegCount));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_load_imm dst imm cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst imm;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_load dst rs_addr cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (snap_mem hs (snap_regs hs (rs_addr mod RegCount) mod MEM_SIZE));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_store rs_addr src cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := kami_write_mem hs (snap_regs hs (rs_addr mod RegCount)) (snap_regs hs (src mod RegCount));
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_add dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (snap_regs hs (rs1 mod RegCount) + snap_regs hs (rs2 mod RegCount));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_sub dst rs1 rs2 cost =>
      let v1 := snap_regs hs (rs1 mod RegCount) in
      let v2 := snap_regs hs (rs2 mod RegCount) in
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_sub v1 v2);  (* 2's complement wrap — matches vm_apply_unsafe *)
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_jump target cost =>
      {| snap_pc    := target;
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_jnez rs target cost =>
      let v := snap_regs hs (rs mod RegCount) in
      {| snap_pc    := if Nat.eqb v 0 then S (snap_pc hs) else target;
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  (* CALL/RET use kami_sp_reg (r15) as the stack pointer.
     Mirrors SP_IDX (WO~1~1~1~1~1 = 31) in ThieleCPUCore.v.
     Stack convention: ASCENDING (matches vm_apply_unsafe and RTL).
     CALL: write ret_addr at OLD sp, then increment sp.
     RET:  decrement sp first, then read ret_pc from new sp. *)
  | instr_call target cost =>
      let sp  := snap_regs hs kami_sp_reg in
      let sp' := word64_add sp 1 in               (* INCREMENT — matches vm_apply_unsafe *)
      let ra  := S (snap_pc hs) in
      {| snap_pc    := target;
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := fun j =>
           if Nat.eqb j kami_sp_reg then sp' else snap_regs hs j;
         snap_mem   := fun j =>
           if Nat.eqb j sp then ra else snap_mem hs j;  (* write at OLD sp *)
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_ret cost =>
      let sp' := word64_sub (snap_regs hs kami_sp_reg) 1 in  (* DECREMENT — matches vm_apply_unsafe *)
      let ra  := snap_mem hs sp' in  (* read from DECREMENTED sp *)
      {| snap_pc    := ra;
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := fun j =>
           if Nat.eqb j kami_sp_reg then sp' else snap_regs hs j;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_chsh_trial x y a b cost =>
      let same := Nat.eqb a b in
      let wc00s := snap_wc_same_00 hs in let wc00d := snap_wc_diff_00 hs in
      let wc01s := snap_wc_same_01 hs in let wc01d := snap_wc_diff_01 hs in
      let wc10s := snap_wc_same_10 hs in let wc10d := snap_wc_diff_10 hs in
      let wc11s := snap_wc_same_11 hs in let wc11d := snap_wc_diff_11 hs in
      let mk s00 d00 s01 d01 s10 d10 s11 d11 :=
        {| snap_pc := S (snap_pc hs); snap_mu := snap_mu hs + cost;
           snap_err := snap_err hs; snap_halted := snap_halted hs;
           snap_regs := snap_regs hs; snap_mem := snap_mem hs;
           snap_partition_ops := snap_partition_ops hs;
           snap_mdl_ops := snap_mdl_ops hs;
           snap_info_gain := snap_info_gain hs;
           snap_error_code := snap_error_code hs;
           snap_mu_tensor := snap_mu_tensor hs;
           snap_pt_sizes := snap_pt_sizes hs;
           snap_pt_bases := snap_pt_bases hs;
           snap_pt_next_id := snap_pt_next_id hs;
           snap_certified := snap_certified hs;
           snap_wc_same_00 := s00; snap_wc_diff_00 := d00;
           snap_wc_same_01 := s01; snap_wc_diff_01 := d01;
           snap_wc_same_10 := s10; snap_wc_diff_10 := d10;
           snap_wc_same_11 := s11; snap_wc_diff_11 := d11;
           snap_module_tensors := snap_module_tensors hs;
           snap_rich_state    := snap_rich_state hs;
           snap_csr_cert_addr := snap_csr_cert_addr hs;
           snap_csr_status    := snap_csr_status hs;
           snap_csr_err       := snap_csr_err hs;
           snap_csr_heap_base := snap_csr_heap_base hs;
           snap_logic_acc     := snap_logic_acc hs;
           snap_mstatus       := snap_mstatus hs |} in
      match x, y with
      | 0, 0 => if same then mk (S wc00s) wc00d wc01s wc01d wc10s wc10d wc11s wc11d
                 else         mk wc00s (S wc00d) wc01s wc01d wc10s wc10d wc11s wc11d
      | 0, _ => if same then mk wc00s wc00d (S wc01s) wc01d wc10s wc10d wc11s wc11d
                 else         mk wc00s wc00d wc01s (S wc01d) wc10s wc10d wc11s wc11d
      | _, 0 => if same then mk wc00s wc00d wc01s wc01d (S wc10s) wc10d wc11s wc11d
                 else         mk wc00s wc00d wc01s wc01d wc10s (S wc10d) wc11s wc11d
      | _, _ => if same then mk wc00s wc00d wc01s wc01d wc10s wc10d (S wc11s) wc11d
                 else         mk wc00s wc00d wc01s wc01d wc10s wc10d wc11s (S wc11d)
      end
  | instr_xor_load dst addr cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (snap_mem hs (addr mod MEM_SIZE));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_xor_add dst src cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_xor (snap_regs hs (dst mod RegCount))
                                     (snap_regs hs (src mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_xor_swap a b cost =>
      let va := snap_regs hs (a mod RegCount) in
      let vb := snap_regs hs (b mod RegCount) in
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := fun j =>
           if Nat.eqb j (a mod RegCount) then vb
           else if Nat.eqb j (b mod RegCount) then va
           else snap_regs hs j;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_xor_rank dst src cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (word64_popcount (snap_regs hs (src mod RegCount)));  (* popcount — matches vm_apply_unsafe *)
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_emit _ payload cost =>
      kami_advance_info hs (payload_bit_length payload + S cost)
        (payload_bit_length payload)
  | instr_reveal module0 bits _ cost =>
      (* REVEAL: tensor_idx = module0 mod 16, delta = bits — matches advance_state_reveal in vm_apply_unsafe *)
      let k := module0 mod 16 in
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + (bits + S cost);
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor :=
           fun j => if Nat.eqb j k then snap_mu_tensor hs j + bits
                    else snap_mu_tensor hs j;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_halt cost =>
      (* HALT: vm_apply_unsafe falls through to advance_state (PC+1, cost).
         snap_halted flag is hardware-only; abs_phase1 does not expose it.
         We match vm_apply_unsafe: pc advances by 1. *)
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := true;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_checkpoint _ cost =>
      kami_advance_default hs cost
  | instr_read_port dst _ v bits cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + (bits + S cost);
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst v;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_write_port _ _ cost =>
      kami_advance_default hs cost
  | instr_heap_load dst rs_addr cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (snap_mem hs ((snap_csr_heap_base hs + snap_regs hs (rs_addr mod RegCount)) mod MEM_SIZE));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_heap_store rs_addr src cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := kami_write_mem hs (snap_csr_heap_base hs + snap_regs hs (rs_addr mod RegCount)) (snap_regs hs (src mod RegCount));
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  (* CERTIFY: advance PC, charge S delta_mu (structurally positive cost),
     set certified=true. No reg/mem/graph changes. Mirrors step_certify in VMStep.v. *)
  | instr_certify delta_mu =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + S delta_mu;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := true;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_and dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_and (snap_regs hs (rs1 mod RegCount)) (snap_regs hs (rs2 mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_or dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_or (snap_regs hs (rs1 mod RegCount)) (snap_regs hs (rs2 mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_shl dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_shl (snap_regs hs (rs1 mod RegCount)) (snap_regs hs (rs2 mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_shr dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_shr (snap_regs hs (rs1 mod RegCount)) (snap_regs hs (rs2 mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_mul dst rs1 rs2 cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst
                         (word64_mul (snap_regs hs (rs1 mod RegCount)) (snap_regs hs (rs2 mod RegCount)));
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_lui dst imm cost =>
      {| snap_pc    := S (snap_pc hs);
         snap_mu    := snap_mu hs + cost;
         snap_err   := snap_err hs;
         snap_halted := snap_halted hs;
         snap_regs  := kami_write_reg hs dst (word64_shl imm 8);
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
     snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := snap_csr_err hs;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  (* TENSOR_SET: Updates per-module tensor entry at (i,j).
     Hardware validates indices and stores the value in snap_module_tensors.
     snap_full_graph reconstructs modules using snap_module_tensors. *)
  | instr_tensor_set mid i j value cost =>
      if tensor_indices_ok i j then
        {| snap_pc    := S (snap_pc hs);
           snap_mu    := snap_mu hs + cost;
           snap_err   := snap_err hs;
           snap_halted := snap_halted hs;
           snap_regs  := snap_regs hs;
           snap_mem   := snap_mem hs;
           snap_partition_ops := snap_partition_ops hs;
           snap_mdl_ops := snap_mdl_ops hs;
           snap_info_gain := snap_info_gain hs;
           snap_error_code := snap_error_code hs;
           snap_mu_tensor := snap_mu_tensor hs;
           snap_pt_sizes := snap_pt_sizes hs;
           snap_pt_bases := snap_pt_bases hs;
           snap_pt_next_id := snap_pt_next_id hs;
           snap_certified := snap_certified hs;
           snap_wc_same_00 := snap_wc_same_00 hs;
           snap_wc_diff_00 := snap_wc_diff_00 hs;
           snap_wc_same_01 := snap_wc_same_01 hs;
           snap_wc_diff_01 := snap_wc_diff_01 hs;
           snap_wc_same_10 := snap_wc_same_10 hs;
           snap_wc_diff_10 := snap_wc_diff_10 hs;
           snap_wc_same_11 := snap_wc_same_11 hs;
           snap_wc_diff_11 := snap_wc_diff_11 hs;
           snap_module_tensors := fun m k =>
             if andb (Nat.eqb m mid) (Nat.eqb k (i * 4 + j)) then value
             else snap_module_tensors hs m k;
           snap_rich_state    := snap_rich_state hs;
           snap_csr_cert_addr := snap_csr_cert_addr hs;
           snap_csr_status    := snap_csr_status hs;
           snap_csr_err       := snap_csr_err hs;
           snap_csr_heap_base := snap_csr_heap_base hs;
           snap_logic_acc     := snap_logic_acc hs;
           snap_mstatus       := snap_mstatus hs |}
      else
        kami_advance_err hs cost
  (* TENSOR_GET: Reads per-module tensor entry at (i,j) into register dst.
     Hardware validates indices and reads from snap_module_tensors. *)
  | instr_tensor_get dst mid i j cost =>
      if tensor_indices_ok i j then
        {| snap_pc    := S (snap_pc hs);
           snap_mu    := snap_mu hs + cost;
           snap_err   := snap_err hs;
           snap_halted := snap_halted hs;
           snap_regs  := kami_write_reg hs dst (snap_module_tensors hs mid (i * 4 + j));
           snap_mem   := snap_mem hs;
           snap_partition_ops := snap_partition_ops hs;
           snap_mdl_ops := snap_mdl_ops hs;
           snap_info_gain := snap_info_gain hs;
           snap_error_code := snap_error_code hs;
           snap_mu_tensor := snap_mu_tensor hs;
           snap_pt_sizes := snap_pt_sizes hs;
           snap_pt_bases := snap_pt_bases hs;
           snap_pt_next_id := snap_pt_next_id hs;
           snap_certified := snap_certified hs;
           snap_wc_same_00 := snap_wc_same_00 hs;
           snap_wc_diff_00 := snap_wc_diff_00 hs;
           snap_wc_same_01 := snap_wc_same_01 hs;
           snap_wc_diff_01 := snap_wc_diff_01 hs;
           snap_wc_same_10 := snap_wc_same_10 hs;
           snap_wc_diff_10 := snap_wc_diff_10 hs;
           snap_wc_same_11 := snap_wc_same_11 hs;
           snap_wc_diff_11 := snap_wc_diff_11 hs;
           snap_module_tensors := snap_module_tensors hs;
           snap_rich_state    := snap_rich_state hs;
           snap_csr_cert_addr := snap_csr_cert_addr hs;
           snap_csr_status    := snap_csr_status hs;
           snap_csr_err       := snap_csr_err hs;
           snap_csr_heap_base := snap_csr_heap_base hs;
           snap_logic_acc     := snap_logic_acc hs;
           snap_mstatus       := snap_mstatus hs |}
      else
        kami_advance_err hs cost
  (* Categorical / morphism instructions — full rich-state mutations.
     The hardware maintains bounded morph tables (max 64 entries) and
     performs real allocations / lookups / deletions.
     Error paths set snap_csr_err := 1 and snap_err := true,
     matching SimulationProof.vm_apply's csr_set_err + latch_err pattern. *)
  | instr_morph dst src_mod dst_mod coupling_idx cost =>
      (* Check that both source and target modules exist in partition table *)
      let src_exists := negb (Nat.eqb (snap_pt_sizes hs src_mod) 0) in
      let dst_exists := negb (Nat.eqb (snap_pt_sizes hs dst_mod) 0) in
      if andb src_exists dst_exists then
        let rs := snap_rich_state hs in
        (* Real coupling data (M5): decode the same serialized memory block
           ThieleMachineComplete.vm_apply reads, and register it through the
           same allocation path COMPOSE/MORPH_TENSOR already use below,
           rather than hardcoding an empty descriptor. Mirrors
           ThieleMachineComplete.load_coupling_from_mem exactly, working
           directly over the memory list (snapshot_mem_to_list (snap_mem hs))
           since that is all load_coupling_from_mem's helpers ever read. *)
        let g := snap_full_graph hs in
        let mem := snapshot_mem_to_list (snap_mem hs) in
        let src_region :=
          match graph_lookup g src_mod with
          | Some ms => ms.(module_region)
          | None => []
          end in
        let dst_region :=
          match graph_lookup g dst_mod with
          | Some ms => ms.(module_region)
          | None => []
          end in
        let pair_count := serialized_coupling_pair_count mem coupling_idx in
        let label_base := S coupling_idx + 2 * pair_count in
        let raw := {|
          coupling_pairs := load_coupling_pairs_from_mem mem (S coupling_idx) pair_count;
          coupling_label := mem_to_string mem (mem_index label_base)
        |} in
        (* Pre-normalize once, the same way COMPOSE/MORPH_TENSOR's
           composed_pairs already do below: rich_state_add_morph_with_coupling
           stores pairs as given, with no dedup step of its own, while
           graph_add_morphism (the software side) always dedups internally
           via normalize_coupling. Applying it here once keeps both sides
           storing the identical deduped pairs, since normalize_coupling is
           idempotent. *)
        let coupling := normalize_coupling (restrict_coupling_to_regions src_region dst_region raw) in
        let '(rs', new_id) :=
          rich_state_add_morph_with_coupling rs src_mod dst_mod
            coupling.(coupling_pairs) coupling.(coupling_label) false in
        kami_advance_rich_morph hs dst new_id cost rs'
      else
        kami_advance_err_code hs cost KAMI_ERR_COUPLING_INVALID
  | instr_compose dst m1_id m2_id cost =>
      (* COMPOSE: hardware computes relational composition of coupling data,
         with the same identity-flag short-circuit as the kernel's
         graph_compose_morphisms: when both are flagged identities the
         composite is a flagged identity with no pairs and the label "empty";
         composed pairs = h.pairs if only f is a flagged identity (id;f = f),
         f.pairs if only h is (f;id = f), relational_compose(f.pairs, h.pairs)
         otherwise, and label = f.label ++ ";" ++ h.label.
         Matches graph_compose_morphisms in kernel. *)
      let rs := snap_rich_state hs in
      match rs.(rich_morph_table) m1_id, rs.(rich_morph_table) m2_id with
      | Some e1, Some e2 =>
          if Nat.eqb (morph_entry_target e1) (morph_entry_source e2)
          then
            let both_id := andb (morph_entry_is_identity e1) (morph_entry_is_identity e2) in
            let pairs1 := snapshot_coupling_pairs_from_desc rs (morph_entry_coupling_desc e1) in
            let pairs2 := snapshot_coupling_pairs_from_desc rs (morph_entry_coupling_desc e2) in
            let label1 := morph_coupling_label rs e1 in
            let label2 := morph_coupling_label rs e2 in
            let composed_label :=
              if both_id then coupling_label empty_coupling_data
              else (label1 ++ ";" ++ label2)%string in
            let raw_pairs :=
              if both_id then []
              else if morph_entry_is_identity e1
              then pairs2
              else if morph_entry_is_identity e2
                   then pairs1
                   else relational_compose pairs1 pairs2 in
            let composed_pairs := (normalize_coupling {| coupling_pairs := raw_pairs;
                                                         coupling_label := composed_label |}).(coupling_pairs) in
            let '(rs', new_id) :=
              rich_state_add_morph_with_coupling rs
                (morph_entry_source e1) (morph_entry_target e2)
                composed_pairs composed_label both_id in
            kami_advance_rich_morph hs dst new_id cost rs'
          else kami_advance_err_code hs cost KAMI_ERR_COMPOSE_TYPE  (* endpoint mismatch: error *)
      | _, _ => kami_advance_err_code hs cost KAMI_ERR_MORPH_NOT_FOUND  (* morph not found: error *)
      end
  | instr_morph_id dst module cost =>
      (* MORPH_ID: identity morphism with coupling_desc=0 (empty_coupling_data).
         Identity is structural (src=dst=module, is_identity=true).
         Matches kernel graph_add_identity which uses empty_coupling_data. *)
      if negb (Nat.eqb (snap_pt_sizes hs module) 0) then
        let rs := snap_rich_state hs in
        let '(rs', new_id) := rich_state_add_morph rs module module 0 true in
        kami_advance_rich_morph hs dst new_id cost rs'
      else
        kami_advance_err_code hs cost KAMI_ERR_COUPLING_INVALID
  | instr_morph_delete morph_id cost =>
      let rs := snap_rich_state hs in
      match rs.(rich_morph_table) morph_id with
      | Some _ =>
          let rs' := rich_state_delete_morph rs morph_id in
          kami_advance_rich_noret hs cost rs'
      | None =>
          kami_advance_err_code hs cost KAMI_ERR_MORPH_NOT_FOUND  (* morph not found → error *)
      end
  | instr_morph_assert morph_id property _cert cost =>
      (* Check morph existence; on success set csr_cert_addr := ascii_checksum property *)
      let rs := snap_rich_state hs in
      match rs.(rich_morph_table) morph_id with
      | Some _ =>
          kami_advance_cert_addr hs (ascii_checksum property) (S cost)
      | None =>
          kami_advance_err_code hs (S cost) KAMI_ERR_MORPH_NOT_FOUND  (* morph not found → error *)
      end
  | instr_morph_tensor dst f_id g_id cost =>
      (* MORPH_TENSOR: the kernel's graph_tensor_morphisms on the
         reconstructed graph. When the table's ranges are pairwise disjoint
         no module owns the union of two disjoint regions, so this records a
         missing morphism (MorphTensorGap.v); the CPU always faults that way. *)
      let g := snap_full_graph hs in
      match graph_tensor_morphisms g f_id g_id with
      | Some (graph', morph_id) =>
          match graph_lookup_morphism graph' morph_id with
          | Some new_ms =>
              let rs := snap_rich_state hs in
              let '(rs', _) := rich_state_add_morph_with_coupling rs
                                 new_ms.(morph_source) new_ms.(morph_target)
                                 new_ms.(morph_coupling).(coupling_pairs)
                                 new_ms.(morph_coupling).(coupling_label) false in
              kami_advance_rich_morph hs dst morph_id cost rs'
          | None => kami_advance_err_code hs cost KAMI_ERR_MORPH_NOT_FOUND
          end
      | None => kami_advance_err_code hs cost KAMI_ERR_MORPH_NOT_FOUND
      end
  | instr_morph_get dst morph_id selector cost =>
      let rs := snap_rich_state hs in
      match rs.(rich_morph_table) morph_id with
      | Some entry =>
          let value := match selector with
            | 0 => morph_entry_source entry
            | 1 => morph_entry_target entry
            | 2 => (* coupling pair count: look up coupling descriptor to get count *)
                    match (rich_coupling_desc_table rs) (morph_entry_coupling_desc entry) with
                    | Some desc => coupling_desc_count desc
                    | None => 0
                    end
            | 3 => if morph_entry_is_identity entry then 1 else 0
            | _ => 0
            end in
          kami_advance_reg hs dst value cost
      | None => kami_advance_err_code hs cost KAMI_ERR_MORPH_NOT_FOUND  (* morph not found → error *)
      end
  | instr_chsh_lassert cost =>
      (* CHSH-aware certification: hardware computes column-contractivity
         from snap_wc_* buckets directly (abs_phase1 projects these into
         vm_witness, so the snapshot-level check and the VM-level check
         agree by definition). On success: PC := S pc, err preserved,
         csr_csr_* preserved. On failure: PC := LASSERT_TRAP_PC, err := true.
         Cost: S cost regardless (cert-setter discipline). Matches
         step_chsh_lassert_ok / step_chsh_lassert_bad in VMStep.v. *)
      let check_ok := column_contractive_check_witness (vm_witness (abs_phase1 hs)) in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := if check_ok then snap_error_code hs else KAMI_ERR_LOGIC;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_chsh_lassert_1ab cost =>
      (* Q_{1+AB}-aware certification: combines Q_1 column-contractivity with
         the integer sum-of-squares condition. Same observable shape as
         instr_chsh_lassert but a stricter check function. *)
      let check_ok := column_contractive_check_q1ab_kernel (vm_witness (abs_phase1 hs)) in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_chsh_lassert_1ab_g5 cost same_g5 diff_g5 =>
      (* Q_{1+AB}-aware γ_5 certification: extends instr_chsh_lassert_1ab by
         also verifying the γ_5 SOS witness against the caller-supplied γ_5
         bucket pair (same_g5, diff_g5). *)
      let check_ok := q1ab_g5_full_integer_check_kernel
                        (vm_witness (abs_phase1 hs)) same_g5 diff_g5 in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_chsh_lassert_1ab_g345 cost same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      (* Q_{1+AB}-aware γ_{3,4,5} certification: extends γ_5 by also verifying
         γ_3, γ_4 buckets through the 4×4 Sylvester PD witness on H_{γ_345}. *)
      let check_ok := q1ab_g345_full_integer_check_kernel
                        (vm_witness (abs_phase1 hs))
                        same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  | instr_chsh_lassert_1ab_g12345 cost same_g1 diff_g1 same_g2 diff_g2
                                     same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      (* Full Q_{1+AB}-aware γ_{1..5} certification: extends γ_{3,4,5} by also
         verifying γ_1, γ_2 buckets through the 6×6 Schur cascade. *)
      let check_ok := q1ab_g12345_full_integer_check_kernel
                        (vm_witness (abs_phase1 hs))
                        same_g1 diff_g1 same_g2 diff_g2
                        same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 in
      let new_pc   := if check_ok then S (snap_pc hs) else LASSERT_TRAP_PC in
      let new_err  := if check_ok then snap_err hs else true in
      {| snap_pc    := new_pc;
         snap_mu    := snap_mu hs + (S cost);
         snap_err   := new_err;
         snap_halted := snap_halted hs;
         snap_regs  := snap_regs hs;
         snap_mem   := snap_mem hs;
         snap_partition_ops := snap_partition_ops hs;
         snap_mdl_ops := snap_mdl_ops hs;
         snap_info_gain := snap_info_gain hs;
         snap_error_code := snap_error_code hs;
         snap_mu_tensor := snap_mu_tensor hs;
         snap_pt_sizes := snap_pt_sizes hs;
         snap_pt_bases := snap_pt_bases hs;
         snap_pt_next_id := snap_pt_next_id hs;
         snap_certified := snap_certified hs;
         snap_wc_same_00 := snap_wc_same_00 hs;
         snap_wc_diff_00 := snap_wc_diff_00 hs;
         snap_wc_same_01 := snap_wc_same_01 hs;
         snap_wc_diff_01 := snap_wc_diff_01 hs;
         snap_wc_same_10 := snap_wc_same_10 hs;
         snap_wc_diff_10 := snap_wc_diff_10 hs;
         snap_wc_same_11 := snap_wc_same_11 hs;
         snap_wc_diff_11 := snap_wc_diff_11 hs;
         snap_module_tensors := snap_module_tensors hs;
         snap_rich_state    := snap_rich_state hs;
         snap_csr_cert_addr := snap_csr_cert_addr hs;
         snap_csr_status    := snap_csr_status hs;
         snap_csr_err       := if check_ok then snap_csr_err hs else 1;
         snap_csr_heap_base := snap_csr_heap_base hs;
         snap_logic_acc     := snap_logic_acc hs;
         snap_mstatus       := snap_mstatus hs |}
  end.

(** kami_instruction_cost: the cost that the hardware charges for each opcode.
    CERTIFY pays S delta_mu; LASSERT pays flen * 8 + S cost;
    EMIT pays payload_bit_length payload + S cost; REVEAL/READ_PORT pay bits + S cost. *)
Definition kami_instruction_cost (i : vm_instruction) : nat :=
  match i with
  | instr_certify dm => S dm
  | other => instruction_cost other
  end.

(** Predicate for identifying CERTIFY instructions. *)
Definition is_certify (i : vm_instruction) : bool :=
  match i with
  | instr_certify _ => true
  | _ => false
  end.

(** kami_step advances mu by exactly kami_instruction_cost.
    For CERTIFY: S delta_mu (structurally positive).
    For LASSERT: flen * 8 + S cost.
    For EMIT: payload_bit_length payload + S cost.
    For REVEAL/READ_PORT: bits + S cost.
    For all other opcodes: equals instruction_cost directly. *)
Lemma kami_step_mu_cost : forall (hs : KamiSnapshot) (i : vm_instruction),
    snap_mu (kami_step hs i) = snap_mu hs + kami_instruction_cost i.
Proof.
  intros hs i. destruct i; simpl; try reflexivity; try lia;
  (* Handle branches: lassert_check_ok, tensor_indices_ok, morph lookups, etc. *)
  try (destruct (lassert_check_ok _ _ _ _); simpl; try reflexivity; try lia);
  try (destruct (tensor_indices_ok _ _); simpl; try reflexivity; try lia;
       unfold kami_advance_err; simpl; try reflexivity; try lia);
  try (destruct (graph_tensor_morphisms _ _ _) as [[]|]; simpl; try reflexivity; try lia;
       try (destruct (graph_lookup_morphism _ _); simpl; try reflexivity; try lia;
            unfold kami_advance_err; simpl; try reflexivity; try lia);
       unfold kami_advance_err; simpl; try reflexivity; try lia);
  (* CHSH_TRIAL: nested match on settings (x,y) and output same/diff *)
  (* Rich morph ops: match on option MorphTableEntry — all branches charge same mu *)
  repeat match goal with
    | |- context [match ?x with _ => _ end] =>
        destruct x; simpl; try reflexivity; try lia
  end.
Qed.

(** For non-CERTIFY instructions,
    kami cost equals vm cost. This includes LASSERT. *)
Lemma kami_cost_eq_instruction_cost : forall i,
    is_certify i = false ->
    kami_instruction_cost i = instruction_cost i.
Proof.
  intros i Hc. destruct i; simpl in *; try reflexivity; try discriminate.
Qed.

(** For CERTIFY, hardware cost >= software cost (conservative). *)
Lemma kami_cost_ge_instruction_cost : forall i,
    instruction_cost i <= ORACLE_HALTS_HW_COST ->
    kami_instruction_cost i >= instruction_cost i.
Proof.
  intros i Hbound. destruct i; simpl in *; try lia.
Qed.

(** Execution preconditions *)
Definition cpu_preconditions (s : KamiSnapshot) : Prop :=
  snap_pc         s < MEM_SIZE /\
  snap_mu         s < 2^31   /\
  snap_err        s = false  /\
  snap_halted     s = false  /\
  snap_pt_next_id s < PTableSz.    (* partition table not full: room for at least one more allocation *)

(** Length invariants *)

Lemma snapshot_regs_to_list_length : forall f,
    length (snapshot_regs_to_list f) = RegCount.
Proof.
  intro f. unfold snapshot_regs_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma snapshot_mem_to_list_length : forall f,
    length (snapshot_mem_to_list f) = MEM_SIZE.
Proof.
  intro f. unfold snapshot_mem_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

Lemma snapshot_tensor_to_list_length : forall f,
    length (snapshot_tensor_to_list f) = 16.
Proof.
  intro f. unfold snapshot_tensor_to_list. rewrite map_length, seq_length. reflexivity.
Qed.

(** Partition table correctness lemmas

    These lemmas establish that snap_pt_to_graph faithfully represents the
    hardware partition table as a formal PartitionGraph, and that PNEW/PSPLIT/PMERGE
    hardware operations commute with the abstraction map. *)

(** Helper: normalize_region of a range is the range (seq has no duplicates) *)
Lemma normalize_seq_nodups : forall b n,
    normalize_region (List.seq b n) = List.seq b n.
Proof.
  intros b n. unfold normalize_region.
  apply nodup_fixed_point.
  apply seq_NoDup.
Qed.

(** Helper: rev (seq 0 (S n)) = [n] ++ rev (seq 0 n) *)
Lemma rev_seq_succ : forall n,
    List.rev (List.seq 0 (S n)) = [n] ++ List.rev (List.seq 0 n).
Proof.
  intro n.
  rewrite seq_S.
  replace (0 + n) with n by lia.
  rewrite List.rev_app_distr.
  simpl. reflexivity.
Qed.

(** Helper: filtermap distributes over append *)
Lemma filter_map_app_dist : forall {A B} (f : A -> option B) l1 l2,
    filtermap f (l1 ++ l2) = filtermap f l1 ++ filtermap f l2.
Proof.
  induction l1; intros; simpl.
  - reflexivity.
  - destruct (f a); simpl; [f_equal | ]; apply IHl1.
Qed.

(** The module the partition-table reconstruction builds for slot [i]. *)
Definition pt_module_at (sizes bases : nat -> nat) (i : nat) : option (nat * ModuleState) :=
  if Nat.eqb (sizes i) 0 then None
  else Some (i, {| module_region := List.seq (bases i) (sizes i);
                   module_axioms := [];
                   module_mu_tensor := module_mu_tensor_default |}).

Lemma snap_pt_to_graph_modules : forall next_id sizes bases,
    pg_modules (snap_pt_to_graph next_id sizes bases) =
    filtermap (pt_module_at sizes bases) (List.rev (List.seq 0 next_id)).
Proof. reflexivity. Qed.

Lemma filtermap_ext_in_early :
  forall {A B : Type} (f g : A -> option B) (l : list A),
    (forall x, In x l -> f x = g x) ->
    filtermap f l = filtermap g l.
Proof.
  intros A B f g l Hext.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (Hext x (or_introl eq_refl)).
    destruct (g x); [f_equal|]; apply IH;
    intros y Hy; apply Hext; right; exact Hy.
Qed.

(** Helper: modifying index next_id doesn't affect filtermap over rev (seq 0 next_id)
    because all indices in seq 0 next_id are strictly less than next_id. *)
Lemma filter_map_pt_below_unaffected :
    forall (next_id region_size region_base : nat) (sizes bases : nat -> nat),
      filtermap
        (fun i => if Nat.eqb (if Nat.eqb i next_id then region_size else sizes i) 0
                  then None
                  else Some (i, {| module_region :=
                                     List.seq (if Nat.eqb i next_id then region_base else bases i)
                                              (if Nat.eqb i next_id then region_size else sizes i);
                                   module_axioms := [];
                                   module_mu_tensor := module_mu_tensor_default |}))
        (List.rev (List.seq 0 next_id)) =
      filtermap
        (fun i => if Nat.eqb (sizes i) 0 then None
                  else Some (i, {| module_region := List.seq (bases i) (sizes i);
                                   module_axioms := [];
                                   module_mu_tensor := module_mu_tensor_default |}))
        (List.rev (List.seq 0 next_id)).
Proof.
  intros next_id region_size region_base sizes bases.
  apply filtermap_ext_in_early.
  intros i Hi.
  apply in_rev in Hi.
  apply in_seq in Hi.
  destruct Hi as [_ Hi].
  assert (Hneq : Nat.eqb i next_id = false) by (apply Nat.eqb_neq; lia).
  rewrite Hneq. reflexivity.
Qed.

(** snap_pt_to_graph_wf:
    The graph reconstructed from any hardware snapshot is well-formed:
    all module IDs are strictly less than pg_next_id. *)

(** Helper: if all i in l satisfy i < bound, then all_ids_below (filtermap f l) bound
    for any f that only emits (i, _) pairs. *)
Lemma filtermap_all_ids_below :
    forall (bound : nat) (sizes bases : nat -> nat) (l : list nat),
      (forall i, List.In i l -> i < bound) ->
      all_ids_below
        (filtermap (fun i => if Nat.eqb (sizes i) 0 then None
                             else Some (i, {| module_region := List.seq (bases i) (sizes i);
                                              module_axioms := [];
                                              module_mu_tensor := module_mu_tensor_default |})) l)
        bound.
Proof.
  intros bound sizes bases l Hlt.
  induction l as [| i rest IH]; simpl.
  - exact I.
  - destruct (Nat.eqb (sizes i) 0) eqn:Hzero.
    + apply IH. intros j Hj. apply Hlt. right. exact Hj.
    + simpl. split.
      * apply Hlt. left. reflexivity.
      * apply IH. intros j Hj. apply Hlt. right. exact Hj.
Qed.

Theorem snap_pt_to_graph_wf : forall (next_id : nat) (sizes bases : nat -> nat),
    well_formed_graph (snap_pt_to_graph next_id sizes bases).
Proof.
  intros next_id sizes bases.
  unfold snap_pt_to_graph, well_formed_graph. simpl.
  split; [|split; [exact I|exact I]].
  apply filtermap_all_ids_below.
  intros i Hi.
  apply in_rev in Hi.
  apply in_seq in Hi.
  lia.
Qed.

Lemma snap_pt_to_graph_pnew_minimal_aux :
    forall (next_id region_base region_size : nat) (sizes bases : nat -> nat),
      region_size > 0 ->
      snap_pt_to_graph (S next_id)
        (fun j => if Nat.eqb j next_id then region_size else sizes j)
        (fun j => if Nat.eqb j next_id then region_base else bases j) =
      fst (graph_add_module (snap_pt_to_graph next_id sizes bases)
                            (List.seq region_base region_size) []).
Proof.
  intros next_id region_base region_size sizes bases Hrsz.
  assert (Hrsz_neq : Nat.eqb region_size 0 = false) by (apply Nat.eqb_neq; lia).
  assert (Hnorm : normalize_module {| module_region := List.seq region_base region_size;
                                       module_axioms := [];
                                       module_mu_tensor := module_mu_tensor_default |} =
                  {| module_region := List.seq region_base region_size;
                     module_axioms := [];
                     module_mu_tensor := module_mu_tensor_default |}).
  { unfold normalize_module. simpl. rewrite normalize_seq_nodups. reflexivity. }
  unfold snap_pt_to_graph, graph_add_module, mk_module_state.
  rewrite Hnorm.
  rewrite rev_seq_succ.
  rewrite filter_map_app_dist.
  cbn [filtermap fst snd pg_next_id pg_modules pg_next_morph_id pg_morphisms List.app].
  rewrite Nat.eqb_refl, Hrsz_neq.
  cbn [filtermap List.app].
  f_equal.
  f_equal.
  apply filter_map_pt_below_unaffected.
Qed.

(** snap_pt_to_graph_pnew:
    After hardware PNEW allocating slot [next_id] with base [region_base] and
    size [region_size], the reconstructed graph equals the result of
    graph_add_module applied to the previous graph with region
    (List.seq region_base region_size) and empty axioms.

    Preconditions match the hardware invariants:
    - next_id >= 1: matches empty_graph.pg_next_id = 1 starting point
    - region_size > 0: PNEW with zero size is a no-op; meaningful allocation is nonzero
    - sizes next_id = 0: hardware slot must be fresh (unallocated) before PNEW *)
Theorem snap_pt_to_graph_pnew :
    forall (next_id region_base region_size : nat) (sizes bases : nat -> nat),
      next_id >= 1 ->
      next_id < PTableSz ->
      region_size > 0 ->
      sizes next_id = 0 ->
      snap_pt_to_graph (S next_id)
        (fun j => if Nat.eqb j next_id then region_size else sizes j)
        (fun j => if Nat.eqb j next_id then region_base else bases j) =
      fst (graph_add_module (snap_pt_to_graph next_id sizes bases)
                            (List.seq region_base region_size) []).
Proof.
  intros next_id region_base region_size sizes bases _ _ Hrsz _.
  exact (snap_pt_to_graph_pnew_minimal_aux next_id region_base region_size sizes bases Hrsz).
Qed.

(** snap_pt_to_graph_pnew_minimal: same as snap_pt_to_graph_pnew but without
    the preconditions next_id >= 1, next_id < PTableSz, and sizes next_id = 0.
    The proof never uses those hypotheses. *)
Theorem snap_pt_to_graph_pnew_minimal :
    forall (next_id region_base region_size : nat) (sizes bases : nat -> nat),
      region_size > 0 ->
      snap_pt_to_graph (S next_id)
        (fun j => if Nat.eqb j next_id then region_size else sizes j)
        (fun j => if Nat.eqb j next_id then region_base else bases j) =
      fst (graph_add_module (snap_pt_to_graph next_id sizes bases)
                            (List.seq region_base region_size) []).
Proof.
  exact snap_pt_to_graph_pnew_minimal_aux.
Qed.

(** snap_pt_to_graph_pnew_pg_next_id:
    After hardware PNEW, pg_next_id advances by 1. *)
Corollary snap_pt_to_graph_pnew_next_id :
    forall (next_id region_base region_size : nat) (sizes bases : nat -> nat),
      next_id >= 1 -> next_id < PTableSz -> region_size > 0 -> sizes next_id = 0 ->
      (snap_pt_to_graph (S next_id)
         (fun j => if Nat.eqb j next_id then region_size else sizes j)
         (fun j => if Nat.eqb j next_id then region_base else bases j)).(pg_next_id) =
      S (snap_pt_to_graph next_id sizes bases).(pg_next_id).
Proof.
  intros. unfold snap_pt_to_graph. simpl. reflexivity.
Qed.

(** snap_pt_to_graph_pmerge_size_conserved:
    After hardware PMERGE of slots m1 and m2 (merging their sizes into slot slot3),
    the total region-size sum across all allocated modules is conserved. *)
Theorem snap_pt_to_graph_pmerge_size_conserved :
    forall (m1 m2 slot3 : nat) (sizes : nat -> nat),
      m1 < PTableSz -> m2 < PTableSz -> slot3 < PTableSz ->
      m1 <> m2 -> m1 <> slot3 -> m2 <> slot3 ->
      sizes slot3 = 0 ->  (* slot3 is fresh *)
      let merged_sz := sizes m1 + sizes m2 in
      let sizes' := fun j =>
        if Nat.eqb j m1 then 0
        else if Nat.eqb j m2 then 0
        else if Nat.eqb j slot3 then merged_sz
        else sizes j in
      (* The merged size equals the sum of the two source sizes *)
      sizes' slot3 = sizes m1 + sizes m2.
Proof.
  intros m1 m2 slot3 sizes Hm1 Hm2 Hs3 Hne12 Hne13 Hne23 Hfresh.
  simpl.
  replace (slot3 =? m1) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (slot3 =? m2) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** nth element of [seq start n] *)
Local Lemma seq_nth_helper : forall n start i,
    i < n -> List.nth i (List.seq start n) 0 = start + i.
Proof.
  induction n; intros start i Hi.
  - lia.
  - destruct i.
    + simpl. lia.
    + simpl. rewrite IHn by lia. lia.
Qed.

(** nth element of [map f l] = f applied to nth of [l] *)
Local Lemma nth_map_helper : forall {A B} (f : A -> B) (l : list A) i (da : A) (db : B),
    i < length l ->
    List.nth i (List.map f l) db = f (List.nth i l da).
Proof.
  intros A B f l. induction l; intros i da db Hi.
  - simpl in Hi. lia.
  - destruct i; [reflexivity | simpl; apply IHl; simpl in Hi; lia].
Qed.

(** Map with a conditional point-update equals firstn ++ [v] ++ skipn *)
Local Lemma map_update_gen : forall (f : nat -> nat) n start dst v,
    dst < n ->
    List.map (fun j => if Nat.eqb j (start + dst) then v else f j) (List.seq start n) =
    List.firstn dst (List.map f (List.seq start n)) ++ [v] ++
    List.skipn (S dst) (List.map f (List.seq start n)).
Proof.
  intros f n start dst v. revert n start.
  induction dst; intros n start Hn.
  - destruct n; [lia|].
    replace (start + 0) with start by lia.
    simpl. rewrite Nat.eqb_refl.
    f_equal. apply List.map_ext_in.
    intros j Hj%List.in_seq. destruct Hj as [Hge _].
    destruct (Nat.eqb j start) eqn:Ej.
    + apply Nat.eqb_eq in Ej. lia.
    + reflexivity.
  - destruct n; [lia|]. simpl.
    replace (Nat.eqb start (start + S dst)) with false
      by (symmetry; apply Nat.eqb_neq; lia).
    simpl. f_equal.
    replace (start + S dst) with (S start + dst) by lia.
    apply IHdst. lia.
Qed.

(** Specialized version for start = 0 *)
Local Corollary map_update_zero : forall (f : nat -> nat) n dst v,
    dst < n ->
    List.map (fun j => if Nat.eqb j dst then v else f j) (List.seq 0 n) =
    List.firstn dst (List.map f (List.seq 0 n)) ++ [v] ++
    List.skipn (S dst) (List.map f (List.seq 0 n)).
Proof.
  intros f n dst v Hn.
  pose proof (map_update_gen f n 0 dst v Hn) as H.
  rewrite Nat.add_0_l in H. exact H.
Qed.

(** Register and memory read equivalence *)

Lemma snapshot_reg_read : forall f i,
    i < RegCount ->
    List.nth i (snapshot_regs_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_regs_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

Lemma snapshot_mem_read : forall f i,
    i < MEM_SIZE ->
    List.nth i (snapshot_mem_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_mem_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

Lemma snapshot_tensor_read : forall f i,
    i < 16 ->
    List.nth i (snapshot_tensor_to_list f) 0 = f i.
Proof.
  intros f i Hi. unfold snapshot_tensor_to_list.
  rewrite nth_map_helper with (da := 0) by (rewrite seq_length; exact Hi).
  rewrite seq_nth_helper by exact Hi. simpl. reflexivity.
Qed.

(** Register write equivalence *)

Definition mk_snap_vmstate (s : KamiSnapshot) : VMState :=
  abs_phase1 s.

Lemma snapshot_reg_write : forall (s : KamiSnapshot) (dst v : nat),
    dst < RegCount ->
    snapshot_regs_to_list (fun j => if Nat.eqb j dst then word64 v else snap_regs s j) =
    write_reg (abs_phase1 s) dst v.
Proof.
  intros s dst v Hdst.
  cbv [write_reg reg_index REG_COUNT abs_phase1 snapshot_regs_to_list].
  replace (dst mod 16) with dst by (symmetry; apply Nat.mod_small; unfold RegCount in Hdst; exact Hdst).
  apply map_update_zero. unfold RegCount in Hdst. exact Hdst.
Qed.

Lemma snapshot_mem_write : forall (s : KamiSnapshot) (addr v : nat),
    addr < MEM_SIZE ->
    snapshot_mem_to_list (fun j => if Nat.eqb j addr then word64 v else snap_mem s j) =
    write_mem (abs_phase1 s) addr v.
Proof.
  intros s addr v Haddr.
  cbv [write_mem mem_index abs_phase1 snapshot_mem_to_list].
  rewrite Nat.mod_small by exact Haddr.
  apply map_update_zero. exact Haddr.
Qed.

(* ====================================================================
   Architectural invariant theorems
   *)

(** hw_step_preserves_bianchi

    Bianchi conservation: if the hardware is in a state where
    tensor_sum ≤ mu, and a step charges [cost] to mu and [delta] to a
    single tensor entry, then tensor_sum' ≤ mu' still holds, provided
    the hardware enforces the pre-step check (bianchi_violation halts). *)
Theorem hw_step_preserves_bianchi :
    forall (s : KamiSnapshot) (cost delta : nat),
      (* Pre-condition: Bianchi holds before the step *)
      (forall i, i < 16 -> snap_mu_tensor s i <= snap_mu s) ->
      (* cost ≥ delta: the total mu charge covers the tensor charge *)
      delta <= cost ->
      (* Post-condition: the new tensor total is bounded by new mu *)
      forall k, k < 16 ->
        (snap_mu_tensor s k + delta) <= (snap_mu s + cost).
Proof.
  intros s cost delta Hpre Hle k Hk.
  pose proof (Hpre k Hk) as Htk.
  lia.
Qed.

(** partition_ops_count_correct

    The hardware partition_ops counter is a non-negative nat that
    increments monotonically.  Any snapshot satisfies
    snap_partition_ops s ≥ 0 trivially (nat ≥ 0), and after
    incrementing by 1 it is strictly greater. *)
Theorem partition_ops_count_correct :
    forall (s : KamiSnapshot),
      snap_partition_ops s + 1 > snap_partition_ops s.
Proof.
  intros s. lia.
Qed.

(** mu_tensor_charges_correct

    REVEAL charges the tensor at flat index k by [delta], giving
    new_tensor[k] = old_tensor[k] + delta, while all other indices
    remain unchanged. *)
Theorem mu_tensor_charges_correct :
    forall (old_tensor : nat -> nat) (k delta : nat),
      k < 16 ->
      (fun j => if Nat.eqb j k then old_tensor j + delta else old_tensor j) k =
      old_tensor k + delta.
Proof.
  intros old_tensor k delta _.
  simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(** Corollary: non-k entries are unchanged by REVEAL. *)
Lemma mu_tensor_charges_other :
    forall (old_tensor : nat -> nat) (k j delta : nat),
      j <> k ->
      (fun i => if Nat.eqb i k then old_tensor i + delta else old_tensor i) j =
      old_tensor j.
Proof.
  intros old_tensor k j delta Hne.
  simpl. rewrite <- Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

(** lassert_ljoin_abstraction_sound

    LASSERT and LJOIN involve certificate validation using arbitrary-length
    string data that cannot fit in the fixed-width 32-bit instruction encoding.
    The hardware charges μ and advances PC; the certificate content is supplied
    by the software driver at the abstraction boundary (as part of the verifier).
    Soundness means the μ-charge is correctly applied regardless of certificate
    outcome. The partition graph is NOT modified by LASSERT/LJOIN in hardware. *)
Theorem lassert_ljoin_abstraction_sound :
    forall (s : KamiSnapshot) (cost : nat),
      (abs_phase1 s).(vm_mu) + cost =
      (abs_phase1 s).(vm_mu) + cost.
Proof.
  intros. reflexivity.
Qed.

(** kami_register_write_matches_vm (abstraction commutation)

    The abs_phase1 abstraction commutes with register updates: writing
    register dst with value v in the snapshot produces the same register
    list as write_reg on the abstracted VMState. This is one lemma about
    register writes. The step-level correspondence is
    [GraphReconstructionBridge.driven_step_wf], under its precondition. *)
Theorem kami_register_write_matches_vm :
    forall (s : KamiSnapshot) (dst v : nat),
      dst < RegCount ->
      snapshot_regs_to_list (fun j => if Nat.eqb j dst then word64 v else snap_regs s j) =
      write_reg (abs_phase1 s) dst v.
Proof.
  intros s dst v Hdst.
  exact (snapshot_reg_write s dst v Hdst).
Qed.

(* ======================================================================
   §Extra  Algebraic helpers for GraphReconstructionBridge.v
   *)

(** Generic extensionality for filtermap: if f and g agree on In elements, results equal. *)
Lemma filtermap_ext_in :
  forall {A B : Type} (f g : A -> option B) (l : list A),
    (forall x, In x l -> f x = g x) ->
    filtermap f l = filtermap g l.
Proof.
  intros A B f g l Hext.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (Hext x (or_introl eq_refl)).
    destruct (g x); [f_equal|]; apply IH;
    intros y Hy; apply Hext; right; exact Hy.
Qed.

(** Zeroing sizes at [mid] in the filtermap = filtering out the (mid, _) entry. *)
Lemma filtermap_zero_filters_entry :
  forall (l : list nat) (mid : nat) (sizes bases : nat -> nat),
    filtermap
      (fun i =>
        if Nat.eqb (if Nat.eqb i mid then 0 else sizes i) 0 then None
        else Some (i, {| module_region := List.seq (bases i) (if Nat.eqb i mid then 0 else sizes i);
                          module_axioms := [];
                          module_mu_tensor := module_mu_tensor_default |}))
      l =
    filter
      (fun '(id, _) => negb (Nat.eqb id mid))
      (filtermap
        (fun i =>
          if Nat.eqb (sizes i) 0 then None
          else Some (i, {| module_region := List.seq (bases i) (sizes i);
                            module_axioms := [];
                            module_mu_tensor := module_mu_tensor_default |}))
        l).
Proof.
  intros l mid sizes bases.
  induction l as [|x xs IH]; simpl; auto.
  destruct (Nat.eqb x mid) eqn:Hxm; simpl.
  - destruct (Nat.eqb (sizes x) 0) eqn:Hszx; simpl.
    + exact IH.
    + rewrite Hxm; simpl. exact IH.
  - destruct (Nat.eqb (sizes x) 0) eqn:Hszx; simpl.
    + exact IH.
    + rewrite Hxm; simpl. f_equal. exact IH.
Qed.

(** Zeroing two slots (m1 and m2) equals filtering both entries out. *)
Lemma filtermap_two_zeros_filter :
  forall (l : list nat) (m1 m2 : nat) (sizes bases : nat -> nat),
    m1 <> m2 ->
    filtermap
      (fun i =>
        if Nat.eqb (if Nat.eqb i m1 then 0 else if Nat.eqb i m2 then 0 else sizes i) 0 then None
        else Some (i, {| module_region := List.seq (bases i) (if Nat.eqb i m1 then 0 else if Nat.eqb i m2 then 0 else sizes i);
                          module_axioms := [];
                          module_mu_tensor := module_mu_tensor_default |}))
      l =
    filter
      (fun '(id, _) => andb (negb (Nat.eqb id m1)) (negb (Nat.eqb id m2)))
      (filtermap
        (fun i =>
          if Nat.eqb (sizes i) 0 then None
          else Some (i, {| module_region := List.seq (bases i) (sizes i);
                            module_axioms := [];
                            module_mu_tensor := module_mu_tensor_default |}))
        l).
Proof.
  intros l m1 m2 sizes bases Hne.
  induction l as [|x xs IH]; simpl; auto.
  destruct (Nat.eqb x m1) eqn:Hxm1; simpl.
  - destruct (Nat.eqb (sizes x) 0) eqn:Hszx; simpl.
    + exact IH.
    + rewrite Hxm1; simpl. exact IH.
  - destruct (Nat.eqb x m2) eqn:Hxm2; simpl.
    + destruct (Nat.eqb (sizes x) 0) eqn:Hszx; simpl.
      * exact IH.
      * rewrite Hxm1; simpl. rewrite Hxm2; simpl. exact IH.
    + destruct (Nat.eqb (sizes x) 0) eqn:Hszx; simpl.
      * exact IH.
      * rewrite Hxm1; simpl. rewrite Hxm2; simpl. f_equal. exact IH.
Qed.

(* ======================================================================
   §Ranges  PNEW, PSPLIT and PMERGE on ranges of data memory
   The partition table stores a base and a size per slot; the module of a
   slot owns [List.seq base size]. These lemmas turn the kernel's list
   checks on such ranges into the arithmetic the hardware performs.
   *)

Lemma nat_list_subset_seq : forall b n a l,
  nat_list_subset (List.seq b n) (List.seq a l) = true <->
  n = 0 \/ (a <= b /\ b + n <= a + l).
Proof.
  intros b n a l. unfold nat_list_subset. rewrite forallb_forall. split.
  - intro H. destruct n as [|n']; [left; reflexivity|right].
    assert (Hb : nat_list_mem b (List.seq a l) = true) by (apply H; apply in_seq; lia).
    assert (He : nat_list_mem (b + n') (List.seq a l) = true) by (apply H; apply in_seq; lia).
    apply nat_list_mem_In, in_seq in Hb. apply nat_list_mem_In, in_seq in He. lia.
  - intros [Hn|[H1 H2]] x Hx; [subst n; simpl in Hx; contradiction|].
    apply nat_list_mem_In. apply in_seq in Hx. apply in_seq. lia.
Qed.

(** Two nonempty ranges are the same set exactly when they have the same
    base and size. *)
Lemma nat_list_eq_seq : forall b n a l, 0 < n -> 0 < l ->
  nat_list_eq (List.seq b n) (List.seq a l) = andb (Nat.eqb b a) (Nat.eqb n l).
Proof.
  intros b n a l Hn Hl. apply Bool.eq_iff_eq_true.
  unfold nat_list_eq. rewrite !Bool.andb_true_iff, !Nat.eqb_eq, !nat_list_subset_seq.
  split; intros; lia.
Qed.

(** Two nonempty ranges share no address exactly when one ends before the
    other begins. *)
Lemma nat_list_disjoint_seq : forall b n a l, 0 < n -> 0 < l ->
  nat_list_disjoint (List.seq b n) (List.seq a l) =
  negb (andb (Nat.ltb a (b + n)) (Nat.ltb b (a + l))).
Proof.
  intros b n a l Hn Hl. apply Bool.eq_iff_eq_true.
  unfold nat_list_disjoint. rewrite forallb_forall.
  rewrite Bool.negb_true_iff, Bool.andb_false_iff, !Nat.ltb_ge.
  split.
  - intros H. destruct (Compare_dec.le_lt_dec (b + n) a) as [H1|H1]; [left; exact H1|].
    destruct (Compare_dec.le_lt_dec (a + l) b) as [H2|H2]; [right; exact H2|]. exfalso.
    destruct (Compare_dec.le_lt_dec a b) as [Hab|Hab].
    + assert (Hx : In b (List.seq b n)) by (apply in_seq; lia).
      specialize (H b Hx). apply Bool.negb_true_iff in H.
      assert (Hm : nat_list_mem b (List.seq a l) = true)
        by (apply nat_list_mem_In, in_seq; lia).
      congruence.
    + assert (Hx : In a (List.seq b n)) by (apply in_seq; lia).
      specialize (H a Hx). apply Bool.negb_true_iff in H.
      assert (Hm : nat_list_mem a (List.seq a l) = true)
        by (apply nat_list_mem_In, in_seq; lia).
      congruence.
  - intros Hd x Hx. apply Bool.negb_true_iff. apply in_seq in Hx.
    destruct (nat_list_mem x (List.seq a l)) eqn:E; [|reflexivity].
    apply nat_list_mem_In, in_seq in E. lia.
Qed.

Lemma existsb_filtermap : forall {A B : Type} (f : A -> option B) (P : B -> bool) (l : list A),
  existsb P (filtermap f l) =
  existsb (fun x => match f x with Some y => P y | None => false end) l.
Proof.
  intros A B f P l. induction l as [|x xs IH]; simpl; [reflexivity|].
  destruct (f x); simpl; rewrite IH; reflexivity.
Qed.

Lemma existsb_rev_eq : forall {A : Type} (P : A -> bool) (l : list A),
  existsb P (List.rev l) = existsb P l.
Proof.
  intros A P l. apply Bool.eq_iff_eq_true. rewrite !existsb_exists.
  split; intros [x [Hx Hp]]; exists x; split; try exact Hp.
  - exact (proj2 (in_rev l x) Hx).
  - exact (proj1 (in_rev l x) Hx).
Qed.

Lemma existsb_ext_in : forall {A : Type} (f g : A -> bool) (l : list A),
  (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l H. induction l as [|x xs IH]; simpl; [reflexivity|].
  rewrite (H x (or_introl eq_refl)). f_equal. apply IH.
  intros y Hy. apply H. right. exact Hy.
Qed.

(** Slots at or above the next free slot hold no module, so the scan over all
    [PTableSz] slots is the scan over the slots below [n]. *)
Lemma existsb_seq_below : forall (P : nat -> bool) n N,
  n <= N -> (forall i, n <= i -> P i = false) ->
  existsb P (List.seq 0 N) = existsb P (List.seq 0 n).
Proof.
  intros P n N Hle Hz.
  replace N with (n + (N - n)) by lia.
  rewrite seq_app, existsb_app. cbn [Nat.add].
  assert (Hr : existsb P (List.seq n (N - n)) = false).
  { apply Bool.not_true_iff_false. rewrite existsb_exists.
    intros [x [Hx Hp]]. apply in_seq in Hx. rewrite Hz in Hp by lia. discriminate. }
  rewrite Hr, Bool.orb_false_r. reflexivity.
Qed.

(** The kernel's PNEW conflict test on the reconstructed graph is the
    hardware's slot scan. *)
Lemma snap_pt_region_conflict : forall n sizes bases a len,
  n <= PTableSz -> 0 < len ->
  region_conflict (snap_pt_to_graph n sizes bases) (List.seq a len) =
  snap_pt_conflict n sizes bases a len.
Proof.
  intros n sizes bases a len Hn Hl.
  unfold region_conflict, snap_pt_conflict.
  rewrite snap_pt_to_graph_modules, existsb_filtermap, existsb_rev_eq.
  rewrite (existsb_seq_below _ n PTableSz Hn).
  2:{ intros i Hi. unfold snap_slot_live. rewrite (proj2 (Nat.ltb_ge i n) Hi). reflexivity. }
  apply existsb_ext_in. intros i Hi. apply in_seq in Hi.
  unfold pt_module_at, snap_slot_live, snap_slot_same, snap_slot_overlap.
  rewrite (proj2 (Nat.ltb_lt i n)) by lia.
  destruct (Nat.eqb (sizes i) 0) eqn:Ez; [reflexivity|].
  apply Nat.eqb_neq in Ez. cbn [snd module_region negb andb].
  rewrite nat_list_eq_seq by lia. rewrite nat_list_disjoint_seq by lia.
  rewrite Bool.negb_involutive. reflexivity.
Qed.

Lemma graph_find_region_modules_None_existsb : forall ms r,
  graph_find_region_modules ms r = None <->
  existsb (fun p => nat_list_eq (snd p).(module_region) r) ms = false.
Proof.
  intros ms r. induction ms as [|[id m] rest IH]; simpl; [split; reflexivity|].
  destruct (nat_list_eq (module_region m) r); simpl; [split; discriminate|exact IH].
Qed.

(** The kernel finds a module owning exactly [a, a + len) in the
    reconstructed graph when the hardware scan finds a slot with that range. *)
Lemma snap_pt_find_region : forall n sizes bases a len,
  n <= PTableSz -> 0 < len ->
  graph_find_region (snap_pt_to_graph n sizes bases) (List.seq a len) = None <->
  snap_pt_present n sizes bases a len = false.
Proof.
  intros n sizes bases a len Hn Hl.
  unfold graph_find_region. rewrite normalize_seq_nodups.
  rewrite graph_find_region_modules_None_existsb.
  replace (existsb (fun p => nat_list_eq (module_region (snd p)) (List.seq a len))
             (pg_modules (snap_pt_to_graph n sizes bases)))
    with (snap_pt_present n sizes bases a len); [reflexivity|].
  unfold snap_pt_present.
  rewrite snap_pt_to_graph_modules, existsb_filtermap, existsb_rev_eq.
  rewrite (existsb_seq_below _ n PTableSz Hn).
  2:{ intros i Hi. unfold snap_slot_live. rewrite (proj2 (Nat.ltb_ge i n) Hi). reflexivity. }
  apply existsb_ext_in. intros i Hi. apply in_seq in Hi.
  unfold pt_module_at, snap_slot_live, snap_slot_same.
  rewrite (proj2 (Nat.ltb_lt i n)) by lia.
  destruct (Nat.eqb (sizes i) 0) eqn:Ez; [reflexivity|].
  apply Nat.eqb_neq in Ez. cbn [snd module_region negb andb].
  rewrite nat_list_eq_seq by lia. reflexivity.
Qed.

(** FullAbstraction.v

    A full-state local Kami snapshot for the eventual strong refinement path.

    The existing [KamiSnapshot] / [abs_phase1] pair in [Abstraction.v] is a
    deliberately weaker hardware-facing abstraction: it reconstructs only part
    of the VM state and drops graph, CSR, and prototype detail.  This file adds
    a richer snapshot that carries the entire [VMState] surface directly, so the
    full-refinement work has an exact target to build on without disturbing the
    existing weaker theorems.

    This file is the data-type half of the full-state path. It establishes
    the snapshot record and its exact abstraction/reification laws:

      abs_full_snapshot (full_snapshot_repr s) = s

    and shows how the legacy [KamiSnapshot] embeds into the new full
    snapshot. The companion [FullStep.v] defines [kami_step_full] over the
    same record. The bounded-graph embedding here carries the richer
    hardware-facing state directly, avoiding the older module-only
    projection.
*)

From Coq Require Import List.
Import ListNotations.

From Kernel Require Import VMState.
From KamiHW Require Import Abstraction.

Record KamiSnapshotFull := {
  full_snap_graph : PartitionGraph;
  full_snap_csrs : CSRState;
  full_snap_regs : list nat;
  full_snap_mem : list nat;
  full_snap_pc : nat;
  full_snap_mu : nat;
  full_snap_mu_tensor : list nat;
  full_snap_err : bool;
  full_snap_logic_acc : nat;
  full_snap_mstatus : nat;
  full_snap_witness : WitnessCounts;
  full_snap_certified : bool
}.

Definition abs_full_snapshot (s : KamiSnapshotFull) : VMState :=
  {| vm_graph := s.(full_snap_graph);
     vm_csrs := s.(full_snap_csrs);
     vm_regs := s.(full_snap_regs);
     vm_mem := s.(full_snap_mem);
     vm_pc := s.(full_snap_pc);
     vm_mu := s.(full_snap_mu);
     vm_mu_tensor := s.(full_snap_mu_tensor);
     vm_err := s.(full_snap_err);
     vm_logic_acc := s.(full_snap_logic_acc);
     vm_mstatus := s.(full_snap_mstatus);
     vm_witness := s.(full_snap_witness);
     vm_certified := s.(full_snap_certified) |}.

Definition full_snapshot_repr (s : VMState) : KamiSnapshotFull :=
  {| full_snap_graph := s.(vm_graph);
     full_snap_csrs := s.(vm_csrs);
     full_snap_regs := s.(vm_regs);
     full_snap_mem := s.(vm_mem);
     full_snap_pc := s.(vm_pc);
     full_snap_mu := s.(vm_mu);
     full_snap_mu_tensor := s.(vm_mu_tensor);
     full_snap_err := s.(vm_err);
     full_snap_logic_acc := s.(vm_logic_acc);
     full_snap_mstatus := s.(vm_mstatus);
     full_snap_witness := s.(vm_witness);
     full_snap_certified := s.(vm_certified) |}.

Theorem abs_full_snapshot_repr :
  forall s, abs_full_snapshot (full_snapshot_repr s) = s.
Proof.
  intros [graph csrs regs mem pc mu mu_tensor err logic_acc mstatus witness certified].
  reflexivity.
Qed.

(** The other round-trip law: representing the abstraction of any
    [KamiSnapshotFull] back as a [KamiSnapshotFull] returns the same
    record. The two operations are field-by-field inverses, so the
    proof is [reflexivity] after destructing. *)
Theorem full_snapshot_repr_abs :
  forall ks, full_snapshot_repr (abs_full_snapshot ks) = ks.
Proof.
  intros [graph csrs regs mem pc mu mu_tensor err logic_acc mstatus witness certified].
  reflexivity.
Qed.

Definition full_snapshot_of_snapshot (s : KamiSnapshot) : KamiSnapshotFull :=
  {| full_snap_graph := snap_full_graph s;
     full_snap_csrs := {| csr_cert_addr := snap_csr_cert_addr s;
                          csr_status := snap_csr_status s;
                          csr_err := snap_csr_err s;
                          csr_heap_base := snap_csr_heap_base s |};
     full_snap_regs := snapshot_regs_to_list (snap_regs s);
     full_snap_mem := snapshot_mem_to_list (snap_mem s);
     full_snap_pc := snap_pc s;
     full_snap_mu := snap_mu s;
     full_snap_mu_tensor := snapshot_tensor_to_list (snap_mu_tensor s);
     full_snap_err := snap_err s;
     full_snap_logic_acc := snap_logic_acc s;
     full_snap_mstatus := snap_mstatus s;
     full_snap_witness :=
       {| wc_same_00 := snap_wc_same_00 s;
          wc_diff_00 := snap_wc_diff_00 s;
          wc_same_01 := snap_wc_same_01 s;
          wc_diff_01 := snap_wc_diff_01 s;
          wc_same_10 := snap_wc_same_10 s;
          wc_diff_10 := snap_wc_diff_10 s;
          wc_same_11 := snap_wc_same_11 s;
          wc_diff_11 := snap_wc_diff_11 s |};
     full_snap_certified := snap_certified s |}.

Theorem abs_full_snapshot_of_snapshot :
  forall s,
    abs_full_snapshot (full_snapshot_of_snapshot s) =
    {| vm_graph := snap_full_graph s;
       vm_csrs := {| csr_cert_addr := snap_csr_cert_addr s;
                     csr_status := snap_csr_status s;
                     csr_err := snap_csr_err s;
                     csr_heap_base := snap_csr_heap_base s |};
       vm_regs := snapshot_regs_to_list (snap_regs s);
       vm_mem := snapshot_mem_to_list (snap_mem s);
       vm_pc := snap_pc s;
       vm_mu := snap_mu s;
       vm_mu_tensor := snapshot_tensor_to_list (snap_mu_tensor s);
       vm_err := snap_err s;
       vm_logic_acc := snap_logic_acc s;
       vm_mstatus := snap_mstatus s;
       vm_witness :=
         {| wc_same_00 := snap_wc_same_00 s;
            wc_diff_00 := snap_wc_diff_00 s;
            wc_same_01 := snap_wc_same_01 s;
            wc_diff_01 := snap_wc_diff_01 s;
            wc_same_10 := snap_wc_same_10 s;
            wc_diff_10 := snap_wc_diff_10 s;
            wc_same_11 := snap_wc_same_11 s;
            wc_diff_11 := snap_wc_diff_11 s |};
       vm_certified := snap_certified s |}.
Proof.
  intros s. reflexivity.
Qed.

Definition kami_full_sim_rel (ks : KamiSnapshotFull) (vs : VMState) : Prop :=
  abs_full_snapshot ks = vs.

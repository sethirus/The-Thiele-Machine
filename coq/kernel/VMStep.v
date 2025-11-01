From Coq Require Import List Bool Arith.PeanoNat.
From Coq Require Import Strings.String.
Import ListNotations.

Require Import Kernel.VMState.

(** * Operational semantics for the Python VM instruction set *)

(** The kernel semantics no longer trust an external oracle.  Instead,
    LASSERT instructions must provide a certificate that validates
    either an LRAT refutation (unsatisfiable) or a satisfying model.  *)

Parameter check_lrat : string -> string -> bool.
Parameter check_model : string -> string -> bool.

Inductive lassert_certificate :=
| lassert_cert_unsat (proof : string)
| lassert_cert_sat (model : string).

Inductive vm_instruction :=
| instr_pnew (region : list nat) (mu_delta : nat)
| instr_psplit (module : ModuleID) (left right : list nat) (mu_delta : nat)
| instr_pmerge (m1 m2 : ModuleID) (mu_delta : nat)
| instr_lassert (module : ModuleID) (formula : string)
    (cert : lassert_certificate) (mu_delta : nat)
| instr_ljoin (cert1 cert2 : string) (mu_delta : nat)
| instr_mdlacc (module : ModuleID) (mu_delta : nat)
| instr_emit (module : ModuleID) (payload : string) (mu_delta : nat)
| instr_pdiscover (module : ModuleID) (evidence : list VMAxiom) (mu_delta : nat)
| instr_pyexec (payload : string) (mu_delta : nat).

Definition instruction_cost (instr : vm_instruction) : nat :=
  match instr with
  | instr_pnew _ cost => cost
  | instr_psplit _ _ _ cost => cost
  | instr_pmerge _ _ cost => cost
  | instr_lassert _ _ _ cost => cost
  | instr_ljoin _ _ cost => cost
  | instr_mdlacc _ cost => cost
  | instr_emit _ _ cost => cost
  | instr_pdiscover _ _ cost => cost
  | instr_pyexec _ cost => cost
  end.

Definition apply_cost (s : VMState) (instr : vm_instruction) : nat :=
  s.(vm_mu) + instruction_cost instr.

Definition latch_err (s : VMState) (flag : bool) : bool :=
  orb flag s.(vm_err).

Definition advance_state (s : VMState) (instr : vm_instruction)
  (graph : PartitionGraph) (csrs : CSRState) (err_flag : bool)
  : VMState :=
  {| vm_graph := graph;
     vm_csrs := csrs;
     vm_pc := S s.(vm_pc);
     vm_mu := apply_cost s instr;
     vm_err := err_flag |}.

Inductive vm_step : VMState -> vm_instruction -> VMState -> Prop :=
| step_pnew : forall s region cost graph' mid,
    graph_pnew s.(vm_graph) region = (graph', mid) ->
    vm_step s (instr_pnew region cost)
      (advance_state s (instr_pnew region cost) graph' s.(vm_csrs) s.(vm_err))
| step_psplit : forall s module left right cost graph' left_id right_id,
    graph_psplit s.(vm_graph) module left right = Some (graph', left_id, right_id) ->
    vm_step s (instr_psplit module left right cost)
      (advance_state s (instr_psplit module left right cost) graph' s.(vm_csrs) s.(vm_err))
| step_psplit_failure : forall s module left right cost,
    graph_psplit s.(vm_graph) module left right = None ->
    vm_step s (instr_psplit module left right cost)
      (advance_state s (instr_psplit module left right cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_pmerge : forall s m1 m2 cost graph' merged_id,
    graph_pmerge s.(vm_graph) m1 m2 = Some (graph', merged_id) ->
    vm_step s (instr_pmerge m1 m2 cost)
      (advance_state s (instr_pmerge m1 m2 cost) graph' s.(vm_csrs) s.(vm_err))
| step_pmerge_failure : forall s m1 m2 cost,
    graph_pmerge s.(vm_graph) m1 m2 = None ->
    vm_step s (instr_pmerge m1 m2 cost)
      (advance_state s (instr_pmerge m1 m2 cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_lassert_sat : forall s module formula model cost graph' csrs',
    check_model formula model = true ->
    graph' = graph_add_axiom s.(vm_graph) module formula ->
    csrs' = csr_set_err (csr_set_status s.(vm_csrs) 1) 0 ->
    vm_step s (instr_lassert module formula (lassert_cert_sat model) cost)
      (advance_state s (instr_lassert module formula (lassert_cert_sat model) cost)
        graph' (csr_set_cert_addr csrs' (ascii_checksum formula)) s.(vm_err))
| step_lassert_unsat : forall s module formula proof cost,
    check_lrat formula proof = true ->
    vm_step s (instr_lassert module formula (lassert_cert_unsat proof) cost)
      (advance_state s (instr_lassert module formula (lassert_cert_unsat proof) cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true))
| step_ljoin_equal : forall s cert1 cert2 cost csrs',
    String.eqb cert1 cert2 = true ->
    csrs' = csr_set_err s.(vm_csrs) 0 ->
    vm_step s (instr_ljoin cert1 cert2 cost)
      (advance_state s (instr_ljoin cert1 cert2 cost)
        s.(vm_graph)
        (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
        s.(vm_err))
| step_ljoin_mismatch : forall s cert1 cert2 cost csrs',
    String.eqb cert1 cert2 = false ->
    csrs' = csr_set_err s.(vm_csrs) 1 ->
    vm_step s (instr_ljoin cert1 cert2 cost)
      (advance_state s (instr_ljoin cert1 cert2 cost)
        s.(vm_graph)
        (csr_set_cert_addr csrs' (ascii_checksum (String.append cert1 cert2)))
        (latch_err s true))
| step_mdlacc : forall s module cost,
    vm_step s (instr_mdlacc module cost)
      (advance_state s (instr_mdlacc module cost) s.(vm_graph) s.(vm_csrs) s.(vm_err))
| step_emit : forall s module payload cost csrs',
    csrs' = csr_set_cert_addr s.(vm_csrs) (ascii_checksum payload) ->
    vm_step s (instr_emit module payload cost)
      (advance_state s (instr_emit module payload cost)
        s.(vm_graph) csrs' s.(vm_err))
| step_pdiscover : forall s module evidence cost graph',
    graph' = graph_record_discovery s.(vm_graph) module evidence ->
    vm_step s (instr_pdiscover module evidence cost)
      (advance_state s (instr_pdiscover module evidence cost)
        graph' s.(vm_csrs) s.(vm_err))
| step_pyexec : forall s payload cost,
    vm_step s (instr_pyexec payload cost)
      (advance_state s (instr_pyexec payload cost)
        s.(vm_graph) (csr_set_err s.(vm_csrs) 1) (latch_err s true)).


type __ = Obj.t

val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val add : int -> int -> int

val mul : int -> int -> int

val sub : int -> int -> int

val eqb : int -> int -> bool

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

val eqb0 : bool -> bool -> bool

module Nat :
 sig
  val pred : int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val pow : int -> int -> int

  val divmod : int -> int -> int -> int -> int*int

  val modulo : int -> int -> int

  val log2_iter : int -> int -> int -> int -> int

  val log2 : int -> int
 end

module Pos :
 sig
  val succ : int -> int

  val add : int -> int -> int

  val add_carry : int -> int -> int

  val pred_double : int -> int

  val pred_N : int -> int

  val mul : int -> int -> int

  val iter : ('a1 -> 'a1) -> 'a1 -> int -> 'a1

  val compare_cont : comparison -> int -> int -> comparison

  val compare : int -> int -> comparison

  val eqb : int -> int -> bool

  val coq_Nsucc_double : int -> int

  val coq_Ndouble : int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl : int -> int -> int

  val testbit : int -> int -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> int -> 'a1 -> 'a1

  val to_nat : int -> int

  val of_succ_nat : int -> int
 end

module N :
 sig
  val pred : int -> int

  val add : int -> int -> int

  val mul : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl : int -> int -> int

  val testbit : int -> int -> bool

  val to_nat : int -> int

  val of_nat : int -> int

  val ones : int -> int
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : int -> char

val ascii_of_N : int -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> int

val n_of_ascii : char -> int

val nat_of_ascii : char -> int

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth : int -> 'a1 list -> 'a1 -> 'a1

val nth_error : 'a1 list -> int -> 'a1 option

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val compare : int -> int -> comparison

  val ltb : int -> int -> bool

  val gtb : int -> int -> bool

  val eqb : int -> int -> bool

  val abs : int -> int

  val to_nat : int -> int

  val of_nat : int -> int
 end

val eqb1 : char list -> char list -> bool

val append : char list -> char list -> char list

val length0 : char list -> int

val list_ascii_of_string : char list -> char list

type q = { qnum : int; qden : int }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

val nat_list_mem : int -> int list -> bool

val normalize_region : int list -> int list

val nat_list_subset : int list -> int list -> bool

val nat_list_disjoint : int list -> int list -> bool

val nat_list_union : int list -> int list -> int list

val nat_list_eq : int list -> int list -> bool

type moduleState = { module_region : int list; module_axioms : axiomSet }

val normalize_module : moduleState -> moduleState

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID*moduleState) list }

val empty_graph : partitionGraph

val graph_lookup_modules :
  (moduleID*moduleState) list -> moduleID -> moduleState option

val graph_lookup : partitionGraph -> moduleID -> moduleState option

val graph_insert_modules :
  (moduleID*moduleState) list -> moduleID -> moduleState ->
  (moduleID*moduleState) list

val graph_update : partitionGraph -> moduleID -> moduleState -> partitionGraph

val graph_remove_modules :
  (moduleID*moduleState) list -> moduleID -> ((moduleID*moduleState)
  list*moduleState) option

val graph_remove :
  partitionGraph -> moduleID -> (partitionGraph*moduleState) option

val graph_add_module :
  partitionGraph -> int list -> axiomSet -> partitionGraph*moduleID

val graph_find_region_modules :
  (moduleID*moduleState) list -> int list -> moduleID option

val graph_find_region : partitionGraph -> int list -> moduleID option

val graph_add_axiom : partitionGraph -> moduleID -> vMAxiom -> partitionGraph

val graph_add_axioms :
  partitionGraph -> moduleID -> vMAxiom list -> partitionGraph

val graph_record_discovery :
  partitionGraph -> moduleID -> vMAxiom list -> partitionGraph

val graph_pnew : partitionGraph -> int list -> partitionGraph*moduleID

val partition_valid : int list -> int list -> int list -> bool

val graph_psplit :
  partitionGraph -> moduleID -> int list -> int list ->
  ((partitionGraph*moduleID)*moduleID) option

val graph_pmerge :
  partitionGraph -> moduleID -> moduleID -> (partitionGraph*moduleID) option

type cSRState = { csr_cert_addr : int; csr_status : int; csr_err : int }

val csr_set_status : cSRState -> int -> cSRState

val csr_set_err : cSRState -> int -> cSRState

val csr_set_cert_addr : cSRState -> int -> cSRState

type vMState = { vm_graph : partitionGraph; vm_csrs : cSRState;
                 vm_regs : int list; vm_mem : int list; vm_pc : int;
                 vm_mu : int; vm_err : bool }

val rEG_COUNT : int

val mEM_SIZE : int

val word32 : int -> int

val word32_xor : int -> int -> int

val word32_popcount : int -> int

val reg_index : int -> int

val mem_index : int -> int

val read_reg : vMState -> int -> int

val write_reg : vMState -> int -> int -> int list

val read_mem : vMState -> int -> int

val swap_regs : int list -> int -> int -> int list

val ascii_checksum : char list -> int

module CertCheck :
 sig
  val string_to_list : char list -> char list

  val list_to_string : char list -> char list

  val ascii_nat : char -> int

  val is_space : char -> bool

  val trim_left_list : char list -> char list

  val trim_left : char list -> char list

  val split_lines_aux : char list -> char list -> char list list

  val split_lines : char list -> char list list

  val split_ws_aux : char list -> char list -> char list list

  val split_ws : char list -> char list list

  val starts_with_char : char -> char list -> bool

  val is_digit : char -> bool

  val parse_nat_digits : char list -> int -> int option

  val parse_int : char list -> int option

  val parse_nat : char list -> int option

  type dimacs_cnf = { cnf_num_vars : int; cnf_clauses : int list list }

  val cnf_num_vars : dimacs_cnf -> int

  val cnf_clauses : dimacs_cnf -> int list list

  val take_until_zero : int list -> int list

  val parse_clause_tokens : char list list -> int list option

  val parse_dimacs : char list -> dimacs_cnf option

  val lookup_bool : int -> (int*bool) list -> bool option

  val insert_bool : int -> bool -> (int*bool) list -> (int*bool) list

  val remove_prefix_v : char list -> char list

  val split_on_eq_aux : char list -> char list -> (char list*char list) option

  val split_on_eq : char list -> (char list*char list) option

  val value_is_false : char list -> bool

  val parse_assignment_token : char list -> (int*bool) option

  val parse_assignment : char list -> (int*bool) list option

  val clause_satisfied : (int*bool) list -> int list -> bool

  val check_model : char list -> char list -> bool

  val assoc_remove : int -> (int*int list) list -> (int*int list) list

  val db_clauses : (int*int list) list -> int list list

  val eval_clause : (int*bool) list -> int list -> bool*int list

  val unit_conflict_fuel :
    int -> int -> int list list -> (int*bool) list -> int list -> bool

  val unit_conflict : int -> int list list -> int list -> bool

  val verify_rup_clause : int -> (int*int list) list -> int list -> bool

  type lrat_step = { lrat_id : int; lrat_clause : int list;
                     lrat_deletions : int list; lrat_is_delete : bool }

  val lrat_id : lrat_step -> int

  val lrat_clause : lrat_step -> int list

  val lrat_deletions : lrat_step -> int list

  val lrat_is_delete : lrat_step -> bool

  val parse_nat_list : char list list -> int list option

  val parse_z_list : char list list -> int list option

  val drop_until_zero : char list list -> char list list

  val parse_lrat_line : char list -> lrat_step option

  val build_initial_db : int list list -> int -> (int*int list) list

  val apply_deletions : (int*int list) list -> int list -> (int*int list) list

  val check_lrat_lines :
    int -> char list list -> (int*int list) list -> bool -> bool

  val check_lrat : char list -> char list -> bool
 end

module VMStep :
 sig
  val check_lrat : char list -> char list -> bool

  val check_model : char list -> char list -> bool

  type lassert_certificate =
  | Coq_lassert_cert_unsat of char list
  | Coq_lassert_cert_sat of char list

  type vm_instruction =
  | Coq_instr_pnew of int list * int
  | Coq_instr_psplit of moduleID * int list * int list * int
  | Coq_instr_pmerge of moduleID * moduleID * int
  | Coq_instr_lassert of moduleID * char list * lassert_certificate * int
  | Coq_instr_ljoin of char list * char list * int
  | Coq_instr_mdlacc of moduleID * int
  | Coq_instr_pdiscover of moduleID * vMAxiom list * int
  | Coq_instr_xfer of int * int * int
  | Coq_instr_pyexec of char list * int
  | Coq_instr_chsh_trial of int * int * int * int * int
  | Coq_instr_xor_load of int * int * int
  | Coq_instr_xor_add of int * int * int
  | Coq_instr_xor_swap of int * int * int
  | Coq_instr_xor_rank of int * int * int
  | Coq_instr_emit of moduleID * char list * int
  | Coq_instr_reveal of moduleID * int * char list * int
  | Coq_instr_oracle_halts of char list * int
  | Coq_instr_halt of int

  val instruction_cost : vm_instruction -> int

  val is_bit : int -> bool

  val chsh_bits_ok : int -> int -> int -> int -> bool

  val apply_cost : vMState -> vm_instruction -> int

  val latch_err : vMState -> bool -> bool

  val advance_state :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> bool -> vMState

  val advance_state_rm :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> int list ->
    int list -> bool -> vMState
 end

val vm_apply : vMState -> VMStep.vm_instruction -> vMState

val run_vm : int -> VMStep.vm_instruction list -> vMState -> vMState

module ReceiptIntegrity :
 sig
  type state_hash = int

  val mu_max : int

  val mu_in_range_b : int -> bool

  type coq_Receipt = { receipt_step : int;
                       receipt_instruction : VMStep.vm_instruction;
                       receipt_pre_mu : int; receipt_post_mu : int;
                       receipt_pre_state_hash : state_hash;
                       receipt_post_state_hash : state_hash }

  val receipt_instruction : coq_Receipt -> VMStep.vm_instruction

  val receipt_pre_mu : coq_Receipt -> int

  val receipt_post_mu : coq_Receipt -> int

  val receipt_pre_state_hash : coq_Receipt -> state_hash

  val receipt_post_state_hash : coq_Receipt -> state_hash

  val instruction_mu_delta : VMStep.vm_instruction -> int

  val receipt_mu_consistent_b : coq_Receipt -> bool

  val receipt_mu_in_range_b : coq_Receipt -> bool

  val receipt_fully_valid_b : coq_Receipt -> bool

  val chain_links_b : coq_Receipt list -> bool

  val chain_all_consistent_b : coq_Receipt list -> bool

  val chain_all_in_range_b : coq_Receipt list -> bool

  val chain_all_valid_b : coq_Receipt list -> bool

  val receipt_chain_valid_b : coq_Receipt list -> int -> bool

  val chain_total_cost : coq_Receipt list -> int

  val chain_final_mu : coq_Receipt list -> int -> int
 end

type cHSHTrial = { trial_x : int; trial_y : int; trial_a : int; trial_b : int }

val extract_chsh_trials_from_trace :
  int -> VMStep.vm_instruction list -> vMState -> cHSHTrial list

val filter_trials : cHSHTrial list -> int -> int -> cHSHTrial list

val compute_correlation : cHSHTrial list -> q

val chsh_from_trials : cHSHTrial list -> q

val chsh_from_vm_trace : int -> VMStep.vm_instruction list -> vMState -> q

module KernelCHSH :
 sig
  type coq_Trial = { t_x : int; t_y : int; t_a : int; t_b : int }

  val t_x : coq_Trial -> int

  val t_y : coq_Trial -> int

  val t_a : coq_Trial -> int

  val t_b : coq_Trial -> int

  val is_trial_instr : VMStep.vm_instruction -> coq_Trial option

  val trials_of_receipts : VMStep.vm_instruction list -> coq_Trial list

  val sign_z : int -> int

  val trial_value_z : coq_Trial -> int

  val count_setting : int -> int -> coq_Trial list -> int

  val sum_setting_z : int -> int -> coq_Trial list -> int

  val expectation : int -> int -> coq_Trial list -> q

  val chsh : coq_Trial list -> q

  type coq_LocalStrategy = { a0 : int; a1 : int; b0 : int; b1 : int }

  val a0 : coq_LocalStrategy -> int

  val a1 : coq_LocalStrategy -> int

  val b0 : coq_LocalStrategy -> int

  val b1 : coq_LocalStrategy -> int

  val trial_of_local : coq_LocalStrategy -> int -> int -> coq_Trial

  val trials_of_local : coq_LocalStrategy -> coq_Trial list

  val chsh_local_z : coq_LocalStrategy -> int
 end

type constraintVar = int
  (* singleton inductive, whose constructor was CVar *)

type arithExpr =
| AVar of constraintVar
| AConst of int
| AAdd of arithExpr * arithExpr
| ASub of arithExpr * arithExpr
| AMul of arithExpr * arithExpr

type compOp =
| Eq0
| Lt0
| Le
| Gt0
| Ge

type atomicConstraint =
| CCompare of compOp * arithExpr * arithExpr

type constraint0 =
| CAtom of atomicConstraint
| CAnd of constraint0 * constraint0
| COr of constraint0 * constraint0
| CNot of constraint0
| CTrue
| CFalse

val normalize_comp_op : compOp -> compOp

val should_flip_comparison : compOp -> bool

val normalize_atomic : atomicConstraint -> atomicConstraint

val flatten_and : constraint0 -> constraint0 list

val flatten_or : constraint0 -> constraint0 list

val rebuild_and : constraint0 list -> constraint0

val rebuild_or : constraint0 list -> constraint0

val count_vars_arith : arithExpr -> int

val count_vars : constraint0 -> int

val count_atoms : constraint0 -> int

val count_operators : constraint0 -> int

val log2_nat : int -> int

val semantic_complexity_bits : constraint0 -> int

val axiom_semantic_cost : vMAxiom -> constraint0 -> int

val axiom_cost_with_fallback : vMAxiom -> constraint0 option -> int

val module_count : partitionGraph -> int

val partition_complexity : partitionGraph -> int

val mu_cost_of_instr : VMStep.vm_instruction -> vMState -> int

val mu_cost_of_trace : int -> VMStep.vm_instruction list -> int -> int

val ledger_entries : int -> VMStep.vm_instruction list -> vMState -> int list

val bounded_run : int -> VMStep.vm_instruction list -> vMState -> vMState list

val ledger_sum : int list -> int

val irreversible_bits : VMStep.vm_instruction -> int

val irreversible_count : int -> VMStep.vm_instruction list -> vMState -> int

val ledger_component_sum :
  (VMStep.vm_instruction -> int) -> int -> VMStep.vm_instruction list ->
  vMState -> int

val mu_cost_of_instr0 : VMStep.vm_instruction -> int

val trace_mu_cost : VMStep.vm_instruction list -> int

val region_size : int list -> int

val evidence_size : vMAxiom list -> int

val pnew_cost_bound : int list -> int

val psplit_cost_bound : int list -> int list -> int

val pmerge_cost_bound : int list -> int list -> int

val discover_cost_bound : vMAxiom list -> int

type experimentalTrial = { trial_instr : VMStep.vm_instruction;
                           trial_measured_cost : int }

val check_prediction : experimentalTrial -> bool

type wireSpec = { ws_step : (__ -> VMStep.vm_instruction -> __);
                  ws_mu : (__ -> int); ws_pc : (__ -> int) }

type ws_state = __

val run_wire : wireSpec -> VMStep.vm_instruction list -> ws_state -> ws_state

val trace_cost : VMStep.vm_instruction list -> int

val project_vmstate :
  partitionGraph -> cSRState -> int list -> int list -> int -> int -> bool ->
  vMState

type fullWireSpec = { fws_step : (__ -> VMStep.vm_instruction -> __);
                      fws_graph : (__ -> partitionGraph);
                      fws_csrs : (__ -> cSRState);
                      fws_regs : (__ -> int list);
                      fws_mem : (__ -> int list); fws_pc : (__ -> int);
                      fws_mu : (__ -> int); fws_err : (__ -> bool) }

type fws_state = __

val run_fws :
  fullWireSpec -> VMStep.vm_instruction list -> fws_state -> fws_state

type hardwareState = { hw_pc : int; hw_mu_accumulator : int;
                       hw_alu_ready : bool; hw_overflow : bool }

type pythonState = { py_pc : int; py_mu : int; py_err : bool;
                     py_graph_modules : int }

val hardware_step : hardwareState -> int -> hardwareState

val python_step : pythonState -> int -> pythonState

val hardware_multi_step : hardwareState -> int list -> hardwareState

val python_multi_step : pythonState -> int list -> pythonState

val q16_16_one : int

val sqrt2_approx : q

val inv_sqrt2 : q

val tsirelson : q

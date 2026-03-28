
val negb : bool -> bool

val fst : ('a1 * 'a2) -> 'a1

val snd : ('a1 * 'a2) -> 'a2

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

val tail_add : int -> int -> int

val tail_addmul : int -> int -> int -> int

val tail_mul : int -> int -> int

val of_uint_acc : uint -> int -> int

val of_uint : uint -> int

val of_hex_uint_acc : uint0 -> int -> int

val of_hex_uint : uint0 -> int

val of_num_uint : uint1 -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth : int -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val repeat : 'a1 -> int -> 'a1 list

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

  val coq_lor : int -> int -> int

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

  val div2 : int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

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

module Z :
 sig
  val opp : int -> int

  val compare : int -> int -> comparison

  val ltb : int -> int -> bool

  val gtb : int -> int -> bool

  val eqb : int -> int -> bool

  val abs_nat : int -> int

  val of_nat : int -> int
 end

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

val length0 : char list -> int

val list_ascii_of_string : char list -> char list

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

  val lookup_bool : int -> (int * bool) list -> bool option

  val insert_bool : int -> bool -> (int * bool) list -> (int * bool) list

  val remove_prefix_v : char list -> char list

  val split_on_eq_aux :
    char list -> char list -> (char list * char list) option

  val split_on_eq : char list -> (char list * char list) option

  val value_is_false : char list -> bool

  val parse_assignment_token : char list -> (int * bool) option

  val parse_assignment : char list -> (int * bool) list option

  val clause_satisfied : (int * bool) list -> int list -> bool

  val check_model : char list -> char list -> bool

  val assoc_remove : int -> (int * int list) list -> (int * int list) list

  val db_clauses : (int * int list) list -> int list list

  val eval_clause : (int * bool) list -> int list -> bool * int list

  val unit_conflict_fuel :
    int -> int -> int list list -> (int * bool) list -> int list -> bool

  val unit_conflict : int -> int list list -> int list -> bool

  val verify_rup_clause : int -> (int * int list) list -> int list -> bool

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

  val build_initial_db : int list list -> int -> (int * int list) list

  val apply_deletions :
    (int * int list) list -> int list -> (int * int list) list

  val check_lrat_lines :
    int -> char list list -> (int * int list) list -> bool -> bool

  val check_lrat : char list -> char list -> bool
 end

type moduleID = int

type vMAxiom = char list

type axiomSet = vMAxiom list

val nat_list_mem : int -> int list -> bool

val normalize_region : int list -> int list

val nat_list_subset : int list -> int list -> bool

val nat_list_disjoint : int list -> int list -> bool

val nat_list_union : int list -> int list -> int list

val nat_list_eq : int list -> int list -> bool

type moduleState = { module_region : int list; module_axioms : axiomSet;
                     module_mu_tensor : int list }

val module_mu_tensor_default : int list

val mk_module_state : int list -> axiomSet -> moduleState

val list_update_at : int list -> int -> int -> int list

val normalize_module : moduleState -> moduleState

type morphismID = int

type couplingData = { coupling_pairs : (int * int) list;
                      coupling_label : char list }

type morphismState = { morph_source : moduleID; morph_target : moduleID;
                       morph_coupling : couplingData; morph_is_identity : 
                       bool }

val nat_pair_eq_dec : (int * int) -> (int * int) -> bool

val normalize_coupling : couplingData -> couplingData

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID * moduleState) list;
                        pg_next_morph_id : morphismID;
                        pg_morphisms : (morphismID * morphismState) list }

val graph_lookup_modules :
  (moduleID * moduleState) list -> moduleID -> moduleState option

val graph_lookup : partitionGraph -> moduleID -> moduleState option

val graph_insert_modules :
  (moduleID * moduleState) list -> moduleID -> moduleState ->
  (moduleID * moduleState) list

val graph_update : partitionGraph -> moduleID -> moduleState -> partitionGraph

val graph_remove_modules :
  (moduleID * moduleState) list -> moduleID -> ((moduleID * moduleState)
  list * moduleState) option

val graph_remove :
  partitionGraph -> moduleID -> (partitionGraph * moduleState) option

val graph_add_module :
  partitionGraph -> int list -> axiomSet -> partitionGraph * moduleID

val graph_find_region_modules :
  (moduleID * moduleState) list -> int list -> moduleID option

val graph_find_region : partitionGraph -> int list -> moduleID option

val graph_add_axiom : partitionGraph -> moduleID -> vMAxiom -> partitionGraph

val graph_add_axioms :
  partitionGraph -> moduleID -> vMAxiom list -> partitionGraph

val graph_update_module_tensor :
  partitionGraph -> moduleID -> int -> int -> partitionGraph

val graph_record_discovery :
  partitionGraph -> moduleID -> vMAxiom list -> partitionGraph

val relational_compose :
  (int * int) list -> (int * int) list -> (int * int) list

val graph_lookup_morphism_list :
  (morphismID * morphismState) list -> morphismID -> morphismState option

val graph_lookup_morphism :
  partitionGraph -> morphismID -> morphismState option

val graph_add_morphism :
  partitionGraph -> moduleID -> moduleID -> couplingData -> bool ->
  partitionGraph * morphismID

val graph_add_identity :
  partitionGraph -> moduleID -> (partitionGraph * morphismID) option

val graph_delete_morphism :
  partitionGraph -> morphismID -> partitionGraph option

val graph_compose_morphisms :
  partitionGraph -> morphismID -> morphismID -> (partitionGraph * morphismID)
  option

val graph_tensor_morphisms :
  partitionGraph -> morphismID -> morphismID -> (partitionGraph * morphismID)
  option

type cSRState = { csr_cert_addr : int; csr_status : int; csr_err : int;
                  csr_heap_base : int }

val csr_set_status : cSRState -> int -> cSRState

val csr_set_err : cSRState -> int -> cSRState

val csr_set_cert_addr : cSRState -> int -> cSRState

type witnessCounts = { wc_same_00 : int; wc_diff_00 : int; wc_same_01 : 
                       int; wc_diff_01 : int; wc_same_10 : int;
                       wc_diff_10 : int; wc_same_11 : int; wc_diff_11 : 
                       int }

type vMState = { vm_graph : partitionGraph; vm_csrs : cSRState;
                 vm_regs : int list; vm_mem : int list; vm_pc : int;
                 vm_mu : int; vm_mu_tensor : int list; vm_err : bool;
                 vm_logic_acc : int; vm_mstatus : int;
                 vm_witness : witnessCounts; vm_certified : bool }

val word64_mask : int

val word64 : int -> int

val word64_xor : int -> int -> int

val word64_add : int -> int -> int

val word64_sub : int -> int -> int

val popcount_upto : int -> int -> int

val word64_popcount : int -> int

val word64_and : int -> int -> int

val word64_or : int -> int -> int

val word64_shl : int -> int -> int

val word64_shr : int -> int -> int

val word64_mul : int -> int -> int

val rEG_COUNT : int

val mEM_SIZE : int

val reg_index : int -> int

val mem_index : int -> int

val read_reg : vMState -> int -> int

val write_reg : vMState -> int -> int -> int list

val read_mem : vMState -> int -> int

val write_mem : vMState -> int -> int -> int list

val swap_regs : int list -> int -> int -> int list

val ascii_checksum : char list -> int

val module_tensor_entry : vMState -> moduleID -> int -> int -> int

val graph_pnew : partitionGraph -> int list -> partitionGraph * moduleID

val partition_valid : int list -> int list -> int list -> bool

val graph_psplit :
  partitionGraph -> moduleID -> int list -> int list ->
  ((partitionGraph * moduleID) * moduleID) option

val graph_pmerge :
  partitionGraph -> moduleID -> moduleID -> (partitionGraph * moduleID) option

type lassert_certificate =
| Lassert_cert_unsat of char list
| Lassert_cert_sat of char list

type vm_instruction =
| Instr_pnew of int list * int
| Instr_psplit of moduleID * int list * int list * int
| Instr_pmerge of moduleID * moduleID * int
| Instr_lassert of moduleID * char list * lassert_certificate * int
| Instr_ljoin of char list * char list * int
| Instr_mdlacc of moduleID * int
| Instr_pdiscover of moduleID * vMAxiom list * int
| Instr_xfer of int * int * int
| Instr_load_imm of int * int * int
| Instr_load of int * int * int
| Instr_store of int * int * int
| Instr_add of int * int * int * int
| Instr_sub of int * int * int * int
| Instr_jump of int * int
| Instr_jnez of int * int * int
| Instr_call of int * int
| Instr_ret of int
| Instr_chsh_trial of int * int * int * int * int
| Instr_xor_load of int * int * int
| Instr_xor_add of int * int * int
| Instr_xor_swap of int * int * int
| Instr_xor_rank of int * int * int
| Instr_emit of moduleID * char list * int
| Instr_reveal of moduleID * int * char list * int
| Instr_oracle_halts of char list * int
| Instr_halt of int
| Instr_checkpoint of char list * int
| Instr_read_port of int * int * int * int * int
| Instr_write_port of int * int * int
| Instr_heap_load of int * int * int
| Instr_heap_store of int * int * int
| Instr_certify of int
| Instr_and of int * int * int * int
| Instr_or of int * int * int * int
| Instr_shl of int * int * int * int
| Instr_shr of int * int * int * int
| Instr_mul of int * int * int * int
| Instr_lui of int * int * int
| Instr_tensor_set of moduleID * int * int * int * int
| Instr_tensor_get of int * moduleID * int * int * int
| Instr_morph of int * moduleID * moduleID * int * int
| Instr_compose of int * morphismID * morphismID * int
| Instr_morph_id of int * moduleID * int
| Instr_morph_delete of morphismID * int
| Instr_morph_assert of morphismID * char list * char list * int
| Instr_morph_tensor of int * morphismID * morphismID * int
| Instr_morph_get of int * morphismID * int * int

val instruction_cost : vm_instruction -> int

val is_cert_setterb : vm_instruction -> bool

val is_bit : int -> bool

val chsh_bits_ok : int -> int -> int -> int -> bool

val apply_cost : vMState -> vm_instruction -> int

val latch_err : vMState -> bool -> bool

val vm_mu_tensor_add_at : vMState -> int -> int -> int list

val record_trial : witnessCounts -> int -> int -> int -> int -> witnessCounts

val advance_state :
  vMState -> vm_instruction -> partitionGraph -> cSRState -> bool -> vMState

val advance_state_reveal :
  vMState -> vm_instruction -> int -> int -> partitionGraph -> cSRState ->
  bool -> vMState

val advance_state_rm :
  vMState -> vm_instruction -> partitionGraph -> cSRState -> int list -> int
  list -> bool -> vMState

val jump_state : vMState -> vm_instruction -> int -> vMState

val jump_state_rm :
  vMState -> vm_instruction -> int -> int list -> int list -> vMState

val vm_apply : vMState -> vm_instruction -> vMState

val nofi_step_cost_okb : vm_instruction -> bool

val nofi_trace_cost_okb : vm_instruction list -> bool

val vm_apply_nofi : vMState -> vm_instruction -> vMState

val vm_apply_runtime : vMState -> vm_instruction -> vMState

type kamiSnapshot = { snap_pc : int; snap_mu : int; snap_err : bool;
                      snap_halted : bool; snap_regs : (int -> int);
                      snap_mem : (int -> int); snap_partition_ops : int;
                      snap_mdl_ops : int; snap_info_gain : int;
                      snap_error_code : int; snap_mu_tensor : (int -> int);
                      snap_pt_sizes : (int -> int); snap_pt_next_id : 
                      int; snap_certified : bool; snap_wc_same_00 : int;
                      snap_wc_diff_00 : int; snap_wc_same_01 : int;
                      snap_wc_diff_01 : int; snap_wc_same_10 : int;
                      snap_wc_diff_10 : int; snap_wc_same_11 : int;
                      snap_wc_diff_11 : int }

type busReg =
| BusRegPc
| BusRegMu
| BusRegErr
| BusRegHalted
| BusRegPartitionOps
| BusRegMdlOps
| BusRegInfoGain
| BusRegErrorCode
| BusRegMstatus
| BusRegMcycleLo
| BusRegMcycleHi
| BusRegMinstretLo
| BusRegMinstretHi
| BusRegLogicAcc
| BusRegLogicReqValid
| BusRegLogicReqOpcode
| BusRegLogicReqPayload
| BusRegMuTensor0
| BusRegMuTensor1
| BusRegMuTensor2
| BusRegMuTensor3
| BusRegBianchiAlarm
| BusRegPtNextId
| BusRegPtSize
| BusRegLoadInstrAddr
| BusRegLoadInstrData
| BusRegLoadInstrKick
| BusRegSetLogicRespValid
| BusRegSetLogicRespError
| BusRegSetLogicRespValue
| BusRegSetActiveModule
| BusRegSetTrapVector

val decodeBusReg : int -> busReg option

val busRegReadable : busReg -> bool

val busRegWritable : busReg -> bool

type busCoreView = { view_pc : int; view_mu : int; view_err : bool;
                     view_halted : bool; view_partition_ops : int;
                     view_mdl_ops : int; view_info_gain : int;
                     view_error_code : int; view_mstatus : int;
                     view_mcycle_lo : int; view_mcycle_hi : int;
                     view_minstret_lo : int; view_minstret_hi : int;
                     view_logic_acc : int; view_logic_req_valid : bool;
                     view_logic_req_opcode : int;
                     view_logic_req_payload : int; view_mu_tensor0 : 
                     int; view_mu_tensor1 : int; view_mu_tensor2 : int;
                     view_mu_tensor3 : int; view_bianchi_alarm : bool;
                     view_pt_next_id : int; view_pt_size : (int -> int) }

val bool_to_nat : bool -> int

val busRegReadValue : busCoreView -> busReg -> int option

val busRead : busCoreView -> int -> int option

type busShadowRegs = { sh_load_instr_addr : int; sh_load_instr_data : 
                       int; sh_load_instr_kick : bool;
                       sh_logic_resp_valid : bool;
                       sh_logic_resp_error : bool; sh_logic_resp_value : 
                       int; sh_active_module : int; sh_trap_vector : 
                       int }

type busWrapperState = { bw_core : kamiSnapshot; bw_shadow : busShadowRegs }

val busWriteShadow : busShadowRegs -> busReg -> int -> busShadowRegs

val busWrite : busWrapperState -> int -> int -> busWrapperState

val coreViewOfSnapshot : kamiSnapshot -> busCoreView

type busOp =
| BusOpRead of int
| BusOpWrite of int * int

val bus_step : busWrapperState -> busOp -> busWrapperState

val pnew_chain : int -> vMState -> int list -> int -> vMState


val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

val add : int -> int -> int

val mul : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val eqb : int -> int -> bool

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val modulo : int -> int -> int
 end

val in_dec : ('a1 -> 'a1 -> bool) -> 'a1 -> 'a1 list -> bool

val nth : int -> 'a1 list -> 'a1 -> 'a1

val rev : 'a1 list -> 'a1 list

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val forallb : ('a1 -> bool) -> 'a1 list -> bool

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

val firstn : int -> 'a1 list -> 'a1 list

val skipn : int -> 'a1 list -> 'a1 list

val nodup : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list

val repeat : 'a1 -> int -> 'a1 list

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val pred_N : positive -> n

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val eqb : positive -> positive -> bool

  val coq_Nsucc_double : n -> n

  val coq_Ndouble : n -> n

  val coq_lor : positive -> positive -> positive

  val coq_land : positive -> positive -> n

  val coq_lxor : positive -> positive -> n

  val shiftl : positive -> n -> positive

  val testbit : positive -> n -> bool

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> int

  val of_succ_nat : int -> positive
 end

module N :
 sig
  val pred : n -> n

  val add : n -> n -> n

  val mul : n -> n -> n

  val div2 : n -> n

  val coq_lor : n -> n -> n

  val coq_land : n -> n -> n

  val coq_lxor : n -> n -> n

  val shiftl : n -> n -> n

  val shiftr : n -> n -> n

  val testbit : n -> n -> bool

  val to_nat : n -> int

  val of_nat : int -> n

  val ones : n -> n
 end

val zero : char

val one : char

val shift : bool -> char -> char

val ascii_of_pos : positive -> char

val ascii_of_N : n -> char

val ascii_of_nat : int -> char

val n_of_digits : bool list -> n

val n_of_ascii : char -> n

val nat_of_ascii : char -> int

module Z :
 sig
  val opp : z -> z

  val compare : z -> z -> comparison

  val ltb : z -> z -> bool

  val gtb : z -> z -> bool

  val eqb : z -> z -> bool

  val abs : z -> z

  val to_nat : z -> int

  val of_nat : int -> z
 end

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

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

  val parse_int : char list -> z option

  val parse_nat : char list -> int option

  type dimacs_cnf = { cnf_num_vars : int; cnf_clauses : z list list }

  val cnf_num_vars : dimacs_cnf -> int

  val cnf_clauses : dimacs_cnf -> z list list

  val take_until_zero : z list -> z list

  val parse_clause_tokens : char list list -> z list option

  val parse_dimacs : char list -> dimacs_cnf option

  val lookup_bool : int -> (int*bool) list -> bool option

  val insert_bool : int -> bool -> (int*bool) list -> (int*bool) list

  val remove_prefix_v : char list -> char list

  val split_on_eq_aux : char list -> char list -> (char list*char list) option

  val split_on_eq : char list -> (char list*char list) option

  val value_is_false : char list -> bool

  val parse_assignment_token : char list -> (int*bool) option

  val parse_assignment : char list -> (int*bool) list option

  val clause_satisfied : (int*bool) list -> z list -> bool

  val check_model : char list -> char list -> bool

  val assoc_remove : int -> (int*z list) list -> (int*z list) list

  val db_clauses : (int*z list) list -> z list list

  val eval_clause : (int*bool) list -> z list -> bool*z list

  val unit_conflict_fuel :
    int -> int -> z list list -> (int*bool) list -> z list -> bool

  val unit_conflict : int -> z list list -> z list -> bool

  val verify_rup_clause : int -> (int*z list) list -> z list -> bool

  type lrat_step = { lrat_id : int; lrat_clause : z list;
                     lrat_deletions : int list; lrat_is_delete : bool }

  val lrat_id : lrat_step -> int

  val lrat_clause : lrat_step -> z list

  val lrat_deletions : lrat_step -> int list

  val lrat_is_delete : lrat_step -> bool

  val parse_nat_list : char list list -> int list option

  val parse_z_list : char list list -> z list option

  val drop_until_zero : char list list -> char list list

  val parse_lrat_line : char list -> lrat_step option

  val build_initial_db : z list list -> int -> (int*z list) list

  val apply_deletions : (int*z list) list -> int list -> (int*z list) list

  val check_lrat_lines :
    int -> char list list -> (int*z list) list -> bool -> bool

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

type partitionGraph = { pg_next_id : moduleID;
                        pg_modules : (moduleID*moduleState) list }

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

val graph_update_module_tensor :
  partitionGraph -> moduleID -> int -> int -> partitionGraph

val graph_record_discovery :
  partitionGraph -> moduleID -> vMAxiom list -> partitionGraph

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

val word32_mask : n

val word32 : int -> int

val word32_xor : int -> int -> int

val word32_add : int -> int -> int

val word32_sub : int -> int -> int

val word32_popcount : int -> int

val word32_and : int -> int -> int

val word32_or : int -> int -> int

val word32_shl : int -> int -> int

val word32_shr : int -> int -> int

val word32_mul : int -> int -> int

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

val graph_pnew : partitionGraph -> int list -> partitionGraph*moduleID

val partition_valid : int list -> int list -> int list -> bool

val graph_psplit :
  partitionGraph -> moduleID -> int list -> int list ->
  ((partitionGraph*moduleID)*moduleID) option

val graph_pmerge :
  partitionGraph -> moduleID -> moduleID -> (partitionGraph*moduleID) option

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

val instruction_cost : vm_instruction -> int

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

val pnew_chain : int -> vMState -> int list -> int -> vMState

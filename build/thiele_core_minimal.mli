
val negb : bool -> bool

val fst : ('a1*'a2) -> 'a1

val snd : ('a1*'a2) -> 'a2

val length : 'a1 list -> int

val app : 'a1 list -> 'a1 list -> 'a1 list

type comparison =
| Eq
| Lt
| Gt

val add : int -> int -> int

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : int -> int -> int

  val mul : int -> int -> int

  val sub : int -> int -> int

  val ltb : int -> int -> bool

  val divmod : int -> int -> int -> int -> int*int

  val modulo : int -> int -> int
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
  val opp : int -> int

  val compare : int -> int -> comparison

  val ltb : int -> int -> bool

  val gtb : int -> int -> bool

  val eqb : int -> int -> bool

  val abs : int -> int

  val to_nat : int -> int

  val of_nat : int -> int
 end

val eqb0 : char list -> char list -> bool

val append : char list -> char list -> char list

val list_ascii_of_string : char list -> char list

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

val rEG_COUNT : int

val mEM_SIZE : int

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
                 vm_mu : int; vm_mu_tensor : int list; vm_err : bool }

val word32_mask : int

val word32 : int -> int

val word32_xor : int -> int -> int

val word32_add : int -> int -> int

val word32_sub : int -> int -> int

val word32_popcount : int -> int

val reg_index : int -> int

val mem_index : int -> int

val read_reg : vMState -> int -> int

val write_reg : vMState -> int -> int -> int list

val read_mem : vMState -> int -> int

val write_mem : vMState -> int -> int -> int list

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
  | Coq_instr_load_imm of int * int * int
  | Coq_instr_load of int * int * int
  | Coq_instr_store of int * int * int
  | Coq_instr_add of int * int * int * int
  | Coq_instr_sub of int * int * int * int
  | Coq_instr_jump of int * int
  | Coq_instr_jnez of int * int * int
  | Coq_instr_call of int * int
  | Coq_instr_ret of int
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

  val list_update_at : int list -> int -> int -> int list

  val vm_mu_tensor_add_at : vMState -> int -> int -> int list

  val advance_state :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> bool -> vMState

  val advance_state_reveal :
    vMState -> vm_instruction -> int -> int -> partitionGraph -> cSRState ->
    bool -> vMState

  val advance_state_rm :
    vMState -> vm_instruction -> partitionGraph -> cSRState -> int list ->
    int list -> bool -> vMState

  val jump_state : vMState -> vm_instruction -> int -> vMState

  val jump_state_rm :
    vMState -> vm_instruction -> int -> int list -> int list -> vMState
 end

val vm_apply : vMState -> VMStep.vm_instruction -> vMState

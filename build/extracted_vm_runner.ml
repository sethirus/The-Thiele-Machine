(*
  Minimal runner for the Coq-extracted VM semantics in build/thiele_core.ml.

  Input format (whitespace-separated):
    - Optional first line: FUEL <int>
    - Then one instruction per line:
        PNEW   {0,1,2} <cost>
        PSPLIT <mid> {0,2} {1,3} <cost>
        PMERGE <m1> <m2> <cost>
        MDLACC <mid> <cost>
        PDISCOVER <mid> {axiom1,axiom2,...} <cost>
        ORACLE_HALTS <payload_token> <cost>
        HALT   <cost>

  Output: a single JSON object on stdout describing the final vMState.
*)

open Printf

(* build/thiele_core.ml compiles as module [Thiele_core]. *)
open Thiele_core

(* Compatibility shim for older OCaml versions *)
let list_nth_opt lst n =
  try Some (List.nth lst n)
  with _ -> None

let trim (s : string) : string =
  let is_space = function ' ' | '\n' | '\r' | '\t' -> true | _ -> false in
  let len = String.length s in
  let rec left i = if i >= len then len else if is_space s.[i] then left (i + 1) else i in
  let rec right i = if i < 0 then -1 else if is_space s.[i] then right (i - 1) else i in
  let l = left 0 in
  let r = right (len - 1) in
  if r < l then "" else String.sub s l (r - l + 1)

let split_ws (s : string) : string list =
  let rec go i acc =
    if i >= String.length s then List.rev acc
    else if s.[i] = ' ' || s.[i] = '\t' then go (i + 1) acc
    else
      let j = ref i in
      while !j < String.length s && s.[!j] <> ' ' && s.[!j] <> '\t' do
        incr j
      done;
      let tok = String.sub s i (!j - i) in
      go !j (tok :: acc)
  in
  go 0 []

let safe_int (s : string) : int =
  try int_of_string s
  with _ ->
    try Int64.to_int (Int64.of_string s)
    with _ -> failwith ("invalid int: " ^ s)

let char_list_of_string (s : string) : char list =
  List.init (String.length s) (String.get s)

(* Decode the underscore-encoded DIMACS formula format used by the Python API.
   Encoding convention (from thielecpu/vm.py and tests):
     '__'  →  '\n'   (double underscore encodes newline between DIMACS lines)
     '_'   →  ' '    (single underscore encodes space between tokens)
   Must process '__' before '_' to avoid double-decoding. *)
let decode_formula (s : string) : string =
  let buf = Buffer.create (String.length s) in
  let len = String.length s in
  let i = ref 0 in
  while !i < len do
    if !i + 1 < len && s.[!i] = '_' && s.[!i + 1] = '_' then begin
      Buffer.add_char buf '\n';
      i := !i + 2
    end else if s.[!i] = '_' then begin
      Buffer.add_char buf ' ';
      i := !i + 1
    end else begin
      Buffer.add_char buf s.[!i];
      i := !i + 1
    end
  done;
  Buffer.contents buf

let parse_region (tok : string) : int list =
  let t = trim tok in
  let len = String.length t in
  if len < 2 || t.[0] <> '{' || t.[len - 1] <> '}' then
    failwith ("invalid region token (expected {...}): " ^ tok);
  let inner = String.sub t 1 (len - 2) |> trim in
  if inner = "" then []
  else
    inner
    |> String.split_on_char ','
    |> List.map trim
    |> List.filter (fun x -> x <> "")
    |> List.map safe_int

let parse_brace_list (tok : string) : string list =
  let t = trim tok in
  let len = String.length t in
  if len < 2 || t.[0] <> '{' || t.[len - 1] <> '}' then
    failwith ("invalid list token (expected {...}): " ^ tok);
  let inner = String.sub t 1 (len - 2) |> trim in
  if inner = "" then []
  else
    inner
    |> String.split_on_char ','
    |> List.map trim
    |> List.filter (fun x -> x <> "")

let json_escape (s : string) : string =
  (* Minimal JSON string escape; we only really need quotes/backslashes here. *)
  let b = Buffer.create (String.length s + 8) in
  String.iter
    (fun ch ->
      match ch with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | _ -> Buffer.add_char b ch)
    s;
  Buffer.contents b

let json_bool (b : bool) : string = if b then "true" else "false"

(* State integrity MAC — FNV-1a 64-bit with embedded salt.
   Prevents casual JSON tampering of vm_mu and other fields.
   NOT cryptographically secure; tamper-detection only. *)
let state_integrity_salt = "thiele_mu_guard_v1_2026"

let compute_state_mac (json_body : string) : string =
  let s = state_integrity_salt ^ json_body in
  let h = ref 0xcbf29ce484222325L in (* FNV-1a 64-bit offset basis *)
  let prime = 0x100000001b3L in       (* FNV-1a 64-bit prime *)
  String.iter (fun c ->
    h := Int64.logxor !h (Int64.of_int (Char.code c));
    h := Int64.mul !h prime
  ) s;
  Printf.sprintf "%016Lx" !h

(* Convert int to unsigned 64-bit string representation.
   Negative ints represent values >= 2^62 via two's complement:
   Int64.of_int sign-extends, so -1 -> 0xFFFFFFFFFFFFFFFF. *)
let int_to_uint64_string (x : int) : string =
  if x >= 0 then string_of_int x
  else Printf.sprintf "%Lu" (Int64.of_int x)

let json_int_list (xs : int list) : string =
  let rec go = function
    | [] -> ""
    | [ x ] -> string_of_int x
    | x :: rest -> string_of_int x ^ "," ^ go rest
  in
  "[" ^ go xs ^ "]"

(* Word-sized list serialization: uses unsigned 64-bit representation
   for values that may have bit 62+ set (negative OCaml ints). *)
let json_word_list (xs : int list) : string =
  "[" ^ (String.concat "," (List.map int_to_uint64_string xs)) ^ "]"

(* Sparse memory: truncate trailing zeros before serializing.
   Uses unsigned 64-bit representation for word-sized memory values. *)
let json_sparse_mem (xs : int list) : string =
  let arr = Array.of_list xs in
  let last = ref (-1) in
  Array.iteri (fun i v -> if v <> 0 then last := i) arr;
  if !last < 0 then "[]"
  else
    let rec go i acc =
      if i < 0 then acc
      else go (i-1) (int_to_uint64_string arr.(i) ^ (if acc = "" then "" else "," ^ acc))
    in
    "[" ^ go !last "" ^ "]"

let read_all_lines (path : string) : string list =
  let ic = open_in path in
  let rec loop acc =
    match input_line ic with
    | line -> loop (line :: acc)
    | exception End_of_file ->
        close_in ic;
        List.rev acc
  in
  loop []

let string_of_char_list (cl : char list) : string =
  String.init (List.length cl) (fun i -> List.nth cl i)

let serialize_state_json (s : vMState) : string =
  let modules_json =
    s.vm_graph.pg_modules
    |> List.map (fun (mid, m) ->
           let axiom_strings =
             m.module_axioms
             |> List.map (fun ax -> sprintf "\"%s\"" (json_escape (string_of_char_list ax)))
             |> String.concat ","
           in
           sprintf
             "{\"id\":%d,\"region\":%s,\"axioms\":%d,\"axiom_strings\":[%s],\"mu_tensor\":%s}"
             mid
             (json_int_list m.module_region)
             (List.length m.module_axioms)
             axiom_strings
             (json_word_list m.module_mu_tensor))
    |> String.concat ","
  in
  (* "csr_err_code" is emitted at top level (distinct key) so --resume can parse it
     unambiguously, since "err" appears both as a boolean at top level and as an
     integer inside "csrs". *)
  let json_body =
  sprintf
    "{\"pc\":%d,\"mu\":%d,\"err\":%s,\"certified\":%s,\"csr_err_code\":%d,\"logic_acc\":%d,\"mstatus\":%d,\"regs\":%s,\"mem\":%s,\"mu_tensor\":%s,\"witness\":[%d,%d,%d,%d,%d,%d,%d,%d],\"csrs\":{\"cert_addr\":%d,\"status\":%d,\"err\":%d,\"heap_base\":%d},\"graph\":{\"next_id\":%d,\"modules\":[%s]}}"
    s.vm_pc
    s.vm_mu
    (json_bool s.vm_err)
    (json_bool s.vm_certified)
    s.vm_csrs.csr_err
    s.vm_logic_acc
    s.vm_mstatus
    (json_word_list s.vm_regs)
    (json_sparse_mem s.vm_mem)
    (json_word_list s.vm_mu_tensor)
    s.vm_witness.wc_same_00 s.vm_witness.wc_diff_00
    s.vm_witness.wc_same_01 s.vm_witness.wc_diff_01
    s.vm_witness.wc_same_10 s.vm_witness.wc_diff_10
    s.vm_witness.wc_same_11 s.vm_witness.wc_diff_11
    s.vm_csrs.csr_cert_addr
    s.vm_csrs.csr_status
    s.vm_csrs.csr_err
    s.vm_csrs.csr_heap_base
    s.vm_graph.pg_next_id
    modules_json
  in
  (* Append state integrity MAC *)
  let mac = compute_state_mac json_body in
  let len = String.length json_body in
  String.sub json_body 0 (len - 1) ^ sprintf ",\"_mac\":\"%s\"}" mac

let checkpoint_dir : string =
  match Sys.getenv_opt "THIELE_CHECKPOINT_DIR" with
  | Some d -> d
  | None -> Filename.get_temp_dir_name ()

let write_checkpoint (label : string) (s : vMState) : unit =
  let filename = Filename.concat checkpoint_dir (label ^ ".json") in
  let oc = open_out filename in
  output_string oc (serialize_state_json s);
  output_char oc '\n';
  close_out oc;
  eprintf "[CHECKPOINT] Saved state to %s (pc=%d mu=%d)\n%!" filename s.vm_pc s.vm_mu

let list_set_mod (size : int) (xs : int list) (idx : int) (v : int) : int list =
  let idx = if size <= 0 then 0 else ((idx mod size) + size) mod size in
  let rec go i = function
    | [] -> []
    | x :: rest ->
        if i = idx then v :: rest else x :: go (i + 1) rest
  in
  go 0 xs

(* Memory string helpers — mirror the Coq write_string_to_mem encoding.
   Layout: mem[base] = len (bytes); mem[base+1..] = packed little-endian 4-byte words. *)
let bytes_to_word_4 b0 b1 b2 b3 =
  b0 lor (b1 lsl 8) lor (b2 lsl 16) lor (b3 lsl 24)

let write_string_to_mem_init (mem : int list) (sz : int) (base : int) (str : string) : int list =
  let len = String.length str in
  let mem1 = list_set_mod sz mem base len in
  let n_words = (len + 3) / 4 in
  let rec go m i =
    if i >= n_words then m
    else
      let byte j = if i * 4 + j < len then Char.code str.[i * 4 + j] else 0 in
      let w = bytes_to_word_4 (byte 0) (byte 1) (byte 2) (byte 3) in
      go (list_set_mod sz m (base + 1 + i) w) (i + 1)
  in
  go mem1 0

(* A program element is either a real VM instruction or a harness directive. *)
type program_element =
  | Instr of VMStep.vm_instruction
  | Checkpoint of string
  | WritePort of string * int    (* channel_name, src_reg *)
  | ReadPort of int * string     (* dst_reg, channel_name *)

let parse_program (lines : string list) : int * int list * int list * int * int list * (int * int) list * (int * int) list * program_element list =
    let fuel = ref 256 in
    let mem_size = ref 65536 in
    let rec make_list n acc =
      if n <= 0 then acc else make_list (n - 1) (0 :: acc)
    in
    let init_regs = ref (make_list 32 []) in
    let init_mem = ref None in  (* deferred until mem_size is known *)
    let init_logic_acc = ref 0 in
    let init_tensor = ref (make_list 16 []) in
    (* Track explicit INIT_MEM/INIT_MEM_STR/INIT_REG patches for --resume overlay. *)
    let mem_patches  : (int * int) list ref = ref [] in
    let reg_patches  : (int * int) list ref = ref [] in

    let parse_line (line : string) : program_element option =
    let t = trim line in
    if t = "" || t.[0] = '#' || t.[0] = ';' then None
    else
      let toks = split_ws t in
      match toks with
      | [ "FUEL"; n ] ->
        fuel := safe_int n;
        None
      | [ "MEM_SIZE"; n ] ->
        mem_size := safe_int n;
        None
      | [ "INIT_REG"; r; v ] ->
        let ri = safe_int r and vi = safe_int v in
        init_regs := list_set_mod 32 !init_regs ri vi;
        reg_patches := (ri, vi) :: !reg_patches;
        None
      | [ "INIT_MEM"; a; v ] ->
        let ai = safe_int a and vi = safe_int v in
        let m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
        init_mem := Some (list_set_mod !mem_size m ai vi);
        mem_patches := (ai, vi) :: !mem_patches;
        None
      | [ "INIT_MEM_STR"; a; encoded ] ->
        (* Write underscore-encoded string to initial memory at addr a.
           Encoding: '_' -> ' ', '__' -> '\n' (same as decode_formula).
           mem[a] = len; mem[a+1..] = packed little-endian 4-byte words. *)
        let str = decode_formula encoded in
        let base = safe_int a in
        let len = String.length str in
        let m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
        let m' = write_string_to_mem_init m !mem_size base str in
        init_mem := Some m';
        (* Record all non-trivial patches: length + n_words entries *)
        mem_patches := (base, len) :: !mem_patches;
        let n_words = (len + 3) / 4 in
        for i = 0 to n_words - 1 do
          let byte j = if i * 4 + j < len then Char.code str.[i * 4 + j] else 0 in
          let w = bytes_to_word_4 (byte 0) (byte 1) (byte 2) (byte 3) in
          mem_patches := (base + 1 + i, w) :: !mem_patches
        done;
        None
      | [ "INIT_MEM_STR"; a ] ->
        (* Empty string: just record length=0 at addr a (no word patches needed) *)
        let base = safe_int a in
        let m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
        init_mem := Some (list_set_mod !mem_size m base 0);
        mem_patches := (base, 0) :: !mem_patches;
        None
      | [ "INIT_LOGIC_ACC"; v ] ->
        init_logic_acc := safe_int v;
        None
      | [ "INIT_TENSOR"; idx; v ] ->
        init_tensor := list_set_mod 16 !init_tensor (safe_int idx) (safe_int v);
        None
      | "INIT_PT" :: _ -> None    (* partition table: handled via graph operations *)
      | "INIT_ACTIVE_MODULE" :: _ -> None  (* hardware-only state *)
      (* Phase 2: full Coq instructions (token-count distinguishes from Phase 1 harness) *)
      | [ "CHECKPOINT"; label; cost ] ->
        Some (Instr (VMStep.Coq_instr_checkpoint (char_list_of_string label, safe_int cost)))
      | [ "WRITE_PORT"; ch_idx; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_write_port (safe_int ch_idx, safe_int src, safe_int cost)))
      | [ "READ_PORT"; dst; ch_idx; value; bits; cost ] ->
        Some (Instr (VMStep.Coq_instr_read_port
          (safe_int dst, safe_int ch_idx, safe_int value, safe_int bits, safe_int cost)))
      | [ "HEAP_LOAD"; dst; addr; cost ] ->
        Some (Instr (VMStep.Coq_instr_heap_load (safe_int dst, safe_int addr, safe_int cost)))
      | [ "HEAP_STORE"; addr; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_heap_store (safe_int addr, safe_int src, safe_int cost)))
      (* Phase 1: harness-level directives (no Coq state change) *)
      | [ "CHECKPOINT"; label ] ->
        Some (Checkpoint label)
      | "CHECKPOINT" :: _ ->
        Some (Checkpoint "checkpoint")
      | [ "WRITE_PORT"; channel; src_reg ] ->
        Some (WritePort (channel, safe_int src_reg))
      | [ "READ_PORT"; dst_reg; channel ] ->
        Some (ReadPort (safe_int dst_reg, channel))
      | [ "PNEW"; region_tok; cost ] ->
          Some (Instr (VMStep.Coq_instr_pnew (parse_region region_tok, safe_int cost)))
      | [ "PSPLIT"; mid; left_tok; right_tok; cost ] ->
          Some (Instr (VMStep.Coq_instr_psplit
               ( safe_int mid, parse_region left_tok,
                 parse_region right_tok, safe_int cost )))
      | [ "PMERGE"; m1; m2; cost ] ->
          Some (Instr (VMStep.Coq_instr_pmerge (safe_int m1, safe_int m2, safe_int cost)))
      | [ "MDLACC"; mid; cost ] ->
          Some (Instr (VMStep.Coq_instr_mdlacc (safe_int mid, safe_int cost)))
      | [ "PDISCOVER"; mid; evidence_tok; cost ] ->
          let evidence = parse_brace_list evidence_tok |> List.map char_list_of_string in
          Some (Instr (VMStep.Coq_instr_pdiscover (safe_int mid, evidence, safe_int cost)))
      | [ "XFER"; dst; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_xfer (safe_int dst, safe_int src, safe_int cost)))
      | [ "LOAD_IMM"; dst; imm; cost ] ->
        Some (Instr (VMStep.Coq_instr_load_imm (safe_int dst, safe_int imm, safe_int cost)))
      | [ "LOAD"; dst; addr; cost ] ->
        Some (Instr (VMStep.Coq_instr_load (safe_int dst, safe_int addr, safe_int cost)))
      | [ "STORE"; addr; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_store (safe_int addr, safe_int src, safe_int cost)))
      | [ "ADD"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_add (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "SUB"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_sub (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "JUMP"; target; cost ] ->
        Some (Instr (VMStep.Coq_instr_jump (safe_int target, safe_int cost)))
      | [ "JNEZ"; rs; target; cost ] ->
        Some (Instr (VMStep.Coq_instr_jnez (safe_int rs, safe_int target, safe_int cost)))
      | [ "CALL"; target; cost ] ->
        Some (Instr (VMStep.Coq_instr_call (safe_int target, safe_int cost)))
      | [ "RET"; cost ] ->
        Some (Instr (VMStep.Coq_instr_ret (safe_int cost)))
      | [ "XOR_LOAD"; dst; addr; cost ] ->
        Some (Instr (VMStep.Coq_instr_xor_load (safe_int dst, safe_int addr, safe_int cost)))
      | [ "XOR_ADD"; dst; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_xor_add (safe_int dst, safe_int src, safe_int cost)))
      | [ "XOR_SWAP"; a; b; cost ] ->
        Some (Instr (VMStep.Coq_instr_xor_swap (safe_int a, safe_int b, safe_int cost)))
      | [ "XOR_RANK"; dst; src; cost ] ->
        Some (Instr (VMStep.Coq_instr_xor_rank (safe_int dst, safe_int src, safe_int cost)))
      | [ "CHSH_TRIAL"; x; y; a; b; cost ] ->
        Some (Instr (VMStep.Coq_instr_chsh_trial
             ( safe_int x, safe_int y, safe_int a, safe_int b, safe_int cost )))
      | [ "REVEAL"; ti; tj; bits ] ->
        let flat_idx = (safe_int ti) * 4 + (safe_int tj) in
        let delta = safe_int bits in
        Some (Instr (VMStep.Coq_instr_reveal (flat_idx, delta, [], delta)))
      | [ "REVEAL"; ti; tj; bits; cert ] ->
        let flat_idx = (safe_int ti) * 4 + (safe_int tj) in
        let delta = safe_int bits in
        Some (Instr (VMStep.Coq_instr_reveal (flat_idx, delta, char_list_of_string cert, delta)))
      | [ "LASSERT"; freg; creg; kind; flen; cost ] ->
        (* On-chip model: freg/creg are register indices pointing to formula/cert in vm_mem.
           kind=1 → SAT mode (check_model); kind=0 → UNSAT mode (check_lrat).
           flen = formula length in words; cost = mu_delta. *)
        Some (Instr (VMStep.Coq_instr_lassert (safe_int freg, safe_int creg,
          safe_int kind = 1, safe_int flen, safe_int cost)))
      | [ "LJOIN"; c1reg; c2reg; cost ] ->
        (* On-chip model: c1reg/c2reg are register indices pointing to cert strings in vm_mem. *)
        Some (Instr (VMStep.Coq_instr_ljoin (safe_int c1reg, safe_int c2reg, safe_int cost)))
      | [ "EMIT"; mid; bits; cost ] ->
        Some (Instr (VMStep.Coq_instr_emit (safe_int mid, char_list_of_string bits, safe_int cost)))
      | [ "ORACLE_HALTS"; payload; cost ] ->
        Some (Instr (VMStep.Coq_instr_oracle_halts (char_list_of_string payload, safe_int cost)))
      | [ "HALT"; cost ] -> Some (Instr (VMStep.Coq_instr_halt (safe_int cost)))
      | [ "CERTIFY"; cost ] -> Some (Instr (VMStep.Coq_instr_certify (safe_int cost)))
      | [ "CERTIFY"; _; _; cost ] -> Some (Instr (VMStep.Coq_instr_certify (safe_int cost)))
      | [ "AND"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_and (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "OR"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_or (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "SHL"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_shl (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "SHR"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_shr (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "MUL"; dst; src1; src2; cost ] ->
        Some (Instr (VMStep.Coq_instr_mul (safe_int dst, safe_int src1, safe_int src2, safe_int cost)))
      | [ "LUI"; dst; imm; cost ] ->
        Some (Instr (VMStep.Coq_instr_lui (safe_int dst, safe_int imm, safe_int cost)))
      | [ "TENSOR_SET"; mid; i; j; value; mu_delta ] ->
        Some (Instr (VMStep.Coq_instr_tensor_set (safe_int mid, safe_int i, safe_int j, safe_int value, safe_int mu_delta)))
      | [ "TENSOR_GET"; dst; mid; i; j; mu_delta ] ->
        Some (Instr (VMStep.Coq_instr_tensor_get (safe_int dst, safe_int mid, safe_int i, safe_int j, safe_int mu_delta)))
      (* Phase 5: categorical morphism opcodes (0x27–0x2D) *)
      | [ "MORPH"; dst; src_mod; dst_mod; coupling_idx; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph (safe_int dst, safe_int src_mod, safe_int dst_mod, safe_int coupling_idx, safe_int cost)))
      | [ "COMPOSE"; dst; m1; m2; cost ] ->
        Some (Instr (VMStep.Coq_instr_compose (safe_int dst, safe_int m1, safe_int m2, safe_int cost)))
      | [ "MORPH_ID"; dst; module0; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph_id (safe_int dst, safe_int module0, safe_int cost)))
      | [ "MORPH_DELETE"; morph_id; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph_delete (safe_int morph_id, safe_int cost)))
      | [ "MORPH_ASSERT"; morph_id; property; cert; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph_assert (safe_int morph_id, char_list_of_string property, char_list_of_string cert, safe_int cost)))
      | [ "MORPH_TENSOR"; dst; f; g; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph_tensor (safe_int dst, safe_int f, safe_int g, safe_int cost)))
      | [ "MORPH_GET"; dst; morph_id; selector; cost ] ->
        Some (Instr (VMStep.Coq_instr_morph_get (safe_int dst, safe_int morph_id, safe_int selector, safe_int cost)))
      | _ -> failwith ("unrecognized instruction line: " ^ t)
  in
  let elements = lines |> List.filter_map parse_line in
  let init_m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
  (!fuel, !init_regs, init_m, !init_logic_acc, !init_tensor, !mem_patches, !reg_patches, elements)

let initial_state () : vMState =
  let rec make_list n acc =
    if n <=  0 then acc else make_list (n - 1) (0 :: acc)
  in
  {
    vm_graph = { pg_next_id = 1; pg_modules = []; pg_next_morph_id = 0; pg_morphisms = [] };
    vm_csrs = { csr_cert_addr = 0; csr_status = 0; csr_err = 0; csr_heap_base = 0 };
    vm_regs = make_list 32 [];
    vm_mem = make_list 65536 [];
    vm_pc = 0;
    vm_mu = 0;
    vm_mu_tensor = make_list 16 [];
    vm_err = false;
    vm_logic_acc = 0;
    vm_mstatus = 0;
    vm_witness = { wc_same_00 = 0; wc_diff_00 = 0;
                   wc_same_01 = 0; wc_diff_01 = 0;
                   wc_same_10 = 0; wc_diff_10 = 0;
                   wc_same_11 = 0; wc_diff_11 = 0 };
    vm_certified = false;
  }

(* Extract only the VM instructions from program elements (for NoFI check). *)
let extract_instructions (elements : program_element list) : VMStep.vm_instruction list =
  List.filter_map (function Instr i -> Some i | _ -> None) elements

(* I/O channel management for WRITE_PORT / READ_PORT (Philosophy B). *)
let output_channels : (string, out_channel) Hashtbl.t = Hashtbl.create 4
let input_channels : (string, in_channel) Hashtbl.t = Hashtbl.create 4

let get_output_channel (name : string) : out_channel =
  try Hashtbl.find output_channels name
  with Not_found ->
    let oc = match name with
      | "stdout" -> stdout
      | "stderr" -> stderr
      | path -> open_out_gen [Open_append; Open_creat; Open_wronly] 0o644 path
    in
    Hashtbl.add output_channels name oc;
    oc

let get_input_channel (name : string) : in_channel =
  try Hashtbl.find input_channels name
  with Not_found ->
    let ic = match name with
      | "stdin" -> stdin
      | path -> open_in path
    in
    Hashtbl.add input_channels name ic;
    ic

let read_next_int (ic : in_channel) : int =
  (* Read next whitespace-delimited integer from channel. *)
  let buf = Buffer.create 16 in
  let rec skip_ws () =
    let c = input_char ic in
    if c = ' ' || c = '\t' || c = '\n' || c = '\r' then skip_ws ()
    else Buffer.add_char buf c
  in
  let rec read_digits () =
    match input_char ic with
    | c when (c >= '0' && c <= '9') || c = '-' -> Buffer.add_char buf c; read_digits ()
    | _ -> ()
    | exception End_of_file -> ()
  in
  (try skip_ws (); read_digits () with End_of_file -> ());
  let s = Buffer.contents buf in
  if s = "" then 0 else int_of_string s

let close_all_channels () =
  Hashtbl.iter (fun name oc ->
    if name <> "stdout" && name <> "stderr" then
      (try close_out oc with _ -> ())) output_channels;
  Hashtbl.iter (fun name ic ->
    if name <> "stdin" then
      (try close_in ic with _ -> ())) input_channels

(* Tail-recursive VM execution loop that handles instructions and harness directives.
   The extracted run_vm is NOT tail-recursive, causing stack overflow
   even with modest fuel values (256). This iterative version is safe. *)
let run_vm_with_checkpoints (max_fuel : int) (prog : program_element list) (initial : vMState) : vMState =
  let rec loop fuel s =
    if fuel <= 0 || s.vm_err then s
    else
      match list_nth_opt prog s.vm_pc with
      | None -> s  (* PC out of bounds, halt *)
      | Some (Checkpoint label) ->
          write_checkpoint label s;
          let s' = { s with vm_pc = s.vm_pc + 1 } in
          loop fuel s'  (* checkpoints don't consume fuel *)
      | Some (WritePort (channel, src_reg)) ->
          let value = List.nth s.vm_regs (src_reg mod 32) in
          let oc = get_output_channel channel in
          fprintf oc "%d\n" value;
          flush oc;
          let s' = { s with vm_pc = s.vm_pc + 1 } in
          loop fuel s'  (* directives don't consume fuel *)
      | Some (ReadPort (dst_reg, channel)) ->
          let ic = get_input_channel channel in
          let value = read_next_int ic in
          let s' = { s with
            vm_pc = s.vm_pc + 1;
            vm_regs = list_set_mod 32 s.vm_regs (dst_reg mod 32) value
          } in
          loop fuel s'  (* directives don't consume fuel *)
      | Some (Instr instr) ->
          (* HALT: stop execution (Coq advance_state just advances PC) *)
          (match instr with
           | VMStep.Coq_instr_halt _ ->
               let s' = vm_apply_nofi s instr in
               { s' with vm_csrs = { s'.vm_csrs with csr_status = 2 } }
           | _ ->
               let s' = vm_apply_nofi s instr in
               (* Side-effect: Coq instr_checkpoint serializes state to <label>.json *)
               (match instr with
                | VMStep.Coq_instr_checkpoint (label_chars, _) ->
                    write_checkpoint (string_of_char_list label_chars) s'
                | _ -> ());
               loop (fuel - 1) s')
  in
  loop max_fuel initial

let nofi_violation_state (s : vMState) : vMState =
  {
    s with
    vm_err = true;
    vm_csrs = { s.vm_csrs with csr_err = 1 };
  }

(* Minimal JSON parser for --resume: extract integer fields from checkpoint JSON.
   This is intentionally minimal — it parses the output of serialize_state_json. *)
(* Parse int, handling large unsigned 64-bit values that overflow OCaml int.
   Values > 2^62-1 are stored as negative ints via Int64 sign truncation. *)
let safe_int_of_string (s : string) : int =
  try int_of_string s
  with Failure _ ->
    try Int64.to_int (Int64.of_string s) with _ -> 0

let parse_json_int (json : string) (key : string) : int =
  let pattern = sprintf "\"%s\":" key in
  try
    let i = Str.search_forward (Str.regexp_string pattern) json 0 in
    let start = i + String.length pattern in
    let s = String.sub json start (min 30 (String.length json - start)) in
    let s = trim s in
    (* Extract leading integer *)
    let j = ref 0 in
    let neg = !j < String.length s && s.[!j] = '-' in
    if neg then incr j;
    while !j < String.length s && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
    let ns = String.sub s (if neg then 0 else 0) !j in
    safe_int_of_string ns
  with _ -> 0

let parse_json_bool (json : string) (key : string) : bool =
  let pattern = sprintf "\"%s\":" key in
  try
    let i = Str.search_forward (Str.regexp_string pattern) json 0 in
    let start = i + String.length pattern in
    let s = trim (String.sub json start (min 10 (String.length json - start))) in
    s.[0] = 't'
  with _ -> false

let parse_json_int_array (json : string) (key : string) : int list =
  let pattern = sprintf "\"%s\":[" key in
  try
    let i = Str.search_forward (Str.regexp_string pattern) json 0 in
    let start = i + String.length pattern in
    let j = ref start in
    while !j < String.length json && json.[!j] <> ']' do incr j done;
    let inner = String.sub json start (!j - start) in
    if trim inner = "" then []
    else
      inner
      |> String.split_on_char ','
      |> List.map trim
      |> List.filter (fun x -> x <> "")
      |> List.map safe_int_of_string
  with _ -> []

(* Parse all module entries from "modules":[{...},{...}] in the JSON.
   Returns a list of (moduleID, moduleState) pairs. *)
let parse_modules_from_json (json : string) : (int * moduleState) list =
  try
    let pattern = "\"modules\":[" in
    let plen = String.length pattern in
    let start_idx = Str.search_forward (Str.regexp_string pattern) json 0 in
    let arr_start = start_idx + plen in
    (* Find end of modules array, counting [ ] nesting *)
    let depth = ref 1 in
    let j = ref arr_start in
    let jlen = String.length json in
    while !j < jlen && !depth > 0 do
      if json.[!j] = '[' then incr depth
      else if json.[!j] = ']' then decr depth;
      if !depth > 0 then incr j
    done;
    let arr_content = String.sub json arr_start (!j - arr_start) in
    if trim arr_content = "" then []
    else begin
      let modules = ref [] in
      let i = ref 0 in
      let alen = String.length arr_content in
      while !i < alen do
        (* Skip whitespace/commas to next { *)
        while !i < alen && arr_content.[!i] <> '{' do incr i done;
        if !i < alen then begin
          let obj_start = !i in
          let obj_depth = ref 0 in
          (try
            while true do
              if arr_content.[!i] = '{' then incr obj_depth
              else if arr_content.[!i] = '}' then begin
                decr obj_depth;
                if !obj_depth = 0 then raise Exit
              end;
              incr i
            done
          with Exit -> ());
          let obj_json = String.sub arr_content obj_start (!i - obj_start + 1) in
          let mid = parse_json_int obj_json "id" in
          let region = parse_json_int_array obj_json "region" in
          (* Parse axiom_strings: extract quoted strings between "axiom_strings":[ and ] *)
          let axioms =
            try
              let ax_pattern = "\"axiom_strings\":[" in
              let ax_plen = String.length ax_pattern in
              let ax_si = Str.search_forward (Str.regexp_string ax_pattern) obj_json 0 in
              let ax_start = ax_si + ax_plen in
              let ax_j = ref ax_start in
              let obj_len = String.length obj_json in
              while !ax_j < obj_len && obj_json.[!ax_j] <> ']' do incr ax_j done;
              let ax_inner = String.sub obj_json ax_start (!ax_j - ax_start) in
              let ax_list = ref [] in
              let ai = ref 0 in
              let ailen = String.length ax_inner in
              while !ai < ailen do
                while !ai < ailen && ax_inner.[!ai] <> '"' do incr ai done;
                if !ai < ailen then begin
                  incr ai; (* skip opening quote *)
                  let buf = Buffer.create 16 in
                  let stop = ref false in
                  while !ai < ailen && not !stop do
                    (match ax_inner.[!ai] with
                    | '"' -> stop := true
                    | '\\' when !ai + 1 < ailen ->
                        incr ai; Buffer.add_char buf ax_inner.[!ai]; incr ai
                    | c -> Buffer.add_char buf c; incr ai)
                  done;
                  if !stop then incr ai; (* skip closing quote *)
                  ax_list := (char_list_of_string (Buffer.contents buf)) :: !ax_list
                end
              done;
              List.rev !ax_list
            with _ -> []
          in
          let mu_tensor = try parse_json_int_array obj_json "mu_tensor" with _ -> [] in
          let padded_tensor =
            let len = List.length mu_tensor in
            if len >= 16 then mu_tensor
            else mu_tensor @ (List.init (16 - len) (fun _ -> 0))
          in
          modules :=
            (mid, { module_region = region; module_axioms = axioms; module_mu_tensor = padded_tensor }) :: !modules;
          incr i (* move past } *)
        end
      done;
      List.rev !modules
    end
  with _ -> []

let load_resume_state (path : string) : vMState =
  let ic = open_in path in
  let json = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let json = String.trim json in
  (* Verify state integrity MAC if present *)
  let mac_pattern = ",\"_mac\":\"" in
  (try
    let mac_start = Str.search_forward (Str.regexp_string mac_pattern) json 0 in
    let stored_mac_start = mac_start + String.length mac_pattern in
    let stored_mac_end = String.index_from json stored_mac_start '"' in
    let stored_mac = String.sub json stored_mac_start (stored_mac_end - stored_mac_start) in
    (* Reconstruct JSON body without MAC for verification *)
    let json_body = String.sub json 0 mac_start ^ "}" in
    let expected_mac = compute_state_mac json_body in
    if stored_mac <> expected_mac then (
      eprintf "[ERROR] State MAC verification failed — state may have been tampered with.\n%!";
      eprintf "[ERROR] Expected: %s, got: %s\n%!" expected_mac stored_mac;
      exit 6
    )
  with Not_found ->
    eprintf "[WARN] No state MAC found. State integrity cannot be verified.\n%!"
  );
  let rec make_list n acc =
    if n <= 0 then acc else make_list (n - 1) (0 :: acc)
  in
  {
    vm_graph = {
      pg_next_id = parse_json_int json "next_id";
      pg_modules = parse_modules_from_json json;
      pg_next_morph_id = 0;
      pg_morphisms = [];
    };
    vm_csrs = {
      csr_cert_addr = parse_json_int json "cert_addr";
      csr_status    = parse_json_int json "status";
      (* "csr_err_code" is the unambiguous top-level key; "err" alone would
         collide with the top-level boolean vm_err field. *)
      csr_err       = parse_json_int json "csr_err_code";
      csr_heap_base = parse_json_int json "heap_base";
    };
    vm_regs = (let r = parse_json_int_array json "regs" in
               if r = [] then make_list 32 [] else r);
    vm_mem = (let m = parse_json_int_array json "mem" in
              let len = List.length m in
              if len >= 65536 then m else m @ make_list (65536 - len) []);
    vm_pc        = parse_json_int json "pc";
    vm_mu        = parse_json_int json "mu";
    vm_mu_tensor = (let t = parse_json_int_array json "mu_tensor" in
                    if t = [] then make_list 16 [] else t);
    vm_err       = parse_json_bool json "err";
    vm_logic_acc = parse_json_int json "logic_acc";
    vm_mstatus   = parse_json_int json "mstatus";
    vm_witness = (let w = parse_json_int_array json "witness" in
                  if List.length w >= 8 then
                    { wc_same_00 = List.nth w 0; wc_diff_00 = List.nth w 1;
                      wc_same_01 = List.nth w 2; wc_diff_01 = List.nth w 3;
                      wc_same_10 = List.nth w 4; wc_diff_10 = List.nth w 5;
                      wc_same_11 = List.nth w 6; wc_diff_11 = List.nth w 7 }
                  else
                    { wc_same_00 = 0; wc_diff_00 = 0;
                      wc_same_01 = 0; wc_diff_01 = 0;
                      wc_same_10 = 0; wc_diff_10 = 0;
                      wc_same_11 = 0; wc_diff_11 = 0 });
    vm_certified = (try parse_json_bool json "certified" with _ -> false);
  }

let () =
  try
    (* Parse arguments: <trace.txt> or --resume <state.json> <trace.txt> *)
    let argc = Array.length Sys.argv in
    let resume_path = ref None in
    let trace_path = ref "" in
    if argc = 2 then
      trace_path := Sys.argv.(1)
    else if argc = 4 && Sys.argv.(1) = "--resume" then (
      resume_path := Some Sys.argv.(2);
      trace_path := Sys.argv.(3))
    else (
      eprintf "usage: %s [--resume <state.json>] <trace.txt>\n" Sys.argv.(0);
      exit 2);
    eprintf "[DEBUG] Reading file: %s\n%!" !trace_path;
    let lines = read_all_lines !trace_path in
    eprintf "[DEBUG] Read %d lines\n%!" (List.length lines);
    let fuel, regs0, mem0, logic_acc0, tensor0, mem_patches, reg_patches, prog = parse_program lines in
    eprintf "[DEBUG] Parsed: fuel=%d, prog_len=%d\n%!" fuel (List.length prog);
    let s0 = match !resume_path with
      | Some path ->
        eprintf "[DEBUG] Resuming from %s\n%!" path;
        let base = load_resume_state path in
        (* Apply INIT_MEM/INIT_MEM_STR/INIT_REG overlays on top of resumed state. *)
        let m = List.fold_left
          (fun m (a, v) -> list_set_mod (List.length m) m a v)
          base.vm_mem mem_patches in
        let r = List.fold_left
          (fun r (i, v) -> list_set_mod 32 r i v)
          base.vm_regs reg_patches in
        { base with vm_mem = m; vm_regs = r }
      | None ->
        let s = initial_state () in
        { s with vm_regs = regs0; vm_mem = mem0;
                 vm_logic_acc = logic_acc0; vm_mu_tensor = tensor0 }
    in
    eprintf "[DEBUG] Initial PC=%d MU=%d\n%!" s0.vm_pc s0.vm_mu;
    eprintf "[DEBUG] Calling run_vm...\n%!";
    let instrs = extract_instructions prog in
    let final_state, exit_code =
      if VMStep.nofi_trace_cost_okb instrs then
        (run_vm_with_checkpoints fuel prog s0, 0)
      else
        (nofi_violation_state s0, 5)
    in
    eprintf "[DEBUG] Run completed: PC=%d MU=%d\n%!" final_state.vm_pc final_state.vm_mu;
    printf "%s\n%!" (serialize_state_json final_state);
    if exit_code = 5 then
      eprintf "[ERROR] NoFI policy violation: cert-setting instruction with non-positive cost\n%!";
    close_all_channels ();
    eprintf "[DEBUG] Output complete\n%!";
    exit exit_code  (* Explicit exit to bypass GC finalization *)
  with
  | Stack_overflow ->
      eprintf "[ERROR] Stack overflow during execution\n%!";
      exit 3
  | e ->
      eprintf "[ERROR] Exception: %s\n%!" (Printexc.to_string e);
      exit 4

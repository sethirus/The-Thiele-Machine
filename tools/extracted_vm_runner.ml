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
  try int_of_string s with _ -> failwith ("invalid int: " ^ s)

let char_list_of_string (s : string) : char list =
  List.init (String.length s) (String.get s)

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

let json_int_list (xs : int list) : string =
  let rec go = function
    | [] -> ""
    | [ x ] -> string_of_int x
    | x :: rest -> string_of_int x ^ "," ^ go rest
  in
  "[" ^ go xs ^ "]"

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
             "{\"id\":%d,\"region\":%s,\"axioms\":%d,\"axiom_strings\":[%s]}"
             mid
             (json_int_list m.module_region)
             (List.length m.module_axioms)
             axiom_strings)
    |> String.concat ","
  in
  sprintf
    "{\"pc\":%d,\"mu\":%d,\"err\":%s,\"regs\":%s,\"mem\":%s,\"mu_tensor\":%s,\"csrs\":{\"cert_addr\":%d,\"status\":%d,\"err\":%d,\"heap_base\":%d},\"graph\":{\"next_id\":%d,\"modules\":[%s]}}"
    s.vm_pc
    s.vm_mu
    (json_bool s.vm_err)
    (json_int_list s.vm_regs)
    (json_int_list s.vm_mem)
    (json_int_list s.vm_mu_tensor)
    s.vm_csrs.csr_cert_addr
    s.vm_csrs.csr_status
    s.vm_csrs.csr_err
    s.vm_csrs.csr_heap_base
    s.vm_graph.pg_next_id
    modules_json

let write_checkpoint (label : string) (s : vMState) : unit =
  let filename = label ^ ".json" in
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

(* A program element is either a real VM instruction or a harness directive. *)
type program_element =
  | Instr of VMStep.vm_instruction
  | Checkpoint of string
  | WritePort of string * int    (* channel_name, src_reg *)
  | ReadPort of int * string     (* dst_reg, channel_name *)

let parse_program (lines : string list) : int * int list * int list * program_element list =
    let fuel = ref 256 in
    let mem_size = ref 4096 in
    let rec make_list n acc =
      if n <= 0 then acc else make_list (n - 1) (0 :: acc)
    in
    let init_regs = ref (make_list 32 []) in
    let init_mem = ref None in  (* deferred until mem_size is known *)

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
        init_regs := list_set_mod 32 !init_regs (safe_int r) (safe_int v);
        None
      | [ "INIT_MEM"; a; v ] ->
        let m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
        init_mem := Some (list_set_mod !mem_size m (safe_int a) (safe_int v));
        None
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
      | [ "LASSERT"; mid; axiom; cost ] ->
        Some (Instr (VMStep.Coq_instr_lassert (safe_int mid, char_list_of_string axiom,
          VMStep.Coq_lassert_cert_sat (char_list_of_string ""), safe_int cost)))
      | [ "LJOIN"; f1; f2; cost ] ->
        Some (Instr (VMStep.Coq_instr_ljoin (char_list_of_string f1, char_list_of_string f2, safe_int cost)))
      | [ "EMIT"; mid; bits; cost ] ->
        Some (Instr (VMStep.Coq_instr_emit (safe_int mid, char_list_of_string bits, safe_int cost)))
      | [ "ORACLE_HALTS"; payload; cost ] ->
        Some (Instr (VMStep.Coq_instr_oracle_halts (char_list_of_string payload, safe_int cost)))
      | [ "HALT"; cost ] -> Some (Instr (VMStep.Coq_instr_halt (safe_int cost)))
      | _ -> failwith ("unrecognized instruction line: " ^ t)
  in
  let elements = lines |> List.filter_map parse_line in
  let init_m = match !init_mem with Some m -> m | None -> make_list !mem_size [] in
  (!fuel, !init_regs, init_m, elements)

let initial_state () : vMState =
  let rec make_list n acc =
    if n <=  0 then acc else make_list (n - 1) (0 :: acc)
  in
  {
    vm_graph = { pg_next_id = 1; pg_modules = [] };
    vm_csrs = { csr_cert_addr = 0; csr_status = 0; csr_err = 0; csr_heap_base = 0 };
    vm_regs = make_list 32 [];
    vm_mem = make_list 4096 [];
    vm_pc = 0;
    vm_mu = 0;
    vm_mu_tensor = make_list 16 [];
    vm_err = false;
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
          let s' = vm_apply_nofi s instr in
          (* Side-effect: Coq instr_checkpoint serializes state to <label>.json *)
          (match instr with
           | VMStep.Coq_instr_checkpoint (label_chars, _) ->
               write_checkpoint (string_of_char_list label_chars) s'
           | _ -> ());
          loop (fuel - 1) s'
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
let parse_json_int (json : string) (key : string) : int =
  let pattern = sprintf "\"%s\":" key in
  try
    let i = Str.search_forward (Str.regexp_string pattern) json 0 in
    let start = i + String.length pattern in
    let s = String.sub json start (min 20 (String.length json - start)) in
    let s = trim s in
    (* Extract leading integer *)
    let j = ref 0 in
    let neg = !j < String.length s && s.[!j] = '-' in
    if neg then incr j;
    while !j < String.length s && s.[!j] >= '0' && s.[!j] <= '9' do incr j done;
    let ns = String.sub s (if neg then 0 else 0) !j in
    int_of_string ns
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
      |> List.map int_of_string
  with _ -> []

let load_resume_state (path : string) : vMState =
  let ic = open_in path in
  let json = really_input_string ic (in_channel_length ic) in
  close_in ic;
  let rec make_list n acc =
    if n <= 0 then acc else make_list (n - 1) (0 :: acc)
  in
  {
    vm_graph = { pg_next_id = parse_json_int json "next_id"; pg_modules = [] };
    vm_csrs = {
      csr_cert_addr = parse_json_int json "cert_addr";
      csr_status = parse_json_int json "status";
      csr_err = parse_json_int json "err";
      csr_heap_base = parse_json_int json "heap_base";
    };
    vm_regs = (let r = parse_json_int_array json "regs" in
               if r = [] then make_list 32 [] else r);
    vm_mem = (let m = parse_json_int_array json "mem" in
              if m = [] then make_list 4096 [] else m);
    vm_pc = parse_json_int json "pc";
    vm_mu = parse_json_int json "mu";
    vm_mu_tensor = (let t = parse_json_int_array json "mu_tensor" in
                    if t = [] then make_list 16 [] else t);
    vm_err = parse_json_bool json "err";
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
    let fuel, regs0, mem0, prog = parse_program lines in
    eprintf "[DEBUG] Parsed: fuel=%d, prog_len=%d\n%!" fuel (List.length prog);
    let s0 = match !resume_path with
      | Some path ->
        eprintf "[DEBUG] Resuming from %s\n%!" path;
        load_resume_state path
      | None ->
        let s = initial_state () in
        { s with vm_regs = regs0; vm_mem = mem0 }
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

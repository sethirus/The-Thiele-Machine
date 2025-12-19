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

let list_set_mod (size : int) (xs : int list) (idx : int) (v : int) : int list =
  let idx = if size <= 0 then 0 else ((idx mod size) + size) mod size in
  let rec go i = function
    | [] -> []
    | x :: rest ->
        if i = idx then v :: rest else x :: go (i + 1) rest
  in
  go 0 xs

let parse_program (lines : string list) : int * int list * int list * VMStep.vm_instruction list =
  let rec skip_blanks = function
    | [] -> []
    | l :: rest ->
        let t = trim l in
        if t = "" || t.[0] = '#' || t.[0] = ';' then skip_blanks rest else l :: rest
  in
  let lines = skip_blanks lines in
  let fuel, rest_lines =
    match lines with
    | first :: rest ->
        let t = trim first in
        let toks = split_ws t in
        (match toks with
        | [ "FUEL"; n ] -> (safe_int n, rest)
        | _ -> (256, lines))
    | [] -> (256, [])
  in
    let init_regs = ref (List.init 32 (fun _ -> 0)) in
    let init_mem = ref (List.init 256 (fun _ -> 0)) in

    let parse_line (line : string) : VMStep.vm_instruction option =
    let t = trim line in
    if t = "" || t.[0] = '#' || t.[0] = ';' then None
    else
      let toks = split_ws t in
      match toks with
      | [ "INIT_REG"; r; v ] ->
        init_regs := list_set_mod 32 !init_regs (safe_int r) (safe_int v);
        None
      | [ "INIT_MEM"; a; v ] ->
        init_mem := list_set_mod 256 !init_mem (safe_int a) (safe_int v);
        None
      | [ "PNEW"; region_tok; cost ] ->
          Some (VMStep.Coq_instr_pnew (parse_region region_tok, safe_int cost))
      | [ "PSPLIT"; mid; left_tok; right_tok; cost ] ->
          Some
            (VMStep.Coq_instr_psplit
               ( safe_int mid,
                 parse_region left_tok,
                 parse_region right_tok,
                 safe_int cost ))
      | [ "PMERGE"; m1; m2; cost ] ->
          Some (VMStep.Coq_instr_pmerge (safe_int m1, safe_int m2, safe_int cost))
      | [ "MDLACC"; mid; cost ] ->
          Some (VMStep.Coq_instr_mdlacc (safe_int mid, safe_int cost))
      | [ "PDISCOVER"; mid; evidence_tok; cost ] ->
          let evidence =
            parse_brace_list evidence_tok
            |> List.map char_list_of_string
          in
          Some (VMStep.Coq_instr_pdiscover (safe_int mid, evidence, safe_int cost))
      | [ "XFER"; dst; src; cost ] ->
        Some (VMStep.Coq_instr_xfer (safe_int dst, safe_int src, safe_int cost))
      | [ "XOR_LOAD"; dst; addr; cost ] ->
        Some (VMStep.Coq_instr_xor_load (safe_int dst, safe_int addr, safe_int cost))
      | [ "XOR_ADD"; dst; src; cost ] ->
        Some (VMStep.Coq_instr_xor_add (safe_int dst, safe_int src, safe_int cost))
      | [ "XOR_SWAP"; a; b; cost ] ->
        Some (VMStep.Coq_instr_xor_swap (safe_int a, safe_int b, safe_int cost))
      | [ "XOR_RANK"; dst; src; cost ] ->
        Some (VMStep.Coq_instr_xor_rank (safe_int dst, safe_int src, safe_int cost))
      | [ "CHSH_TRIAL"; x; y; a; b; cost ] ->
        Some
          (VMStep.Coq_instr_chsh_trial
             ( safe_int x,
               safe_int y,
               safe_int a,
               safe_int b,
               safe_int cost ))
      | [ "ORACLE_HALTS"; payload; cost ] ->
        Some (VMStep.Coq_instr_oracle_halts (char_list_of_string payload, safe_int cost))
      | [ "HALT"; cost ] -> Some (VMStep.Coq_instr_halt (safe_int cost))
      | _ -> failwith ("unrecognized instruction line: " ^ t)
  in
  let instrs =
    rest_lines |> List.filter_map parse_line
  in
    (fuel, !init_regs, !init_mem, instrs)

let initial_state () : vMState =
  {
    vm_graph = { pg_next_id = 1; pg_modules = [] };
    vm_csrs = { csr_cert_addr = 0; csr_status = 0; csr_err = 0 };
    vm_regs = List.init 32 (fun _ -> 0);
    vm_mem = List.init 256 (fun _ -> 0);
    vm_pc = 0;
    vm_mu = 0;
    vm_err = false;
  }

let () =
  if Array.length Sys.argv <> 2 then (
    eprintf "usage: %s <trace.txt>\n" Sys.argv.(0);
    exit 2);
  let trace_path = Sys.argv.(1) in
  let lines = read_all_lines trace_path in
  let fuel, regs0, mem0, prog = parse_program lines in
  let s0 = initial_state () in
  let s0 = { s0 with vm_regs = regs0; vm_mem = mem0 } in
  let final_state = run_vm fuel prog s0 in
  let modules_json =
    final_state.vm_graph.pg_modules
    |> List.map (fun (mid, m) ->
           sprintf
             "{\"id\":%d,\"region\":%s,\"axioms\":%d}"
             mid
             (json_int_list m.module_region)
             (List.length m.module_axioms))
    |> String.concat ","
  in
  printf
    "{\"pc\":%d,\"mu\":%d,\"err\":%s,\"regs\":%s,\"mem\":%s,\"csrs\":{\"cert_addr\":%d,\"status\":%d,\"err\":%d},\"graph\":{\"next_id\":%d,\"modules\":[%s]}}\n"
    final_state.vm_pc
    final_state.vm_mu
    (json_bool final_state.vm_err)
    (json_int_list final_state.vm_regs)
    (json_int_list final_state.vm_mem)
    final_state.vm_csrs.csr_cert_addr
    final_state.vm_csrs.csr_status
    final_state.vm_csrs.csr_err
    final_state.vm_graph.pg_next_id
    modules_json

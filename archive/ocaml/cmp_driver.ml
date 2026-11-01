(* cmp_driver.ml: a command-line driver for the verified compiler extracted
   from Coq (cmp_extracted.ml, from coq/kernel/foundation/CmpExtract.v).

   The driver is input and output only. It reads the text of source programs
   (s-expressions) from standard input, builds syntax trees with the
   extracted constructors, calls the extracted functions (the shape check,
   the compiler, the host program, the runner, the source interpreter) and
   prints what they return as lines of words and integers. It defines no
   behaviour of the compiler or of the machines. The python tests
   (tests/test_cmp_compiler.py) write the input and check the output against
   independent python implementations of the source language, the counter
   machine and the host machine.

   Build (from the directory holding cmp_extracted.ml/.mli):
     ocamlfind ocamlopt -package zarith -linkpkg \
       cmp_extracted.mli cmp_extracted.ml cmp_driver.ml -o cmp_driver

   Source syntax.
     aexp  := N | (v N) | (+ aexp aexp) | (- aexp aexp)        (- is truncated)
     bexp  := true | false | (= aexp aexp) | (< aexp aexp) | (not bexp)
              | (and bexp bexp) | (or bexp bexp)
     stmt  := skip | (set N aexp) | (seq stmt stmt ...) | (if bexp stmt stmt)
              | (while bexp stmt) | (call (N ...) N (aexp ...))
     proc  := (proc N stmt (aexp ...))     parameters, body, result expressions
     prog  := (prog (proc ...) stmt)       procedures, main statement
   A bare number N in an aexp is the constant; (v N) is variable N.

   Commands.
     (case ID NIN OUT IFUEL HFUEL (X ...) PROG)
         checks the shape of PROG, compiles it, runs the source interpreter
         with fuel IFUEL and the host program with fuel HFUEL on inputs X ...
         and prints a block of lines ending with END:
           case ID
           wf 0|1                           (a program that is not well
                                             formed stops here)
           sizes NV0 NVF MMLEN HOSTLEN
           interp none | interp OPS V0 V1 ...      (variables 0 .. NV0 - 1)
           host halted 0|1 STEPS PC ANSWER V0 V1 ...   (registers 1 .. NV0)
           time COMPILE INTERP RUN          (seconds of processor time)
     (dump NIN OUT PROG)
         prints the counter machine program and the host program:
           mm L, then L lines "inc X" or "dec X J"
           host L, then L lines "inc X" or "dec X J"
           END
*)

module E = Cmp_extracted

(* ----------------------------------------------------------------- *)
(* Reading s-expressions.                                             *)
(* ----------------------------------------------------------------- *)

type sx = A of string | L of sx list

let read_all () =
  let buf = Buffer.create 65536 in
  let chunk = Bytes.create 65536 in
  let rec loop () =
    let n = input stdin chunk 0 65536 in
    if n > 0 then begin
      Buffer.add_subbytes buf chunk 0 n;
      loop ()
    end
  in
  loop ();
  Buffer.contents buf

let tokenize s =
  let n = String.length s in
  let toks = ref [] in
  let i = ref 0 in
  while !i < n do
    let c = s.[!i] in
    if c = '(' || c = ')' then begin toks := String.make 1 c :: !toks; incr i end
    else if c = ' ' || c = '\n' || c = '\t' || c = '\r' then incr i
    else begin
      let j = ref !i in
      while !j < n && (let d = s.[!j] in d <> '(' && d <> ')' && d <> ' ' && d <> '\n' && d <> '\t' && d <> '\r') do incr j done;
      toks := String.sub s !i (!j - !i) :: !toks;
      i := !j
    end
  done;
  Array.of_list (List.rev !toks)

let parse_all toks =
  let pos = ref 0 in
  let n = Array.length toks in
  let rec one () =
    let t = toks.(!pos) in
    incr pos;
    if t = "(" then begin
      let items = ref [] in
      while !pos < n && toks.(!pos) <> ")" do items := one () :: !items done;
      if !pos >= n then failwith "unbalanced parenthesis";
      incr pos;
      L (List.rev !items)
    end else if t = ")" then failwith "unexpected )"
    else A t
  in
  let out = ref [] in
  while !pos < n do out := one () :: !out done;
  List.rev !out

(* ----------------------------------------------------------------- *)
(* Building the extracted syntax trees.                               *)
(* ----------------------------------------------------------------- *)

let z_of = function A s -> Z.of_string s | L _ -> failwith "number expected"
let zlist = function L l -> List.map z_of l | A _ -> failwith "list of numbers expected"

let rec aexp = function
  | A s -> E.CNum (Z.of_string s)
  | L [A "v"; x] -> E.CVar (z_of x)
  | L [A "+"; a; b] -> E.CAdd (aexp a, aexp b)
  | L [A "-"; a; b] -> E.CSub (aexp a, aexp b)
  | _ -> failwith "bad arithmetic expression"

let rec bexp = function
  | A "true" -> E.BTrue
  | A "false" -> E.BFalse
  | L [A "="; a; b] -> E.BEq (aexp a, aexp b)
  | L [A "<"; a; b] -> E.BLt (aexp a, aexp b)
  | L [A "not"; b] -> E.BNot (bexp b)
  | L [A "and"; a; b] -> E.BAnd (bexp a, bexp b)
  | L [A "or"; a; b] -> E.BOr (bexp a, bexp b)
  | _ -> failwith "bad boolean expression"

let rec stmt = function
  | A "skip" -> E.SSkip
  | L [A "set"; x; a] -> E.SAssign (z_of x, aexp a)
  | L (A "seq" :: l) ->
    (match List.rev (List.map stmt l) with
     | [] -> E.SSkip
     | last :: rest -> List.fold_left (fun acc s -> E.SSeq (s, acc)) last rest)
  | L [A "if"; b; s; t] -> E.SIf (bexp b, stmt s, stmt t)
  | L [A "while"; b; s] -> E.SWhile (bexp b, stmt s)
  | L [A "call"; ds; p; L args] -> E.SCall (zlist ds, z_of p, List.map aexp args)
  | _ -> failwith "bad statement"

let proc = function
  | L [A "proc"; np; body; L rets] -> { E.pr_np = z_of np; pr_body = stmt body; pr_rets = List.map aexp rets }
  | _ -> failwith "bad procedure"

let prog = function
  | L [A "prog"; L procs; main] -> { E.cp_procs = List.map proc procs; cp_main = stmt main }
  | _ -> failwith "bad program"

(* ----------------------------------------------------------------- *)
(* Printing.                                                          *)
(* ----------------------------------------------------------------- *)

let zs = Z.to_string
let join l = String.concat " " (List.map zs l)

let print_mm l =
  Printf.printf "mm %d\n" (List.length l);
  List.iter (function
      | E.Mm_inc x -> Printf.printf "inc %s\n" (zs x)
      | E.Mm_dec (x, j) -> Printf.printf "dec %s %s\n" (zs x) (zs j)) l

let print_host l =
  Printf.printf "host %d\n" (List.length l);
  List.iter (function
      | E.HInc x -> Printf.printf "inc %s\n" (zs x)
      | E.HDec (x, j) -> Printf.printf "dec %s %s\n" (zs x) (zs j)) l

(* ----------------------------------------------------------------- *)
(* Commands.                                                          *)
(* ----------------------------------------------------------------- *)

let do_case id nin out ifuel hfuel xs p =
  Printf.printf "case %s\n" id;
  if not (E.cmp_wf_b p) then begin
    print_string "wf 0\nEND\n"
  end else begin
    print_string "wf 1\n";
    let t0 = Sys.time () in
    let mm = E.cmp_mm_prog p nin out in
    let host = E.cmp_hostprog p nin out in
    let nv0 = E.cmp_nv0 p nin out in
    let nvf = E.cmp_nvF p nin out in
    (* force the whole program *)
    let mml = List.length mm and hl = List.length host in
    Printf.printf "sizes %s %s %d %d\n" (zs nv0) (zs nvf) mml hl;
    let t1 = Sys.time () in
    let res = E.cmp_run_interp p ifuel xs in
    (match res with
     | None -> print_string "interp none\n"
     | Some (l, k) ->
       let vars = List.init (Z.to_int nv0) (fun x -> E.cmp_lget l (Z.of_int x)) in
       Printf.printf "interp %s %s\n" (zs k) (join vars));
    let t2 = Sys.time () in
    let r = E.cmp_exec p nin out xs hfuel in
    let t3 = Sys.time () in
    let steps = Z.sub hfuel r.E.cr_left in
    let vars = List.init (Z.to_int nv0) (fun x -> E.cr_rget r.E.cr_regs (Z.of_int (x + 1))) in
    Printf.printf "host halted %d %s %s %s %s\n" (if r.E.cr_halted then 1 else 0) (zs steps)
      (zs r.E.cr_pc) (zs (E.cmp_answer out r)) (join vars);
    Printf.printf "time %.3f %.3f %.3f\n" (t1 -. t0) (t2 -. t1) (t3 -. t2);
    print_string "END\n"
  end;
  flush stdout

let do_dump nin out p =
  if not (E.cmp_wf_b p) then print_string "wf 0\nEND\n"
  else begin
    print_mm (E.cmp_mm_prog p nin out);
    print_host (E.cmp_hostprog p nin out);
    print_string "END\n"
  end;
  flush stdout

let () =
  let items = parse_all (tokenize (read_all ())) in
  List.iter (function
      | L [A "case"; A id; nin; out; ifuel; hfuel; xs; p] ->
        do_case id (z_of nin) (z_of out) (z_of ifuel) (z_of hfuel) (zlist xs) (prog p)
      | L [A "dump"; nin; out; p] -> do_dump (z_of nin) (z_of out) (prog p)
      | _ -> failwith "unknown command")
    items

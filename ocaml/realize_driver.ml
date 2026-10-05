(* realize_driver.ml: a command-line driver for the machines extracted from
   Coq (realize_extracted.ml, from ocaml/RealizeExtract.v).

   The driver is input and output only. It reads whitespace-separated words
   and numbers from standard input, builds instructions with the extracted
   constructors rlz_mk_*, runs the extracted machines, and prints states with
   the extracted rlz_view_* functions as lines of integers. It defines no
   machine behaviour. The python tests (tests/test_realize.py) write the
   input and compare the output with the python realisation.

   Build (from the directory holding realize_extracted.ml/.mli):
     ocamlfind ocamlopt -package zarith -linkpkg \
       realize_extracted.mli realize_extracted.ml realize_driver.ml -o realize_driver

   Commands. Every instruction is four integers: op a b c, with op 0 INC a,
   1 DEC a b, 2 HALT, 3 CHECK a with property (b, c), 4 COMMIT a with
   property (b, c), 5 CERTIFY, 6 PAY. A program is its length L followed by
   L instructions. A register file is NS followed by NS pairs (register,
   value); every other register is 0. Each command prints its lines and then
   the line END.

     small N A B <prog>              N steps of the small machine from start A B
     multi N NR <regs> <prog>        the multi-register host over the counter language
     pmulti N NR <regs> <prog>       the same with PAY
     slot N NR <regs> <prog>         the host over PSlot (the host of U)
     pslot N NR <regs> <prog>        the priced host over PSlot (the host of U_P)
     uhost NR STRIDE K X Y <guest>   U run on the guest: the state, then K
                                     states each STRIDE steps later
     puhost NR STRIDE K X Y <guest>  U_P run on the priced guest
     pair M N | unpair X | qs I | heval X | puheval X
     progcode <prog> | puprogcode <prog>

   Each state line is the flat list of rlz_view_*: see thiele_small/flat.py. *)

module R = Realize_extracted

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

let is_space c = c = ' ' || c = '\n' || c = '\t' || c = '\r'

let split_ws s =
  let n = String.length s in
  let toks = ref [] in
  let i = ref 0 in
  while !i < n do
    while !i < n && is_space s.[!i] do incr i done;
    let j = ref !i in
    while !j < n && not (is_space s.[!j]) do incr j done;
    if !j > !i then toks := String.sub s !i (!j - !i) :: !toks;
    i := !j
  done;
  Array.of_list (List.rev !toks)

let toks = split_ws (read_all ())
let pos = ref 0

let next () =
  let t = toks.(!pos) in
  incr pos;
  t

let next_int () = int_of_string (next ())
let next_z () = Z.of_string (next ())

let print_line s =
  print_string s;
  print_char '\n'

let print_ints l = print_line (String.concat " " (List.map Z.to_string l))

let read_prog mk =
  let l = next_int () in
  let rec go k acc =
    if k = 0 then List.rev acc
    else begin
      let op = next_z () in
      let a = next_z () in
      let b = next_z () in
      let c = next_z () in
      go (k - 1) (mk op a b c :: acc)
    end
  in
  go l []

let read_regs () =
  let ns = next_int () in
  let rec go k acc =
    if k = 0 then List.rev acc
    else begin
      let r = next_z () in
      let v = next_z () in
      go (k - 1) ((r, v) :: acc)
    end
  in
  R.rlz_mk_regs (go ns [])

let cmd_small () =
  let n = next_int () in
  let a = next_z () in
  let b = next_z () in
  let prog = read_prog R.rlz_mk_small in
  let s = ref (R.rlz_small_start a b) in
  print_ints (R.rlz_view_small !s);
  for _i = 1 to n do
    s := R.rlz_small_step prog !s;
    print_ints (R.rlz_view_small !s)
  done

let cmd_multi () =
  let n = next_int () in
  let nr = Z.of_int (next_int ()) in
  let regs = read_regs () in
  let prog = read_prog R.rlz_mk_multi in
  let s = ref (R.rlz_multi_start regs) in
  print_ints (R.rlz_view_multi nr !s);
  for _i = 1 to n do
    s := R.rlz_multi_step prog !s;
    print_ints (R.rlz_view_multi nr !s)
  done

let cmd_pmulti () =
  let n = next_int () in
  let nr = Z.of_int (next_int ()) in
  let regs = read_regs () in
  let prog = read_prog R.rlz_mk_pmulti in
  let s = ref (R.rlz_pmulti_start regs) in
  print_ints (R.rlz_view_pmulti nr !s);
  for _i = 1 to n do
    s := R.rlz_pmulti_step prog !s;
    print_ints (R.rlz_view_pmulti nr !s)
  done

let cmd_slot () =
  let n = next_int () in
  let nr = Z.of_int (next_int ()) in
  let regs = read_regs () in
  let prog = read_prog R.rlz_mk_slot in
  let s = ref (R.rlz_host_start regs) in
  print_ints (R.rlz_view_slot nr !s);
  for _i = 1 to n do
    s := R.rlz_host_step prog !s;
    print_ints (R.rlz_view_slot nr !s)
  done

let cmd_pslot () =
  let n = next_int () in
  let nr = Z.of_int (next_int ()) in
  let regs = read_regs () in
  let prog = read_prog R.rlz_mk_pslot in
  let s = ref (R.rlz_phost_start regs) in
  print_ints (R.rlz_view_pslot nr !s);
  for _i = 1 to n do
    s := R.rlz_phost_step prog !s;
    print_ints (R.rlz_view_pslot nr !s)
  done

let cmd_uhost () =
  let nr = Z.of_int (next_int ()) in
  let stride = next_z () in
  let k = next_int () in
  let x = next_z () in
  let y = next_z () in
  let guest = read_prog R.rlz_mk_small in
  let s = ref (R.rlz_host_load guest x y) in
  print_ints (R.rlz_view_slot nr !s);
  for _i = 1 to k do
    s := R.rlz_host_run_prog stride R.rlz_host_program0 !s;
    print_ints (R.rlz_view_slot nr !s)
  done

let cmd_puhost () =
  let nr = Z.of_int (next_int ()) in
  let stride = next_z () in
  let k = next_int () in
  let x = next_z () in
  let y = next_z () in
  let guest = read_prog R.rlz_mk_pguest in
  let s = ref (R.rlz_phost_load guest x y) in
  print_ints (R.rlz_view_pslot nr !s);
  for _i = 1 to k do
    s := R.rlz_phost_run_prog stride R.rlz_phost_program0 !s;
    print_ints (R.rlz_view_pslot nr !s)
  done

let cmd_pair () =
  let m = next_z () in
  let n = next_z () in
  print_line (Z.to_string (R.rlz_pair m n))

let cmd_unpair () =
  let x = next_z () in
  match R.rlz_unpair x with
  | None -> print_line "-"
  | Some (m, n) -> print_line (Z.to_string m ^ " " ^ Z.to_string n)

let cmd_qs () =
  let i = next_z () in
  print_line (Z.to_string (R.rlz_qs i))

let bool_line b = print_line (if b then "1" else "0")

let cmd_heval () =
  let x = next_z () in
  bool_line (R.rlz_host_eval x)

let cmd_puheval () =
  let x = next_z () in
  bool_line (R.rlz_pu_heval x)

let cmd_progcode () =
  let prog = read_prog R.rlz_mk_small in
  print_line (Z.to_string (R.rlz_prog_code prog))

let cmd_puprogcode () =
  let prog = read_prog R.rlz_mk_pguest in
  print_line (Z.to_string (R.rlz_pu_prog_code prog))

let () =
  while !pos < Array.length toks do
    let cmd = next () in
    (match cmd with
     | "small" -> cmd_small ()
     | "multi" -> cmd_multi ()
     | "pmulti" -> cmd_pmulti ()
     | "slot" -> cmd_slot ()
     | "pslot" -> cmd_pslot ()
     | "uhost" -> cmd_uhost ()
     | "puhost" -> cmd_puhost ()
     | "pair" -> cmd_pair ()
     | "unpair" -> cmd_unpair ()
     | "qs" -> cmd_qs ()
     | "heval" -> cmd_heval ()
     | "puheval" -> cmd_puheval ()
     | "progcode" -> cmd_progcode ()
     | "puprogcode" -> cmd_puprogcode ()
     | _ -> failwith ("unknown command " ^ cmd));
    print_line "END"
  done

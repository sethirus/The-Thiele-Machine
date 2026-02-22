(* Main.ml — Kami-extracted module to Bluespec pretty-printer.
   Adapted from Kami/Ext/Ocaml/Main.ml for the Thiele Machine. *)

open Format
open Target
open PP

let arg_output_file_name = ref ""
let set_output_file_name fn = arg_output_file_name := fn
let arg_top_module_name = ref "Top"
let set_top_module_name mn = arg_top_module_name := mn

let arg_spec =
  [("-top", Arg.String set_top_module_name, "Sets a top-module name")]

let usage_msg =
  "Usage: ./kami_to_bsv [-top top_module_name] output_file_name\n"

let () =
  Arg.parse arg_spec set_output_file_name usage_msg;
  if String.length !arg_output_file_name = 0 then
    Printf.printf "%s" usage_msg
  else
    let oc = open_out !arg_output_file_name in
    set_formatter_out_channel oc;
    (* No header file needed — we generate clean BSV *)
    let ic = open_in "/dev/null" in
    (match thieleCoreB with
     | Some bml -> ppBModulesFullDbg bml
                     { cfg_debug = false;
                       cfg_top_module_name = !arg_top_module_name
                     } ic
     | _ -> Printf.printf "Error: Empty bModules from Kami extraction\n");
    close_out oc

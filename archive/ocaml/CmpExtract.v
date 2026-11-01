(** CmpExtract.v: OCaml extraction of the verified compiler and its runners.

    Everything extracted is a Coq definition of the Cmp files, apart from the
    three one-line wrappers below, which only fix the argument order and the
    starting operation count of the interpreter:

      cmp_wf_b        the check of the shape of programs (CmpRun.v), proved to
                      agree with cmp_wf (cmp_wf_b_spec)
      cmp_mm_prog     the compiler from source programs to counter machine
                      programs (CmpCompile.v, stages proved in CmpInline.v,
                      CmpFlat.v, CmpMM.v and composed in CmpCompile.v)
      cmp_hostprog    the counter machine program turned into a host program
                      with INC and DEC only (CmpHost.v)
      cmp_exec        the runner of the host program (CmpRun.v), proved against
                      the register semantics and the host machine of
                      EarnedMulti.v (cmp_exec_machine, cmp_exec_sound,
                      cmp_exec_complete, cmp_exec_unhalted)
      cmp_run_interp  the source interpreter (CmpLang.v, cmp_interp_sound and
                      cmp_interp_complete)

    The OCaml driver (ocaml/cmp_driver.ml) only reads the text of a source
    program, builds the extracted syntax trees with the extracted
    constructors, calls these functions and prints the results. It defines no
    behaviour of the machines or of the compiler.

    Extraction choices. Each is a choice of OCaml representation for an
    inductive type; none is an axiom, and no Axiom or Parameter is
    extracted.

      bool, option, list, prod, unit, sumbool   mapped to the OCaml type
          with the same constructors in the same order (as ExtrOcamlBasic); sumbool is the type of the decision
          functions eq_nat_dec and Nat.eq_dec used by the vendored linker
      nat   mapped to Zarith's Z.t with 0 and Z.succ as constructors and a
          match that tests the sign, with a native operation for each
          arithmetic function the extracted code calls: add, mul, truncated
          sub, eqb, leb, ltb, div and modulo (Coq's x / 0 = 0 and
          x mod 0 = x). Values of source programs grow without bound (a
          product, a factorial), so a native 63-bit integer would wrap
          silently; Z.t does not. ExtrOcamlNatInt is not used.
      andb, orb   inlined as the lazy && and || (as ExtrOcamlBasic)

    Run as: coqc ... CmpExtract.v from a directory where cmp_extracted.ml and
    .mli may be written.

    Dependencies: CmpRun.v and the Cmp files before it. No axioms and no
    unfinished proofs.                                                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is the extraction root of the verified compiler; its claims are in the Cmp
   files it extracts from. *)

From Coq Require Import List Arith Extraction.
Import ListNotations.
Require Import Kernel.CmpLang Kernel.CmpBlocks Kernel.CmpCompile Kernel.CmpHost Kernel.CmpRun.

(* The interpreter of CmpLang.v on the main statement, from the inputs xs
   (variables 0, 1, ...) with the operation count 0. *)
Definition cmp_run_interp (p : cmp_prog) (fuel : nat) (xs : list nat) : option (list nat * nat) :=
  cmp_interp (cp_procs p) fuel xs (cp_main p) 0.

Extraction Language OCaml.
Extraction Blacklist List Nat Bool String Option Z Big_int Int.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive option => "option" ["Some" "None"].
Extract Inductive unit => "unit" ["()"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inductive prod => "( * )" [""].
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"]
  "(fun fO fS n -> if Z.sign n <= 0 then fO () else fS (Z.pred n))".
(* plus, mult, minus are the names under which Coq elaborates + * - ; Nat.add,
   Nat.mul, Nat.sub are the same functions under their own names, and the
   extraction tables are keyed by the name, so both are given. *)
Extract Constant plus => "Z.add". (* SAFE: Z.add is exact integer addition and nat is extracted as Z.t. *)
Extract Constant mult => "Z.mul". (* SAFE: Z.mul is exact integer multiplication. *)
Extract Constant minus => "(fun n m -> Z.max Z.zero (Z.sub n m))". (* SAFE: truncated subtraction, which is what nat subtraction is. *)
Extract Constant Nat.add => "Z.add". (* SAFE: same function as plus under its other name. *)
Extract Constant Nat.mul => "Z.mul". (* SAFE: same function as mult under its other name. *)
Extract Constant Nat.sub => "(fun n m -> Z.max Z.zero (Z.sub n m))". (* SAFE: same function as minus under its other name. *)
Extract Constant Nat.eqb => "Z.equal". (* SAFE: Z.equal tests integer equality. *)
Extract Constant Nat.leb => "Z.leq". (* SAFE: Z.leq tests integer order. *)
Extract Constant Nat.ltb => "Z.lt". (* SAFE: Z.lt tests strict integer order. *)
Extract Constant Nat.div => "(fun a b -> if Z.equal b Z.zero then Z.zero else Z.div a b)". (* SAFE: floor division on naturals with Coq x/0 = 0. *)
Extract Constant Nat.modulo => "(fun a b -> if Z.equal b Z.zero then a else Z.rem a b)". (* SAFE: remainder on naturals with Coq x mod 0 = x. *)
Extract Constant Peano_dec.eq_nat_dec => "Z.equal". (* SAFE: a decision of equality on Z.t is the equality test. *)
Extract Constant Nat.eq_dec => "Z.equal". (* SAFE: a decision of equality on Z.t is the equality test. *)

(* nat and the arithmetic above are the only substitutions. Everything
   else, the compiler, the interpreter, the tries and the runner, is
   extracted from its Coq definition. *)

Extraction "cmp_extracted.ml"
  cmp_wf_b cmp_mm_prog cmp_hostprog cmp_nv0 cmp_nvF cmp_exec cmp_answer cmp_vars
  cmp_run_interp cr_rget cr_load cr_ptab cr_run cmp_flat.

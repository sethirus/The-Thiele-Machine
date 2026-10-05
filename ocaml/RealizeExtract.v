(** RealizeExtract.v: OCaml extraction of the machines, from Realize.v and
    RealizePriced.v.

    Everything extracted is a name defined in Realize.v or RealizePriced.v
    (prefix rlz_), which those files prove to be the function the theorems
    are about, plus a few plain input and output helpers (prefixes rlz_mk_,
    rlz_view_, rlz_stopped_) defined below. The helpers only turn lists of
    numbers into instructions and states into lists of numbers, so that the
    OCaml driver (ocaml/realize_driver.ml) needs no knowledge of the
    extracted type names; they define no machine behaviour.

    Extraction choices. Each is a choice of OCaml representation for a Coq
    inductive type; none is an axiom, and no Axiom or Parameter is extracted.

      bool, option, list, prod, unit, sumbool   mapped to the OCaml type
          with the same constructors in the same order (the mapping of
          the standard ExtrOcamlBasic, written out here). sumbool is
          the type of the decision functions eq_nat_dec and Nat.eq_dec.
      hprop, pu_hprop   the one-constructor property types of the host
          (UniversalCodes.v, UniversalPCodes.v), mapped to unit. Coq's
          extraction cannot read the files that define them (they contain
          module aliases), and a type with one constructor and no
          arguments is unit.
      nat   mapped to Zarith's Z.t with 0 and Z.succ as constructors and a
          match that tests the sign, together with a native OCaml
          operation for each arithmetic function the extracted code
          calls: add, mul, truncated sub, eqb, leb, ltb, pow, div, modulo,
          div2, even and odd. Each is the standard function on the
          non-negative integers, with Coq's value at division by zero
          (x / 0 = 0, x mod 0 = x). Peano nat is not usable here: the
          program code of a guest program is a power of two as large as
          2^100 and the pairing function 2^m * (2n + 1) is used throughout.
          The OCaml integer type ExtrOcamlNatInt is not used because a
          63-bit integer would wrap silently on those values. Z.t has no
          bound. The one function that can fail is Nat.pow, whose exponent
          must fit in a native int; Z.to_int raises Overflow otherwise,
          which stops the run and never gives a wrong value.
      andb, orb   inlined as the lazy && and || (as ExtrOcamlBasic), so
          evaluation order is that of the Coq definitions.

    Run as: coqc ... RealizeExtract.v from a directory where
    realize_extracted.ml and .mli may be written.

    Dependencies: Realize.v, RealizePriced.v. No axioms, no Admitted.     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is the extraction root of the realisation; its claims are in
   Realize.v and RealizePriced.v. *)

From Coq Require Import List Arith Lia Bool Extraction.
Import ListNotations.
Require Import Kernel.Realize.
Require Import Kernel.RealizePriced.

(* ================================================================= *)
(* Input and output helpers.                                          *)
(* ================================================================= *)

(* Counter 0 is CA, anything else CB. *)
Definition rlz_mk_ctr (n : nat) : Minimal.EarnedCore.ctr := if Nat.eqb n 0 then Minimal.EarnedCore.CA else Minimal.EarnedCore.CB.

(* The counter-language properties: 0 PZero, 1 PEven, anything else PGe c. *)
Definition rlz_mk_eprop (k c : nat) : Minimal.EarnedCore.prop :=
  match k with 0 => Minimal.EarnedCore.PZero | 1 => Minimal.EarnedCore.PEven | _ => Minimal.EarnedCore.PGe c end.

(* An instruction from four numbers (op, a, b, c): op 0 INC a, 1 DEC a b,
   2 HALT, 3 CHECK (property b c) a, 4 COMMIT (property b c) a, 5 CERTIFY,
   6 PAY (priced machines). Anything else is HALT. *)
Definition rlz_mk_small (op a b c : nat) : Minimal.EarnedCore.instr :=
  match op with
  | 0 => Minimal.EarnedCore.INC (rlz_mk_ctr a)
  | 1 => Minimal.EarnedCore.DEC (rlz_mk_ctr a) b
  | 3 => Minimal.EarnedCore.CHECK (rlz_mk_eprop b c) (rlz_mk_ctr a)
  | 4 => Minimal.EarnedCore.COMMIT (rlz_mk_eprop b c) (rlz_mk_ctr a)
  | 5 => Minimal.EarnedCore.CERTIFY
  | _ => Minimal.EarnedCore.HALT
  end.

Definition rlz_mk_multi (op a b c : nat) : @Minimal.EarnedMulti.instr Minimal.EarnedCore.prop :=
  match op with
  | 0 => Minimal.EarnedMulti.INC a
  | 1 => Minimal.EarnedMulti.DEC a b
  | 3 => Minimal.EarnedMulti.CHECK (rlz_mk_eprop b c) a
  | 4 => Minimal.EarnedMulti.COMMIT (rlz_mk_eprop b c) a
  | 5 => Minimal.EarnedMulti.CERTIFY
  | _ => Minimal.EarnedMulti.HALT
  end.

Definition rlz_mk_pmulti (op a b c : nat) : @Minimal.EarnedMultiPriced.pu_instr Minimal.EarnedCore.prop :=
  match op with
  | 0 => Minimal.EarnedMultiPriced.INC a
  | 1 => Minimal.EarnedMultiPriced.DEC a b
  | 3 => Minimal.EarnedMultiPriced.CHECK (rlz_mk_eprop b c) a
  | 4 => Minimal.EarnedMultiPriced.COMMIT (rlz_mk_eprop b c) a
  | 5 => Minimal.EarnedMultiPriced.CERTIFY
  | 6 => Minimal.EarnedMultiPriced.PAY
  | _ => Minimal.EarnedMultiPriced.HALT
  end.

Definition rlz_mk_slot (op a b c : nat) : @Minimal.EarnedMulti.instr Minimal.UniversalCodes.hprop :=
  match op with
  | 0 => Minimal.EarnedMulti.INC a
  | 1 => Minimal.EarnedMulti.DEC a b
  | 3 => Minimal.EarnedMulti.CHECK Minimal.UniversalCodes.PSlot a
  | 4 => Minimal.EarnedMulti.COMMIT Minimal.UniversalCodes.PSlot a
  | 5 => Minimal.EarnedMulti.CERTIFY
  | _ => Minimal.EarnedMulti.HALT
  end.

(* The universal properties: kinds 0, 1, 2 are UBase of PZero, PEven, PGe c;
   any other kind is URun c. *)
Definition rlz_mk_uprop (k c : nat) : rlz_uprop :=
  match k with
  | 0 => RUBase Minimal.EarnedGeneric.PZero
  | 1 => RUBase Minimal.EarnedGeneric.PEven
  | 2 => RUBase (Minimal.EarnedGeneric.PGe c)
  | _ => RURun c
  end.

Definition rlz_mk_pctr (n : nat) : rlz_ctr := if Nat.eqb n 0 then RCA else RCB.

(* A guest instruction of U_P (priced, universal properties). *)
Definition rlz_mk_pguest (op a b c : nat) : rlz_pinstr :=
  match op with
  | 0 => PINC (rlz_mk_pctr a)
  | 1 => PDEC (rlz_mk_pctr a) b
  | 3 => PCHECK (rlz_mk_uprop b c) (rlz_mk_pctr a)
  | 4 => PCOMMIT (rlz_mk_uprop b c) (rlz_mk_pctr a)
  | 5 => PCERTIFY
  | 6 => PPAY
  | _ => PHALT
  end.

Definition rlz_mk_pslot (op a b c : nat) : @Minimal.EarnedMultiPriced.pu_instr Kernel.UniversalPCodes.pu_hprop :=
  match op with
  | 0 => Minimal.EarnedMultiPriced.INC a
  | 1 => Minimal.EarnedMultiPriced.DEC a b
  | 3 => Minimal.EarnedMultiPriced.CHECK Kernel.UniversalPCodes.PSlot a
  | 4 => Minimal.EarnedMultiPriced.COMMIT Kernel.UniversalPCodes.PSlot a
  | 5 => Minimal.EarnedMultiPriced.CERTIFY
  | 6 => Minimal.EarnedMultiPriced.PAY
  | _ => Minimal.EarnedMultiPriced.HALT
  end.

(* The registers of a start state: a list of (register, value) pairs;
   every other register is 0. *)
Fixpoint rlz_mk_regs (l : list (nat * nat)) (r : nat) : nat :=
  match l with
  | [] => 0
  | (q, v) :: t => if Nat.eqb q r then v else rlz_mk_regs t r
  end.

(* Output: a state as a flat list of numbers. The layouts are those
   of thiele_small/flat.py. *)
Definition b2n (b : bool) : nat := if b then 1 else 0.

Definition rlz_view_eprop (p : Minimal.EarnedCore.prop) : nat * nat :=
  match p with Minimal.EarnedCore.PZero => (0, 0) | Minimal.EarnedCore.PEven => (1, 0) | Minimal.EarnedCore.PGe n => (2, n) end.

Definition rlz_view_ctr (c : Minimal.EarnedCore.ctr) : nat := match c with Minimal.EarnedCore.CA => 0 | Minimal.EarnedCore.CB => 1 end.

(* a fact as four numbers: property kind, property parameter, counter or
   register, version *)
Definition rlz_view_efact (f : Minimal.EarnedCore.fact) : list nat :=
  let (k, n) := rlz_view_eprop (Minimal.EarnedCore.f_prop f) in
  [k; n; rlz_view_ctr (Minimal.EarnedCore.f_ctr f); Minimal.EarnedCore.f_ver f].

Definition rlz_view_mfact (f : @Minimal.EarnedMulti.fact Minimal.EarnedCore.prop) : list nat :=
  let (k, n) := rlz_view_eprop (Minimal.EarnedMulti.f_prop f) in [k; n; Minimal.EarnedMulti.f_reg f; Minimal.EarnedMulti.f_ver f].

Definition rlz_view_pmfact (f : @Minimal.EarnedMultiPriced.pu_fact Minimal.EarnedCore.prop) : list nat :=
  let (k, n) := rlz_view_eprop (Minimal.EarnedMultiPriced.f_prop f) in [k; n; Minimal.EarnedMultiPriced.f_reg f; Minimal.EarnedMultiPriced.f_ver f].

Definition rlz_view_slotfact (f : @Minimal.EarnedMulti.fact Minimal.UniversalCodes.hprop) : list nat :=
  [0; 0; Minimal.EarnedMulti.f_reg f; Minimal.EarnedMulti.f_ver f].

Definition rlz_view_pslotfact (f : @Minimal.EarnedMultiPriced.pu_fact Kernel.UniversalPCodes.pu_hprop) : list nat :=
  [0; 0; Minimal.EarnedMultiPriced.f_reg f; Minimal.EarnedMultiPriced.f_ver f].

Definition rlz_view_chan {A : Type} (v : A -> list nat) (c : option A) : list nat :=
  match c with None => [0] | Some f => 1 :: v f end.

Definition rlz_view_facts {A : Type} (v : A -> list nat) (l : list A) : list nat :=
  length l :: flat_map v l.

(* pc, ca, cb, va, vb, err, mu, cert, channel, facts *)
Definition rlz_view_small (s : Minimal.EarnedCore.state) : list nat :=
  let k := Minimal.EarnedCore.core_of s in
  [Minimal.EarnedCore.pc k; Minimal.EarnedCore.ca k; Minimal.EarnedCore.cb k; Minimal.EarnedCore.va k; Minimal.EarnedCore.vb k; b2n (Minimal.EarnedCore.err k);
   Minimal.EarnedCore.mu s; b2n (Minimal.EarnedCore.cert s)]
  ++ rlz_view_chan rlz_view_efact (Minimal.EarnedCore.chan k)
  ++ rlz_view_facts rlz_view_efact (Minimal.EarnedCore.facts k).

(* pc, err, mu, cert, channel, facts, nregs, values of 0..nregs-1,
   versions of 0..nregs-1 *)
Definition rlz_view_regs (n : nat) (vals vers : nat -> nat) : list nat :=
  n :: map vals (seq 0 n) ++ map vers (seq 0 n).

Definition rlz_view_multi (n : nat) (s : @Minimal.EarnedMulti.state Minimal.EarnedCore.prop) : list nat :=
  let k := Minimal.EarnedMulti.core_of s in
  [Minimal.EarnedMulti.pc k; b2n (Minimal.EarnedMulti.err k); Minimal.EarnedMulti.mu s; b2n (Minimal.EarnedMulti.cert s)]
  ++ rlz_view_chan rlz_view_mfact (Minimal.EarnedMulti.chan k)
  ++ rlz_view_facts rlz_view_mfact (Minimal.EarnedMulti.facts k)
  ++ rlz_view_regs n (Minimal.EarnedMulti.vals k) (Minimal.EarnedMulti.vers k).

Definition rlz_view_pmulti (n : nat) (s : @Minimal.EarnedMultiPriced.pu_state Minimal.EarnedCore.prop) : list nat :=
  let k := Minimal.EarnedMultiPriced.core_of s in
  [Minimal.EarnedMultiPriced.pc k; b2n (Minimal.EarnedMultiPriced.err k); Minimal.EarnedMultiPriced.mu s; b2n (Minimal.EarnedMultiPriced.cert s)]
  ++ rlz_view_chan rlz_view_pmfact (Minimal.EarnedMultiPriced.chan k)
  ++ rlz_view_facts rlz_view_pmfact (Minimal.EarnedMultiPriced.facts k)
  ++ rlz_view_regs n (Minimal.EarnedMultiPriced.vals k) (Minimal.EarnedMultiPriced.vers k).

Definition rlz_view_slot (n : nat) (s : @Minimal.EarnedMulti.state Minimal.UniversalCodes.hprop) : list nat :=
  let k := Minimal.EarnedMulti.core_of s in
  [Minimal.EarnedMulti.pc k; b2n (Minimal.EarnedMulti.err k); Minimal.EarnedMulti.mu s; b2n (Minimal.EarnedMulti.cert s)]
  ++ rlz_view_chan rlz_view_slotfact (Minimal.EarnedMulti.chan k)
  ++ rlz_view_facts rlz_view_slotfact (Minimal.EarnedMulti.facts k)
  ++ rlz_view_regs n (Minimal.EarnedMulti.vals k) (Minimal.EarnedMulti.vers k).

Definition rlz_view_pslot (n : nat) (s : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop) : list nat :=
  let k := Minimal.EarnedMultiPriced.core_of s in
  [Minimal.EarnedMultiPriced.pc k; b2n (Minimal.EarnedMultiPriced.err k);
   Minimal.EarnedMultiPriced.mu s; b2n (Minimal.EarnedMultiPriced.cert s)]
  ++ rlz_view_chan rlz_view_pslotfact (Minimal.EarnedMultiPriced.chan k)
  ++ rlz_view_facts rlz_view_pslotfact (Minimal.EarnedMultiPriced.facts k)
  ++ rlz_view_regs n (Minimal.EarnedMultiPriced.vals k) (Minimal.EarnedMultiPriced.vers k).

(* Whether a program has stopped, as a bool. *)
Definition rlz_stopped_small (P : list Minimal.EarnedCore.instr) (s : Minimal.EarnedCore.state) : bool :=
  match Minimal.EarnedCore.next_instr P (Minimal.EarnedCore.core_of s) with None => true | Some _ => false end.

Definition rlz_stopped_multi (P : list (@Minimal.EarnedMulti.instr Minimal.EarnedCore.prop)) (s : @Minimal.EarnedMulti.state Minimal.EarnedCore.prop) : bool :=
  match Minimal.EarnedMulti.next_instr P (Minimal.EarnedMulti.core_of s) with None => true | Some _ => false end.

Definition rlz_stopped_pmulti (P : list (@Minimal.EarnedMultiPriced.pu_instr Minimal.EarnedCore.prop)) (s : @Minimal.EarnedMultiPriced.pu_state Minimal.EarnedCore.prop) : bool :=
  match Minimal.EarnedMultiPriced.pu_next_instr P (Minimal.EarnedMultiPriced.core_of s) with None => true | Some _ => false end.

Definition rlz_stopped_slot (P : list (@Minimal.EarnedMulti.instr Minimal.UniversalCodes.hprop)) (s : @Minimal.EarnedMulti.state Minimal.UniversalCodes.hprop) : bool :=
  match Minimal.EarnedMulti.next_instr P (Minimal.EarnedMulti.core_of s) with None => true | Some _ => false end.

Definition rlz_stopped_pslot (P : list (@Minimal.EarnedMultiPriced.pu_instr Kernel.UniversalPCodes.pu_hprop))
  (s : @Minimal.EarnedMultiPriced.pu_state Kernel.UniversalPCodes.pu_hprop) : bool :=
  match Minimal.EarnedMultiPriced.pu_next_instr P (Minimal.EarnedMultiPriced.core_of s) with
  | None => true | Some _ => false end.

(* ================================================================= *)
(* Extraction settings.                                               *)
(* ================================================================= *)

Extraction Language OCaml.
Extraction Blacklist List Nat Bool String Option Z Big_int Int.

Extract Inductive bool => "bool" ["true" "false"].
Extract Inductive option => "option" ["Some" "None"].
Extract Inductive unit => "unit" ["()"].
Extract Inductive list => "list" ["[]" "(::)"].
Extract Inductive prod => "( * )" [""].
Extract Inductive sumbool => "bool" ["true" "false"].
Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

Extract Inductive Minimal.UniversalCodes.hprop => "unit" ["()"].
Extract Inductive Kernel.UniversalPCodes.pu_hprop => "unit" ["()"].

Extract Inductive nat => "Z.t" ["Z.zero" "Z.succ"]
  "(fun fO fS n -> if Z.sign n <= 0 then fO () else fS (Z.pred n))".
(* plus, mult, minus are the names under which Coq elaborates + * - ; Nat.add,
   Nat.mul, Nat.sub are the same functions under their own names, and the
   extraction tables are keyed by the name, so both are given. *)
Extract Constant plus => "Z.add".
Extract Constant mult => "Z.mul".
Extract Constant minus => "(fun n m -> Z.max Z.zero (Z.sub n m))".
Extract Constant Nat.add => "Z.add".
Extract Constant Nat.mul => "Z.mul".
Extract Constant Nat.sub => "(fun n m -> Z.max Z.zero (Z.sub n m))".
Extract Constant Nat.eqb => "Z.equal".
Extract Constant Nat.leb => "Z.leq".
Extract Constant Nat.ltb => "Z.lt".
Extract Constant Nat.pow => "(fun a b -> Z.pow a (Z.to_int b))".
Extract Constant Nat.div => "(fun a b -> if Z.equal b Z.zero then Z.zero else Z.div a b)".
Extract Constant Nat.modulo => "(fun a b -> if Z.equal b Z.zero then a else Z.rem a b)".
Extract Constant Nat.div2 => "(fun n -> Z.div n (Z.of_int 2))".
Extract Constant Nat.even => "(fun n -> Z.equal (Z.rem n (Z.of_int 2)) Z.zero)".
Extract Constant Nat.odd => "(fun n -> not (Z.equal (Z.rem n (Z.of_int 2)) Z.zero))".
Extract Constant Peano_dec.eq_nat_dec => "Z.equal".
Extract Constant Nat.eq_dec => "Z.equal".

(* nat and the arithmetic above are the only substitutions. Everything
   else, including fact, iter, the prime search and the machines, is
   extracted from its Coq definition. *)

Extraction "realize_extracted.ml"
  rlz_mk_small rlz_mk_multi rlz_mk_pmulti rlz_mk_slot rlz_mk_pslot rlz_mk_pguest
  rlz_mk_regs
  rlz_view_small rlz_view_multi rlz_view_pmulti rlz_view_slot rlz_view_pslot
  rlz_stopped_small rlz_stopped_multi rlz_stopped_pmulti rlz_stopped_slot
  rlz_stopped_pslot
  rlz_small_exec rlz_small_run rlz_small_step rlz_small_run_prog
  rlz_small_trace_of rlz_small_compile rlz_small_start
  rlz_multi_exec rlz_multi_run rlz_multi_step rlz_multi_run_prog
  rlz_multi_trace_of rlz_multi_start
  rlz_pmulti_exec rlz_pmulti_run rlz_pmulti_step rlz_pmulti_run_prog
  rlz_pmulti_trace_of rlz_pmulti_start
  rlz_host_prop_eqb rlz_host_eval rlz_host_exec rlz_host_run
  rlz_host_step rlz_host_run_prog rlz_host_trace_of rlz_host_start
  rlz_host_program rlz_host_load rlz_prog_code rlz_pair
  rlz_unpair rlz_host_at rlz_guest_at
  rlz_qs rlz_nxtprime rlz_ueval rlz_pu_heval rlz_pu_prog_code
  rlz_phost_prop_eqb rlz_phost_exec rlz_phost_run rlz_phost_step
  rlz_phost_run_prog rlz_phost_trace_of rlz_phost_start rlz_phost_program
  rlz_phost_load rlz_phost_at.

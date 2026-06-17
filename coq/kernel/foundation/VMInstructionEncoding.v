(** VMInstructionEncoding.v — Gödel encoding from [list vm_instruction] to [nat].

    Closeout-plan B.3. The substrate-level structural-undecidability theorem
    is proved at the [nat]-program substrate (see NatSubstrateInstance.v).
    To carry the impossibility back to the 51-opcode VM as a corollary, we
    need a concrete, total injection [list vm_instruction → nat] with a
    proven left inverse. This file provides exactly that, by composing
    the existing [list bool] encoders from VMEncoding.v with a standard
    [list bool ↔ nat] bijection through Coq's [positive] type.

    What this file delivers, no Hypothesis or Axiom:

      - encode_vm_instruction : vm_instruction -> list bool
      - decode_vm_instruction : list bool -> option (vm_instruction * list bool)
      - decode_vm_instruction_correct : round-trip
      - encode_program : list vm_instruction -> list bool
      - decode_program : list bool -> option (list vm_instruction * list bool)
      - decode_program_correct : round-trip
      - bools_to_nat / nat_to_bools : bijection through positive
      - program_to_nat : list vm_instruction -> nat
      - nat_to_program : nat -> list vm_instruction
      - nat_to_program_program_to_nat : nat_to_program (program_to_nat p) = p
*)

From Coq Require Import List Bool Arith.PeanoNat NArith PArith Lia.
Import ListNotations.
Local Open Scope list_scope.

From Kernel Require Import VMState VMStep VMEncoding.

(** ** Per-instruction binary encoding (51 constructors)

    Each constructor gets a unique [nat] tag (0..50) followed by the
    encoded arguments, in declaration order. Decoding reads the tag,
    dispatches to the corresponding case, and decodes the arguments. *)

Definition encode_vm_instruction (i : vm_instruction) : list bool :=
  match i with
  | instr_pnew region mu_delta =>
      encode_nat 0 ++ encode_nat_list region ++ encode_nat mu_delta
  | instr_psplit m l r mu_delta =>
      encode_nat 1 ++ encode_nat m ++ encode_nat_list l ++ encode_nat_list r ++ encode_nat mu_delta
  | instr_pmerge m1 m2 mu_delta =>
      encode_nat 2 ++ encode_nat m1 ++ encode_nat m2 ++ encode_nat mu_delta
  | instr_lassert f c k flen mu_delta =>
      encode_nat 3 ++ encode_nat f ++ encode_nat c ++ encode_bool k ++ encode_nat flen ++ encode_nat mu_delta
  | instr_ljoin c1 c2 mu_delta =>
      encode_nat 4 ++ encode_nat c1 ++ encode_nat c2 ++ encode_nat mu_delta
  | instr_mdlacc m mu_delta =>
      encode_nat 5 ++ encode_nat m ++ encode_nat mu_delta
  | instr_pdiscover m ev mu_delta =>
      encode_nat 6 ++ encode_nat m ++ encode_string_list ev ++ encode_nat mu_delta
  | instr_xfer d s mu_delta =>
      encode_nat 7 ++ encode_nat d ++ encode_nat s ++ encode_nat mu_delta
  | instr_load_imm d imm mu_delta =>
      encode_nat 8 ++ encode_nat d ++ encode_nat imm ++ encode_nat mu_delta
  | instr_load d r mu_delta =>
      encode_nat 9 ++ encode_nat d ++ encode_nat r ++ encode_nat mu_delta
  | instr_store r s mu_delta =>
      encode_nat 10 ++ encode_nat r ++ encode_nat s ++ encode_nat mu_delta
  | instr_add d r1 r2 mu_delta =>
      encode_nat 11 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_sub d r1 r2 mu_delta =>
      encode_nat 12 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_jump t mu_delta =>
      encode_nat 13 ++ encode_nat t ++ encode_nat mu_delta
  | instr_jnez r t mu_delta =>
      encode_nat 14 ++ encode_nat r ++ encode_nat t ++ encode_nat mu_delta
  | instr_call t mu_delta =>
      encode_nat 15 ++ encode_nat t ++ encode_nat mu_delta
  | instr_ret mu_delta =>
      encode_nat 16 ++ encode_nat mu_delta
  | instr_chsh_trial x y a b mu_delta =>
      encode_nat 17 ++ encode_nat x ++ encode_nat y ++ encode_nat a ++ encode_nat b ++ encode_nat mu_delta
  | instr_xor_load d a mu_delta =>
      encode_nat 18 ++ encode_nat d ++ encode_nat a ++ encode_nat mu_delta
  | instr_xor_add d s mu_delta =>
      encode_nat 19 ++ encode_nat d ++ encode_nat s ++ encode_nat mu_delta
  | instr_xor_swap a b mu_delta =>
      encode_nat 20 ++ encode_nat a ++ encode_nat b ++ encode_nat mu_delta
  | instr_xor_rank d s mu_delta =>
      encode_nat 21 ++ encode_nat d ++ encode_nat s ++ encode_nat mu_delta
  | instr_emit m payload mu_delta =>
      encode_nat 22 ++ encode_nat m ++ encode_string payload ++ encode_nat mu_delta
  | instr_reveal m bits cert mu_delta =>
      encode_nat 23 ++ encode_nat m ++ encode_nat bits ++ encode_string cert ++ encode_nat mu_delta
  | instr_halt mu_delta =>
      encode_nat 24 ++ encode_nat mu_delta
  | instr_checkpoint label mu_delta =>
      encode_nat 25 ++ encode_string label ++ encode_nat mu_delta
  | instr_read_port d ch v bits mu_delta =>
      encode_nat 26 ++ encode_nat d ++ encode_nat ch ++ encode_nat v ++ encode_nat bits ++ encode_nat mu_delta
  | instr_write_port ch s mu_delta =>
      encode_nat 27 ++ encode_nat ch ++ encode_nat s ++ encode_nat mu_delta
  | instr_heap_load d r mu_delta =>
      encode_nat 28 ++ encode_nat d ++ encode_nat r ++ encode_nat mu_delta
  | instr_heap_store r s mu_delta =>
      encode_nat 29 ++ encode_nat r ++ encode_nat s ++ encode_nat mu_delta
  | instr_certify mu_delta =>
      encode_nat 30 ++ encode_nat mu_delta
  | instr_and d r1 r2 mu_delta =>
      encode_nat 31 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_or d r1 r2 mu_delta =>
      encode_nat 32 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_shl d r1 r2 mu_delta =>
      encode_nat 33 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_shr d r1 r2 mu_delta =>
      encode_nat 34 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_mul d r1 r2 mu_delta =>
      encode_nat 35 ++ encode_nat d ++ encode_nat r1 ++ encode_nat r2 ++ encode_nat mu_delta
  | instr_lui d imm mu_delta =>
      encode_nat 36 ++ encode_nat d ++ encode_nat imm ++ encode_nat mu_delta
  | instr_tensor_set m i j v mu_delta =>
      encode_nat 37 ++ encode_nat m ++ encode_nat i ++ encode_nat j ++ encode_nat v ++ encode_nat mu_delta
  | instr_tensor_get d m i j mu_delta =>
      encode_nat 38 ++ encode_nat d ++ encode_nat m ++ encode_nat i ++ encode_nat j ++ encode_nat mu_delta
  | instr_morph d sm dm c mu_delta =>
      encode_nat 39 ++ encode_nat d ++ encode_nat sm ++ encode_nat dm ++ encode_nat c ++ encode_nat mu_delta
  | instr_compose d m1 m2 mu_delta =>
      encode_nat 40 ++ encode_nat d ++ encode_nat m1 ++ encode_nat m2 ++ encode_nat mu_delta
  | instr_morph_id d m mu_delta =>
      encode_nat 41 ++ encode_nat d ++ encode_nat m ++ encode_nat mu_delta
  | instr_morph_delete mid mu_delta =>
      encode_nat 42 ++ encode_nat mid ++ encode_nat mu_delta
  | instr_morph_assert mid prop cert mu_delta =>
      encode_nat 43 ++ encode_nat mid ++ encode_string prop ++ encode_string cert ++ encode_nat mu_delta
  | instr_morph_tensor d f g mu_delta =>
      encode_nat 44 ++ encode_nat d ++ encode_nat f ++ encode_nat g ++ encode_nat mu_delta
  | instr_morph_get d mid sel mu_delta =>
      encode_nat 45 ++ encode_nat d ++ encode_nat mid ++ encode_nat sel ++ encode_nat mu_delta
  | instr_chsh_lassert mu_delta =>
      encode_nat 46 ++ encode_nat mu_delta
  | instr_chsh_lassert_1ab mu_delta =>
      encode_nat 47 ++ encode_nat mu_delta
  | instr_chsh_lassert_1ab_g5 mu_delta same_g5 diff_g5 =>
      encode_nat 48 ++ encode_nat mu_delta ++ encode_nat same_g5 ++ encode_nat diff_g5
  | instr_chsh_lassert_1ab_g345 mu_delta same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      encode_nat 49 ++ encode_nat mu_delta
        ++ encode_nat same_g3 ++ encode_nat diff_g3
        ++ encode_nat same_g4 ++ encode_nat diff_g4
        ++ encode_nat same_g5 ++ encode_nat diff_g5
  | instr_chsh_lassert_1ab_g12345 mu_delta same_g1 diff_g1 same_g2 diff_g2
                                     same_g3 diff_g3 same_g4 diff_g4 same_g5 diff_g5 =>
      encode_nat 50 ++ encode_nat mu_delta
        ++ encode_nat same_g1 ++ encode_nat diff_g1
        ++ encode_nat same_g2 ++ encode_nat diff_g2
        ++ encode_nat same_g3 ++ encode_nat diff_g3
        ++ encode_nat same_g4 ++ encode_nat diff_g4
        ++ encode_nat same_g5 ++ encode_nat diff_g5
  end.

(** Decoder. Reads the tag and dispatches; on tag mismatch returns None. *)

Definition decode_vm_instruction (bs : list bool)
  : option (vm_instruction * list bool) :=
  match decode_nat bs with
  | None => None
  | Some (tag, r0) =>
    match tag with
    | 0 =>
      match decode_nat_list r0 with Some (region, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_pnew region d, r2)
      | _ => None end | _ => None end
    | 1 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_nat_list r1 with Some (l, r2) =>
      match decode_nat_list r2 with Some (rr, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_psplit m l rr d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 2 =>
      match decode_nat r0 with Some (m1, r1) =>
      match decode_nat r1 with Some (m2, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_pmerge m1 m2 d, r3)
      | _ => None end | _ => None end | _ => None end
    | 3 =>
      match decode_nat r0 with Some (f, r1) =>
      match decode_nat r1 with Some (c, r2) =>
      match decode_bool r2 with Some (k, r3) =>
      match decode_nat r3 with Some (flen, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_lassert f c k flen d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 4 =>
      match decode_nat r0 with Some (c1, r1) =>
      match decode_nat r1 with Some (c2, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_ljoin c1 c2 d, r3)
      | _ => None end | _ => None end | _ => None end
    | 5 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_mdlacc m d, r2)
      | _ => None end | _ => None end
    | 6 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_string_list r1 with Some (ev, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_pdiscover m ev d, r3)
      | _ => None end | _ => None end | _ => None end
    | 7 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_xfer a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 8 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_load_imm a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 9 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_load a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 10 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_store a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 11 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_add a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 12 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_sub a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 13 =>
      match decode_nat r0 with Some (t, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_jump t d, r2)
      | _ => None end | _ => None end
    | 14 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_jnez a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 15 =>
      match decode_nat r0 with Some (t, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_call t d, r2)
      | _ => None end | _ => None end
    | 16 =>
      match decode_nat r0 with Some (d, r1) =>
        Some (instr_ret d, r1)
      | _ => None end
    | 17 =>
      match decode_nat r0 with Some (x, r1) =>
      match decode_nat r1 with Some (y, r2) =>
      match decode_nat r2 with Some (a, r3) =>
      match decode_nat r3 with Some (b, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_chsh_trial x y a b d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 18 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_xor_load a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 19 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_xor_add a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 20 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_xor_swap a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 21 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_xor_rank a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 22 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_string r1 with Some (p, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_emit m p d, r3)
      | _ => None end | _ => None end | _ => None end
    | 23 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_string r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_reveal m b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 24 =>
      match decode_nat r0 with Some (d, r1) =>
        Some (instr_halt d, r1)
      | _ => None end
    | 25 =>
      match decode_string r0 with Some (l, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_checkpoint l d, r2)
      | _ => None end | _ => None end
    | 26 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (e, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_read_port a b c e d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 27 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_write_port a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 28 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_heap_load a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 29 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_heap_store a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 30 =>
      match decode_nat r0 with Some (d, r1) =>
        Some (instr_certify d, r1)
      | _ => None end
    | 31 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_and a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 32 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_or a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 33 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_shl a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 34 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_shr a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 35 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_mul a b c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 36 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (b, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_lui a b d, r3)
      | _ => None end | _ => None end | _ => None end
    | 37 =>
      match decode_nat r0 with Some (m, r1) =>
      match decode_nat r1 with Some (i, r2) =>
      match decode_nat r2 with Some (j, r3) =>
      match decode_nat r3 with Some (v, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_tensor_set m i j v d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 38 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (m, r2) =>
      match decode_nat r2 with Some (i, r3) =>
      match decode_nat r3 with Some (j, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_tensor_get a m i j d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 39 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (sm, r2) =>
      match decode_nat r2 with Some (dm, r3) =>
      match decode_nat r3 with Some (c, r4) =>
      match decode_nat r4 with Some (d, r5) =>
        Some (instr_morph a sm dm c d, r5)
      | _ => None end | _ => None end | _ => None end | _ => None end | _ => None end
    | 40 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (m1, r2) =>
      match decode_nat r2 with Some (m2, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_compose a m1 m2 d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 41 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (m, r2) =>
      match decode_nat r2 with Some (d, r3) =>
        Some (instr_morph_id a m d, r3)
      | _ => None end | _ => None end | _ => None end
    | 42 =>
      match decode_nat r0 with Some (mid, r1) =>
      match decode_nat r1 with Some (d, r2) =>
        Some (instr_morph_delete mid d, r2)
      | _ => None end | _ => None end
    | 43 =>
      match decode_nat r0 with Some (mid, r1) =>
      match decode_string r1 with Some (p, r2) =>
      match decode_string r2 with Some (c, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_morph_assert mid p c d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 44 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (f, r2) =>
      match decode_nat r2 with Some (g, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_morph_tensor a f g d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 45 =>
      match decode_nat r0 with Some (a, r1) =>
      match decode_nat r1 with Some (mid, r2) =>
      match decode_nat r2 with Some (sel, r3) =>
      match decode_nat r3 with Some (d, r4) =>
        Some (instr_morph_get a mid sel d, r4)
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 46 =>
      match decode_nat r0 with Some (d, r1) =>
        Some (instr_chsh_lassert d, r1)
      | _ => None end
    | 47 =>
      match decode_nat r0 with Some (d, r1) =>
        Some (instr_chsh_lassert_1ab d, r1)
      | _ => None end
    | 48 =>
      match decode_nat r0 with Some (d, r1) =>
      match decode_nat r1 with Some (sg, r2) =>
      match decode_nat r2 with Some (dg, r3) =>
        Some (instr_chsh_lassert_1ab_g5 d sg dg, r3)
      | _ => None end | _ => None end | _ => None end
    | 49 =>
      match decode_nat r0 with Some (d, r1) =>
      match decode_nat r1 with Some (sg3, r2) =>
      match decode_nat r2 with Some (dg3, r3) =>
      match decode_nat r3 with Some (sg4, r4) =>
      match decode_nat r4 with Some (dg4, r5) =>
      match decode_nat r5 with Some (sg5, r6) =>
      match decode_nat r6 with Some (dg5, r7) =>
        Some (instr_chsh_lassert_1ab_g345 d sg3 dg3 sg4 dg4 sg5 dg5, r7)
      | _ => None end | _ => None end | _ => None end
      | _ => None end | _ => None end | _ => None end | _ => None end
    | 50 =>
      match decode_nat r0 with Some (d, r1) =>
      match decode_nat r1 with Some (sg1, r2) =>
      match decode_nat r2 with Some (dg1, r3) =>
      match decode_nat r3 with Some (sg2, r4) =>
      match decode_nat r4 with Some (dg2, r5) =>
      match decode_nat r5 with Some (sg3, r6) =>
      match decode_nat r6 with Some (dg3, r7) =>
      match decode_nat r7 with Some (sg4, r8) =>
      match decode_nat r8 with Some (dg4, r9) =>
      match decode_nat r9 with Some (sg5, r10) =>
      match decode_nat r10 with Some (dg5, r11) =>
        Some (instr_chsh_lassert_1ab_g12345 d sg1 dg1 sg2 dg2 sg3 dg3 sg4 dg4 sg5 dg5, r11)
      | _ => None end | _ => None end | _ => None end | _ => None end
      | _ => None end | _ => None end | _ => None end | _ => None end
      | _ => None end | _ => None end | _ => None end
    | _ => None
    end
  end.

(** ** Round-trip lemma for instructions.

    The proof is mechanical: each constructor case unfolds the encoder,
    pushes the [++] association so the leading bytes are exposed, applies
    the appropriate primitive [decode_X_correct] lemma, and reduces. The
    [decode_chain] tactic discharges all 51 cases uniformly. *)

Ltac decode_chain :=
  rewrite <- ?app_assoc;
  repeat (
    first
      [ rewrite decode_nat_correct
      | rewrite decode_bool_correct
      | rewrite decode_string_correct
      | rewrite decode_nat_list_correct
      | rewrite decode_string_list_correct ];
    cbn [decode_vm_instruction]).

Lemma decode_vm_instruction_correct :
  forall i rest,
    decode_vm_instruction (encode_vm_instruction i ++ rest) = Some (i, rest).
Proof.
  intros i rest.
  destruct i; cbn [encode_vm_instruction];
    unfold decode_vm_instruction;
    decode_chain; reflexivity.
Qed.

(** ** Encoding for [list vm_instruction] *)

Definition encode_program (p : list vm_instruction) : list bool :=
  encode_list encode_vm_instruction p.

Definition decode_program (bs : list bool)
  : option (list vm_instruction * list bool) :=
  decode_sequence decode_vm_instruction bs.

Lemma decode_program_correct :
  forall p rest,
    decode_program (encode_program p ++ rest) = Some (p, rest).
Proof.
  intros p rest.
  unfold decode_program, encode_program.
  apply decode_sequence_correct.
  apply decode_vm_instruction_correct.
Qed.

(** ** [list bool] ↔ [positive] bijection.

    Uses the standard structural bijection: each [bool] becomes one
    binary digit of a [positive] (with the trailing [xH] marker). This
    is a total bijection: every [list bool] maps to a unique [positive]
    and back. *)

Fixpoint bools_to_pos (bs : list bool) : positive :=
  match bs with
  | [] => xH
  | false :: rest => xO (bools_to_pos rest)
  | true :: rest => xI (bools_to_pos rest)
  end.

Fixpoint pos_to_bools (p : positive) : list bool :=
  match p with
  | xH => []
  | xO p' => false :: pos_to_bools p'
  | xI p' => true :: pos_to_bools p'
  end.

Lemma pos_to_bools_to_pos :
  forall bs, pos_to_bools (bools_to_pos bs) = bs.
Proof.
  induction bs as [|b bs IH]; simpl.
  - reflexivity.
  - destruct b; simpl; rewrite IH; reflexivity.
Qed.

Lemma bools_to_pos_to_bools :
  forall p, bools_to_pos (pos_to_bools p) = p.
Proof.
  induction p; simpl; rewrite ?IHp; reflexivity.
Qed.

(** ** [list bool] ↔ [nat] through [positive].

    [bools_to_nat] always returns a positive nat (≥ 1) because
    [bools_to_pos] always returns a positive. [nat_to_bools] returns
    [[]] on the input 0, which is outside the image — the round-trip
    holds in the direction we need. *)

Definition bools_to_nat (bs : list bool) : nat :=
  Pos.to_nat (bools_to_pos bs).

Definition nat_to_bools (n : nat) : list bool :=
  match n with
  | 0 => []
  | S _ => pos_to_bools (Pos.of_nat n)
  end.

Lemma bools_to_nat_pos :
  forall bs, bools_to_nat bs > 0.
Proof.
  intros bs. unfold bools_to_nat. apply Pos2Nat.is_pos.
Qed.

Lemma nat_to_bools_to_nat :
  forall bs, nat_to_bools (bools_to_nat bs) = bs.
Proof.
  intros bs.
  pose proof (bools_to_nat_pos bs) as Hpos.
  unfold nat_to_bools, bools_to_nat.
  destruct (Pos.to_nat (bools_to_pos bs)) as [|n] eqn:Hn.
  - lia.
  - assert (Pos.of_nat (S n) = bools_to_pos bs) as Heq.
    { rewrite <- Hn. apply Pos2Nat.id. }
    rewrite Heq. apply pos_to_bools_to_pos.
Qed.

(** ** Composition: [list vm_instruction] ↔ [nat]

    These are the primary deliverables of B.3: a Coq function from
    programs to natural numbers (Gödel encoding) and a left inverse. *)

Definition program_to_nat (p : list vm_instruction) : nat :=
  bools_to_nat (encode_program p).

Definition nat_to_program (n : nat) : list vm_instruction :=
  match decode_program (nat_to_bools n) with
  | Some (p, _) => p
  | None => []
  end.

(** The round-trip lemma. This is the load-bearing fact downstream:
    every program can be recovered from its nat code. *)

Theorem nat_to_program_program_to_nat :
  forall p, nat_to_program (program_to_nat p) = p.
Proof.
  intros p. unfold nat_to_program, program_to_nat.
  rewrite nat_to_bools_to_nat.
  pose proof (decode_program_correct p []) as Hdec.
  rewrite app_nil_r in Hdec.
  rewrite Hdec. reflexivity.
Qed.

(** [program_to_nat] is injective. *)

Corollary program_to_nat_injective :
  forall p1 p2,
    program_to_nat p1 = program_to_nat p2 ->
    p1 = p2.
Proof.
  intros p1 p2 Heq.
  rewrite <- (nat_to_program_program_to_nat p1).
  rewrite <- (nat_to_program_program_to_nat p2).
  rewrite Heq. reflexivity.
Qed.

(** ** Cost-foundation connectivity.

    The encoding above is a syntactic operation; it does not change
    the program's [instruction_cost] under [vm_mu]. The corollary
    below ties this file to the cost foundation by reading off the
    invariant: round-tripping a program through [program_to_nat] /
    [nat_to_program] preserves the per-instruction cost ledger. *)
Lemma program_to_nat_preserves_instruction_cost :
  forall (p : list vm_instruction),
    map instruction_cost (nat_to_program (program_to_nat p))
      = map instruction_cost p.
Proof.
  intros p. rewrite nat_to_program_program_to_nat. reflexivity.
Qed.

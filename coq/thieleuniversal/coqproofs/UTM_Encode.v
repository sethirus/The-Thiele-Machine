Require Import ThieleUniversal.TM.
From ThieleUniversal Require Import CPU.
Require Import List.
Require Import Nat.
Require Import ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

Module UTM_Encode.
  Import CPU.
  (* Encoding base used for packing instruction operands into a single word. *)
  Definition ENC_BASE := 1024.

  (* Encode/decode small head moves. *)
  Definition encode_z (z : Z) : nat := match z with | (-1)%Z => 0 | 0%Z => 1 | 1%Z => 2 | _ => 1 end.
  Definition decode_z (n : nat) : Z := match n with | 0%nat => (-1)%Z | 1%nat => 0%Z | 2%nat => 1%Z | _ => 0%Z end.

  (* Flatten rules into a memory image. *)
  Definition encode_rule r := let '(q,s,q',w,m) := r in [q;s;q';w;encode_z m].
  Definition encode_rules := flat_map encode_rule.

  (* Encode a single instruction as three consecutive words in memory:
     [opcode; arg1; arg2]. This avoids heavy div/mod arithmetic during
     decoding because we perform simple nth lookups instead of division. *)
  Definition encode_instr_words (i:CPU.Instr) : list nat :=
    match i with
    | CPU.LoadConst rd v      => [0; rd; v; 0]
    | CPU.LoadIndirect rd ra  => [1; rd; ra; 0]
    | CPU.StoreIndirect ra rv => [2; ra; rv; 0]
    | CPU.CopyReg rd rs       => [3; rd; rs; 0]
    | CPU.AddConst rd v       => [4; rd; v; 0]
    | CPU.AddReg rd r1 r2     => [5; rd; r1; r2]
    | CPU.SubReg rd r1 r2     => [6; rd; r1; r2]
    | CPU.Jz rc target        => [7; rc; target; 0]
    | CPU.Jnz rc target       => [8; rc; target; 0]
    | CPU.Halt                => [9; 0; 0; 0]
    end.

  (* Decode an instruction from the memory image. Read three consecutive
     cells starting at PC: opcode, arg1, arg2. This is deliberately
     simple: no divisions, just nth lookups and pattern matching. *)
  Definition decode_instr_from_mem (mem : list nat) (pc : nat) : CPU.Instr :=
    let opcode := nth pc mem 0 in
    let arg1 := nth (pc + 1) mem 0 in
    let arg2 := nth (pc + 2) mem 0 in
    let arg3 := nth (pc + 3) mem 0 in
    match opcode with
    | 0 => CPU.LoadConst arg1 arg2
    | 1 => CPU.LoadIndirect arg1 arg2
    | 2 => CPU.StoreIndirect arg1 arg2
    | 3 => CPU.CopyReg arg1 arg2
    | 4 => CPU.AddConst arg1 arg2
    | 5 => CPU.AddReg arg1 arg2 arg3
    | 6 => CPU.SubReg arg1 arg2 arg3
    | 7 => CPU.Jz arg1 arg2
    | 8 => CPU.Jnz arg1 arg2
    | _ => CPU.Halt
    end.

  (** Every encoded instruction assumes its operands fit within [ENC_BASE]. *)
  Definition instr_small (i : CPU.Instr) : Prop :=
    match i with
    | CPU.LoadConst rd v | CPU.LoadIndirect rd v | CPU.CopyReg rd v | CPU.AddConst rd v
    | CPU.Jz rd v | CPU.Jnz rd v => rd < ENC_BASE /\ v < ENC_BASE
    | CPU.StoreIndirect ra rv => ra < ENC_BASE /\ rv < ENC_BASE
    | CPU.AddReg rd r1 r2 | CPU.SubReg rd r1 r2 =>
        rd < ENC_BASE /\ r1 < ENC_BASE /\ r2 < ENC_BASE
    | CPU.Halt => True
    end.

  (** Decoding an encoded instruction yields the original instruction.
      To reduce per-proof memory pressure we split the arithmetic-heavy
      cases into smaller lemmas and then dispatch on the instruction
      shape. *)
  Lemma decode_encode_LoadConst : forall rd v, instr_small (LoadConst rd v) ->
    decode_instr_from_mem (encode_instr_words (LoadConst rd v)) 0 = LoadConst rd v.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_LoadIndirect : forall rd v, instr_small (LoadIndirect rd v) ->
    decode_instr_from_mem (encode_instr_words (LoadIndirect rd v)) 0 = LoadIndirect rd v.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_StoreIndirect : forall ra rv, instr_small (StoreIndirect ra rv) ->
    decode_instr_from_mem (encode_instr_words (StoreIndirect ra rv)) 0 = StoreIndirect ra rv.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_CopyReg : forall rd rs, instr_small (CopyReg rd rs) ->
    decode_instr_from_mem (encode_instr_words (CopyReg rd rs)) 0 = CopyReg rd rs.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_AddConst : forall rd v, instr_small (AddConst rd v) ->
    decode_instr_from_mem (encode_instr_words (AddConst rd v)) 0 = AddConst rd v.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_AddReg : forall rd r1 r2, instr_small (AddReg rd r1 r2) ->
    decode_instr_from_mem (encode_instr_words (AddReg rd r1 r2)) 0 = AddReg rd r1 r2.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_SubReg : forall rd r1 r2, instr_small (SubReg rd r1 r2) ->
    decode_instr_from_mem (encode_instr_words (SubReg rd r1 r2)) 0 = SubReg rd r1 r2.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_Jz : forall rc target, instr_small (Jz rc target) ->
    decode_instr_from_mem (encode_instr_words (Jz rc target)) 0 = Jz rc target.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_Jnz : forall rc target, instr_small (Jnz rc target) ->
    decode_instr_from_mem (encode_instr_words (Jnz rc target)) 0 = Jnz rc target.
  Proof. intros; cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_Halt : decode_instr_from_mem (encode_instr_words Halt) 0 = Halt.
  Proof. cbv [encode_instr_words decode_instr_from_mem ENC_BASE]; simpl; reflexivity. Qed.

  Lemma decode_encode_roundtrip :
    forall i, instr_small i -> decode_instr_from_mem (encode_instr_words i) 0 = i.
  Proof.
    intros i Hs.
    destruct i as
      [rd val | rd ra | ra rv | rd rs | rd val' | rd rs1 rs2
       | rd rs1 rs2 | rc target | rc target |]; simpl in *; try reflexivity;
    try now (apply decode_encode_LoadConst; assumption);
    try now (apply decode_encode_LoadIndirect; assumption);
    try now (apply decode_encode_StoreIndirect; assumption);
    try now (apply decode_encode_CopyReg; assumption);
    try now (apply decode_encode_AddConst; assumption);
    try now (apply decode_encode_AddReg; assumption);
    try now (apply decode_encode_SubReg; assumption);
    try now (apply decode_encode_Jz; assumption);
    try now (apply decode_encode_Jnz; assumption);
    try now apply decode_encode_Halt.
   Qed.
End UTM_Encode.

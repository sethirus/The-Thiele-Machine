(** VMSelfProgram.v: B3, part 2: the fixed host program U of the uniform
    self-interpreter, and its phase lemmas under actual [run_vm_u].

    Host register roles:
      R0..R3  guest registers (unbounded values)
      R4, R5  values of the guest rs1 / rs2 registers
      R6      result value to write back
      R7      scratch (field indices, opcode, cost)
      R8      the fetched guest word
      R9      status: 0 running, 1 guest terminated, 2 malformed word
      R10     the constant 1
      R11     the guest ledger (the simulated guest's [vm_mu])
      R12     guest program counter
      R13     per-instruction bit width of the packed code
      R14     packed guest code
      R15     scratch (field masks)
    Every host instruction has cost 0, so the host's own [vm_mu] is never
    changed by U; the guest ledger lives only in R11.

    Layout (addresses):
      0..6     fetch the guest word into R8
      7..38    read guest rs1 into R4 and rs2 into R5 (four-way branches)
      39..40   extract the opcode into R7
      41..43   opcode 0 (no instruction at guest pc): status 1, leave U
      44..96   dispatch chain, opcodes 1..12
      97..98   opcodes 13..15: status 2, leave U
      99..114  write R6 into guest register dst (four-way branch)
      115      guest pc := guest pc + 1
      116..121 guest ledger += cost; next guest instruction
    "Leave U" is a jump to address 122 = length U, which is the VM's own
    termination condition for the host run.

    The listing is produced by a small generator kept with the B3 evidence;
    its exact contents are fixed here and every property below is proved
    about this literal list. *)

From Coq Require Import Arith Lia List.
From Coq Require Import NArith.NArith.
Import ListNotations.
From Kernel Require Import VMState VMStep VMUnboundedStep.
From Kernel Require Import VMUnboundedInterpreterSlots VMUnboundedInterpreterCompose.
From Kernel Require Import VMSelfGuest.

Close Scope string_scope.
Open Scope list_scope.

Definition self_interpreter_program : list vm_instruction :=
  [ instr_xfer 7 12 0                 (*   0 FETCH; T := gpc *)
  ; instr_mul 7 7 13 0                (*   1 T := gpc*width *)
  ; instr_shr 8 14 7 0                (*   2 W := code >> shift *)
  ; instr_load_imm 10 1 0             (*   3 ONE := 1 *)
  ; instr_shl 7 10 13 0               (*   4 T := 2^width *)
  ; instr_sub 7 7 10 0                (*   5 T := word mask *)
  ; instr_and 8 8 7 0                 (*   6 W := guest word *)
  ; instr_load_imm 7 6 0              (*   7  *)
  ; instr_shr 7 8 7 0                 (*   8  *)
  ; instr_load_imm 15 3 0             (*   9  *)
  ; instr_and 7 7 15 0                (*  10 rs1 index *)
  ; instr_jnez 7 14 0                 (*  11  *)
  ; instr_xfer 4 0 0                  (*  12  *)
  ; instr_jump 23 0                   (*  13  *)
  ; instr_sub 7 7 10 0                (*  14  *)
  ; instr_jnez 7 18 0                 (*  15  *)
  ; instr_xfer 4 1 0                  (*  16  *)
  ; instr_jump 23 0                   (*  17  *)
  ; instr_sub 7 7 10 0                (*  18  *)
  ; instr_jnez 7 22 0                 (*  19  *)
  ; instr_xfer 4 2 0                  (*  20  *)
  ; instr_jump 23 0                   (*  21  *)
  ; instr_xfer 4 3 0                  (*  22  *)
  ; instr_load_imm 7 8 0              (*  23  *)
  ; instr_shr 7 8 7 0                 (*  24  *)
  ; instr_load_imm 15 3 0             (*  25  *)
  ; instr_and 7 7 15 0                (*  26 rs2 index *)
  ; instr_jnez 7 30 0                 (*  27  *)
  ; instr_xfer 5 0 0                  (*  28  *)
  ; instr_jump 39 0                   (*  29  *)
  ; instr_sub 7 7 10 0                (*  30  *)
  ; instr_jnez 7 34 0                 (*  31  *)
  ; instr_xfer 5 1 0                  (*  32  *)
  ; instr_jump 39 0                   (*  33  *)
  ; instr_sub 7 7 10 0                (*  34  *)
  ; instr_jnez 7 38 0                 (*  35  *)
  ; instr_xfer 5 2 0                  (*  36  *)
  ; instr_jump 39 0                   (*  37  *)
  ; instr_xfer 5 3 0                  (*  38  *)
  ; instr_load_imm 7 15 0             (*  39  *)
  ; instr_and 7 8 7 0                 (*  40 opcode *)
  ; instr_jnez 7 44 0                 (*  41  *)
  ; instr_load_imm 9 1 0              (*  42 status halted *)
  ; instr_jump 122 0                  (*  43  *)
  ; instr_sub 7 7 10 0                (*  44 D1 *)
  ; instr_jnez 7 47 0                 (*  45  *)
  ; instr_jump 115 0                  (*  46  *)
  ; instr_sub 7 7 10 0                (*  47 D2 *)
  ; instr_jnez 7 52 0                 (*  48  *)
  ; instr_load_imm 7 18 0             (*  49  *)
  ; instr_shr 6 8 7 0                 (*  50 C := imm *)
  ; instr_jump 99 0                   (*  51  *)
  ; instr_sub 7 7 10 0                (*  52 D3 *)
  ; instr_jnez 7 56 0                 (*  53  *)
  ; instr_xfer 6 4 0                  (*  54  *)
  ; instr_jump 99 0                   (*  55  *)
  ; instr_sub 7 7 10 0                (*  56 D4 *)
  ; instr_jnez 7 60 0                 (*  57  *)
  ; instr_add 6 4 5 0                 (*  58  *)
  ; instr_jump 99 0                   (*  59  *)
  ; instr_sub 7 7 10 0                (*  60 D5 *)
  ; instr_jnez 7 64 0                 (*  61  *)
  ; instr_sub 6 4 5 0                 (*  62  *)
  ; instr_jump 99 0                   (*  63  *)
  ; instr_sub 7 7 10 0                (*  64 D6 *)
  ; instr_jnez 7 68 0                 (*  65  *)
  ; instr_mul 6 4 5 0                 (*  66  *)
  ; instr_jump 99 0                   (*  67  *)
  ; instr_sub 7 7 10 0                (*  68 D7 *)
  ; instr_jnez 7 72 0                 (*  69  *)
  ; instr_and 6 4 5 0                 (*  70  *)
  ; instr_jump 99 0                   (*  71  *)
  ; instr_sub 7 7 10 0                (*  72 D8 *)
  ; instr_jnez 7 76 0                 (*  73  *)
  ; instr_or 6 4 5 0                  (*  74  *)
  ; instr_jump 99 0                   (*  75  *)
  ; instr_sub 7 7 10 0                (*  76 D9 *)
  ; instr_jnez 7 80 0                 (*  77  *)
  ; instr_shl 6 4 5 0                 (*  78  *)
  ; instr_jump 99 0                   (*  79  *)
  ; instr_sub 7 7 10 0                (*  80 D10 *)
  ; instr_jnez 7 84 0                 (*  81  *)
  ; instr_shr 6 4 5 0                 (*  82  *)
  ; instr_jump 99 0                   (*  83  *)
  ; instr_sub 7 7 10 0                (*  84 D11 *)
  ; instr_jnez 7 89 0                 (*  85  *)
  ; instr_load_imm 7 18 0             (*  86  *)
  ; instr_shr 12 8 7 0                (*  87 gpc := target *)
  ; instr_jump 116 0                  (*  88  *)
  ; instr_sub 7 7 10 0                (*  89 D12 *)
  ; instr_jnez 7 97 0                 (*  90  *)
  ; instr_jnez 4 94 0                 (*  91  *)
  ; instr_add 12 12 10 0              (*  92  *)
  ; instr_jump 116 0                  (*  93  *)
  ; instr_load_imm 7 18 0             (*  94 JTAKE *)
  ; instr_shr 12 8 7 0                (*  95  *)
  ; instr_jump 116 0                  (*  96  *)
  ; instr_load_imm 9 2 0              (*  97 MALF; status malformed *)
  ; instr_jump 122 0                  (*  98  *)
  ; instr_load_imm 7 4 0              (*  99 WRITE *)
  ; instr_shr 7 8 7 0                 (* 100  *)
  ; instr_load_imm 15 3 0             (* 101  *)
  ; instr_and 7 7 15 0                (* 102 dst index *)
  ; instr_jnez 7 106 0                (* 103  *)
  ; instr_xfer 0 6 0                  (* 104  *)
  ; instr_jump 115 0                  (* 105  *)
  ; instr_sub 7 7 10 0                (* 106  *)
  ; instr_jnez 7 110 0                (* 107  *)
  ; instr_xfer 1 6 0                  (* 108  *)
  ; instr_jump 115 0                  (* 109  *)
  ; instr_sub 7 7 10 0                (* 110  *)
  ; instr_jnez 7 114 0                (* 111  *)
  ; instr_xfer 2 6 0                  (* 112  *)
  ; instr_jump 115 0                  (* 113  *)
  ; instr_xfer 3 6 0                  (* 114  *)
  ; instr_add 12 12 10 0              (* 115 ADVPC; gpc++ *)
  ; instr_load_imm 7 10 0             (* 116 ADVMU *)
  ; instr_shr 7 8 7 0                 (* 117  *)
  ; instr_load_imm 15 255 0           (* 118  *)
  ; instr_and 7 7 15 0                (* 119 cost field *)
  ; instr_add 11 11 7 0               (* 120 guest ledger += cost *)
  ; instr_jump 0 0                    (* 121  *)
  ].

Definition U := self_interpreter_program.
Definition U_END : nat := 122.

Lemma U_length : length U = U_END.
Proof. reflexivity. Qed.

(** Host state: every non-register field comes from an ambient state, the
    host ledger is [hmu], and all sixteen registers are given explicitly. *)
Definition hst (amb : VMState) (hmu hpc : nat) (r : list nat) : VMState :=
  {| vm_graph := amb.(vm_graph); vm_csrs := amb.(vm_csrs);
     vm_regs := r; vm_mem := amb.(vm_mem); vm_pc := hpc; vm_mu := hmu;
     vm_mu_tensor := amb.(vm_mu_tensor); vm_err := amb.(vm_err);
     vm_logic_acc := amb.(vm_logic_acc); vm_mstatus := amb.(vm_mstatus);
     vm_witness := amb.(vm_witness); vm_certified := amb.(vm_certified) |}.

(** Smoke test on closed data: guest program [ADD r2 := r0 + r1 (cost 7)]
    with inputs 5 and 9 terminates with r2 = 14 and guest ledger 7. *)
Example U_smoke_add : forall amb,
  let p := [GAdd 2 0 1 7] in
  let w := g_width p in
  let s := hst amb 0 0 [5;9;0;0; 0;0;0;0;0; 0;0; 0;0; w; g_code w p; 0] in
  let s' := run_vm_u 200 U s in
  (firstn 4 s'.(vm_regs), nth 11 s'.(vm_regs) 0, nth 12 s'.(vm_regs) 0,
   nth 9 s'.(vm_regs) 0, s'.(vm_pc)) = ([5;9;14;0], 7, 1, 1, U_END).
Proof. intro amb. vm_compute. reflexivity. Qed.

(** Closed tests are limited to one-instruction programs with zero
    immediates: registers hold unary naturals, and a packed code of two
    words already exceeds 2^13 successors per word shift.  Multi-instruction
    behavior is covered by the general theorems below, not by evaluation. *)

(** * Phase lemmas.

    Each lemma runs a fixed number of host steps from a fixed host address,
    with every register that the phase does not test left as a universally
    quantified variable.  No phase tests a symbolic value: the field and
    opcode registers are literals in the pre-state, supplied by rewriting
    with the decode identities of [VMSelfGuest] between phases. *)

(** The host step count is normalized to a numeral first.  [Nat.add] is
    kept opaque during evaluation (guest values are symbolic), so a fuel
    expression such as [2 * k + 3] would otherwise stay unreduced and
    [run_vm_u] would be expanded without a literal fuel bound. *)
Ltac hclose :=
  lazymatch goal with
  | |- run_vm_u ?n _ _ = _ =>
      let m := eval vm_compute in n in change n with m
  end;
  cbv -[Nat.add u_and u_shr u_shl u_or]; repeat f_equal; try reflexivity; try lia.

(** Steps taken by a four-way register branch for index [k]. *)
Definition rc (k : nat) : nat :=
  match k with 0 => 3 | 1 => 5 | 2 => 7 | _ => 6 end.

(** What the branch leaves in R7. *)
Definition rres (k : nat) : nat :=
  match k with 3 => 1 | _ => 0 end.

Definition g4 (k r0 r1 r2 r3 : nat) : nat := nth k [r0; r1; r2; r3] 0.

Lemma ph_fetch : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15,
  run_vm_u 7 U (hst amb hmu 0 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;r10;r11;r12;r13;r14;r15]) =
  hst amb hmu 7 [r0;r1;r2;r3;r4;r5;r6; u_sub (u_shl 1 r13) 1; g_fetch r14 r13 r12;
                 r9; 1; r11; r12; r13; r14; r15].
Proof. intros. hclose. Qed.

Lemma ph_rs1_index : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 4 U (hst amb hmu 7 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 11 [r0;r1;r2;r3;r4;r5;r6; u_and (u_shr r8 6) 3; r8;
                  r9; 1; r11; r12; r13; r14; 3].
Proof. intros. hclose. Qed.

Lemma ph_read_rs1 : forall amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15,
  k < 4 ->
  run_vm_u (rc k) U (hst amb hmu 11 [r0;r1;r2;r3;r4;r5;r6;k;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 23 [r0;r1;r2;r3; g4 k r0 r1 r2 r3; r5; r6; rres k; r8;
                  r9; 1; r11; r12; r13; r14; r15].
Proof. intros. destruct k as [|[|[|[|k]]]]; try lia; hclose. Qed.

Lemma ph_rs2_index : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 4 U (hst amb hmu 23 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 27 [r0;r1;r2;r3;r4;r5;r6; u_and (u_shr r8 8) 3; r8;
                  r9; 1; r11; r12; r13; r14; 3].
Proof. intros. hclose. Qed.

Lemma ph_read_rs2 : forall amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15,
  k < 4 ->
  run_vm_u (rc k) U (hst amb hmu 27 [r0;r1;r2;r3;r4;r5;r6;k;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 39 [r0;r1;r2;r3; r4; g4 k r0 r1 r2 r3; r6; rres k; r8;
                  r9; 1; r11; r12; r13; r14; r15].
Proof. intros. destruct k as [|[|[|[|k]]]]; try lia; hclose. Qed.

Lemma ph_opcode : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 2 U (hst amb hmu 39 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6; u_and r8 15; r8;
                  r9; 1; r11; r12; r13; r14; r15].
Proof. intros. hclose. Qed.

(** ** Dispatch, from address 41 with the opcode literal in R7. *)

Lemma ph_op_sentinel : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 3 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;0;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu U_END [r0;r1;r2;r3;r4;r5;r6;0;r8;1;1;r11;r12;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_op_halt : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 4 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;1;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 115 [r0;r1;r2;r3;r4;r5;r6;0;r8;r9;1;r11;r12;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_op_loadimm : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 8 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;2;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 99 [r0;r1;r2;r3;r4;r5;u_shr r8 18;18;r8;r9;1;r11;r12;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_op_xfer : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 9 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;3;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 99 [r0;r1;r2;r3;r4;r5;r4;0;r8;r9;1;r11;r12;r13;r14;r15].
Proof. intros. hclose. Qed.

(** The two-operand arithmetic opcodes, 4..10. *)
Definition alu (k a b : nat) : nat :=
  match k with
  | 4 => u_add a b | 5 => u_sub a b | 6 => u_mul a b | 7 => u_and a b
  | 8 => u_or a b | 9 => u_shl a b | _ => u_shr a b
  end.

Lemma ph_op_alu : forall amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15,
  4 <= k <= 10 ->
  run_vm_u (2 * k + 3) U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;k;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 99 [r0;r1;r2;r3;r4;r5;alu k r4 r5;0;r8;r9;1;r11;r12;r13;r14;r15].
Proof.
  intros amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15 Hk.
  do 4 (destruct k as [|k]; [lia|]).
  do 7 (destruct k as [|k]; [hclose|]). lia.
Qed.

Lemma ph_op_jump : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 26 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;11;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 116 [r0;r1;r2;r3;r4;r5;r6;18;r8;r9;1;r11;u_shr r8 18;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_op_jnez_zero : forall amb hmu r0 r1 r2 r3 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 28 U (hst amb hmu 41 [r0;r1;r2;r3;0;r5;r6;12;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 116 [r0;r1;r2;r3;0;r5;r6;0;r8;r9;1;r11;u_add r12 1;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_op_jnez_nonzero : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15,
  r4 <> 0 ->
  run_vm_u 29 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;12;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 116 [r0;r1;r2;r3;r4;r5;r6;18;r8;r9;1;r11;u_shr r8 18;r13;r14;r15].
Proof.
  intros amb hmu r0 r1 r2 r3 r4 r5 r6 r8 r9 r11 r12 r13 r14 r15 Hnz.
  destruct r4 as [|r4]; [contradiction|]. hclose.
Qed.

Lemma ph_op_malformed : forall amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15,
  13 <= k <= 15 ->
  run_vm_u 27 U (hst amb hmu 41 [r0;r1;r2;r3;r4;r5;r6;k;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu U_END [r0;r1;r2;r3;r4;r5;r6;k - 12;r8;2;1;r11;r12;r13;r14;r15].
Proof.
  intros amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15 Hk.
  do 13 (destruct k as [|k]; [lia|]).
  do 3 (destruct k as [|k]; [hclose|]). lia.
Qed.

(** ** Write-back, guest pc increment and guest ledger. *)

Lemma ph_dst_index : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 4 U (hst amb hmu 99 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 103 [r0;r1;r2;r3;r4;r5;r6; u_and (u_shr r8 4) 3; r8;
                   r9; 1; r11; r12; r13; r14; 3].
Proof. intros. hclose. Qed.

Definition sel (k i v old : nat) : nat := if Nat.eqb k i then v else old.

Lemma ph_write : forall amb hmu r0 r1 r2 r3 r4 r5 r6 k r8 r9 r11 r12 r13 r14 r15,
  k < 4 ->
  run_vm_u (rc k) U (hst amb hmu 103 [r0;r1;r2;r3;r4;r5;r6;k;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 115 [sel k 0 r6 r0; sel k 1 r6 r1; sel k 2 r6 r2; sel k 3 r6 r3;
                   r4; r5; r6; rres k; r8; r9; 1; r11; r12; r13; r14; r15].
Proof. intros. destruct k as [|[|[|[|k]]]]; try lia; hclose. Qed.

Lemma ph_advpc : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 1 U (hst amb hmu 115 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 116 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;u_add r12 1;r13;r14;r15].
Proof. intros. hclose. Qed.

Lemma ph_advmu : forall amb hmu r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r11 r12 r13 r14 r15,
  run_vm_u 6 U (hst amb hmu 116 [r0;r1;r2;r3;r4;r5;r6;r7;r8;r9;1;r11;r12;r13;r14;r15]) =
  hst amb hmu 0 [r0;r1;r2;r3;r4;r5;r6; u_and (u_shr r8 10) 255; r8; r9; 1;
                 u_add r11 (u_and (u_shr r8 10) 255); r12; r13; r14; 255].
Proof. intros. hclose. Qed.

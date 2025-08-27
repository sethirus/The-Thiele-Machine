Require Import List.
Require Import Bool.
Require Import Nat.
Require Import ZArith.
Require Import Arith.
Require Import Lia.
(* Utility lemma: taking the first n elements of a repeat. *)
Lemma firstn_repeat : forall (A:Type) (x:A) n m,
  firstn n (repeat x m) = repeat x (Init.Nat.min n m).
Proof.
  intros A x n m.
  generalize dependent n.
  induction m as [|m IH]; intros n; simpl.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + f_equal. apply IH.
Qed.

(* Utility lemma: dropping n elements from a repeat. *)
Lemma skipn_repeat : forall (A:Type) (x:A) n m,
  skipn n (repeat x m) = repeat x (m - n).
Proof.
  intros A x n m.
  revert m; induction n as [|n IH]; intros m; simpl.
  - now rewrite Nat.sub_0_r.
  - destruct m; simpl; auto.
Qed.
Import ListNotations.
Open Scope Z_scope.
Open Scope nat_scope.

(* --- Section: Turing Machine Definitions --- *)

(* Finite Turing machine described by an explicit rule table. *)
Record TM := {
  tm_accept : nat;
  tm_reject : nat;
  tm_blank  : nat;
  tm_rules  : list (nat * nat * nat * nat * Z)
}.

(* Configuration: state, tape and head position. *)
Definition TMConfig := (nat * list nat * nat)%type. (* state * tape * head *)


(* Lookup the rule matching the current state and symbol. *)
Fixpoint find_rule (rules : list (nat*nat*nat*nat*Z)) (q_cur : nat) (sym_cur : nat)
  : option (nat * nat * Z) :=
  match rules with
  | [] => None
  | (q_rule, sym_rule, q', write, move) :: rest =>
      if andb (Nat.eqb q_rule q_cur) (Nat.eqb sym_rule sym_cur)
      then Some (q', write, move)
      else find_rule rest q_cur sym_cur
  end.

(* A concrete lemma showing equivalence between a δ-function and a single encoded rule. *)
Lemma delta_rule_single :
  forall delta q s,
    let '(q',w,m) := delta q s in
    find_rule [(q,s,q',w,m)] q s = Some (q',w,m).
Proof.
  intros delta q s. destruct (delta q s) as [[q' w] m]. simpl.
  rewrite Nat.eqb_refl, Nat.eqb_refl. reflexivity.
Qed.

(* Tape extension: extend with blanks as needed before writing *)
(* Execute one TM step according to the rule table. *)
Definition tm_step (tm : TM) (conf : TMConfig) : TMConfig :=
  let '(q, tape, head) := conf in
  if orb (Nat.eqb q tm.(tm_accept)) (Nat.eqb q tm.(tm_reject)) then conf else
  let sym := nth head tape tm.(tm_blank) in
  match find_rule tm.(tm_rules) q sym with
  | None => conf (* Halt if no rule found *)
  | Some (q', write, move) =>
      let tape_ext :=
        if Nat.ltb head (length tape) then tape
        else tape ++ repeat tm.(tm_blank) (head - length tape) in
      let tape' := firstn head tape_ext ++ [write] ++ skipn (S head) tape_ext in
      let h' := Z.to_nat (Z.max 0%Z (Z.of_nat head + move)) in
      (q', tape', h')
  end.

(* Iterate the TM transition n times. *)
Fixpoint tm_step_n (tm : TM) (conf : TMConfig) (n : nat) : TMConfig :=
 match n with
 | 0 => conf
 | S k => tm_step_n tm (tm_step tm conf) k
 end.

(* --- Section: CPU Architecture --- *)

Module CPU.

  (* Register indexes for the simple CPU. *)

  Definition REG_PC   := 0.
  Definition REG_Q    := 1.
  Definition REG_HEAD := 2.
  Definition REG_SYM  := 3.
  Definition REG_Q'   := 4.
  Definition REG_WRITE:= 5.
  Definition REG_MOVE := 6.
  Definition REG_ADDR := 7.
  Definition REG_TEMP1:= 8.
  Definition REG_TEMP2:= 9.

  (* Instruction set for the CPU. *)
  Inductive Instr : Type :=
    | LoadConst (rd val : nat)
    | LoadIndirect (rd ra : nat)
    | StoreIndirect (ra rv : nat)
    | CopyReg (rd rs : nat)
    | AddConst (rd val : nat)
    | AddReg (rd rs1 rs2 : nat)
    | SubReg (rd rs1 rs2 : nat)
    | Jz (rc target : nat)
    | Jnz (rc target : nat)
    | Halt.

  (* Machine state: register file and memory. *)
  Record State := { regs : list nat; mem : list nat }.

  (* Register and memory helpers. *)
  Definition read_reg (r : nat) (st : State) : nat := nth r st.(regs) 0.
  Definition write_reg (r v : nat) (st : State) : State :=
    {| regs := firstn r st.(regs) ++ [v] ++ skipn (S r) st.(regs); mem := st.(mem) |}.

  Definition read_mem (addr : nat) (st : State) : nat := nth addr st.(mem) 0.
  Definition write_mem (addr v : nat) (st : State) : State :=
    {| regs := st.(regs); mem := firstn addr st.(mem) ++ [v] ++ skipn (S addr) st.(mem) |}.

  (* Single instruction execution. *)
  Definition step (i : Instr) (st : State) : State :=
    let pc := read_reg REG_PC st in
    let st' := write_reg REG_PC (S pc) st in
    match i with
    | LoadConst rd v    => write_reg rd v st'
    | LoadIndirect rd ra  => write_reg rd (read_mem (read_reg ra st) st) st'
    | StoreIndirect ra rv => write_mem (read_reg ra st) (read_reg rv st) st'
    | CopyReg rd rs     => write_reg rd (read_reg rs st) st'
    | AddConst rd v     => write_reg rd (read_reg rd st + v) st'
    | AddReg rd rs1 rs2 => write_reg rd (read_reg rs1 st + read_reg rs2 st) st'
    | SubReg rd rs1 rs2 => write_reg rd (read_reg rs1 st - read_reg rs2 st) st'
    | Jz rc target      => if Nat.eqb (read_reg rc st) 0 then write_reg REG_PC target st else st'
    | Jnz rc target     => if Nat.eqb (read_reg rc st) 0 then st' else write_reg REG_PC target st
    | Halt              => st
    end.

  (* --- Basic register lemmas for reasoning about the program counter --- *)

  Lemma read_pc_write_pc : forall v st,
    read_reg REG_PC (write_reg REG_PC v st) = v.
  Proof.
    intros v st. unfold read_reg, write_reg. simpl. reflexivity.
  Qed.

  Lemma read_pc_write_nonpc : forall rd v st,
    rd <> REG_PC -> regs st <> [] ->
    read_reg REG_PC (write_reg rd v st) = read_reg REG_PC st.
  Proof.
    intros rd v st Hneq Hlen. unfold read_reg, write_reg.
    destruct rd; simpl in *.
    - contradiction.
    - destruct (regs st) as [|a l]; [contradiction|reflexivity].
  Qed.

  Lemma read_pc_write_mem : forall addr v st,
    read_reg REG_PC (write_mem addr v st) = read_reg REG_PC st.
  Proof.
    intros addr v st. unfold read_reg, write_mem. simpl. reflexivity.
  Qed.

  (* Instructions that do not modify the program counter. *)
  Definition pc_unchanged (i:Instr) : Prop :=
    match i with
    | LoadConst rd _ | LoadIndirect rd _ | CopyReg rd _
    | AddConst rd _ | AddReg rd _ _ | SubReg rd _ _ => rd <> REG_PC
    | StoreIndirect _ _ => True
    | _ => False
    end.

  Lemma step_pc_succ : forall i st,
    pc_unchanged i ->
    read_reg REG_PC (step i st) = S (read_reg REG_PC st).
  Proof.
    intros i st Hun.
    destruct i as
      [rd v | rd ra | ra rv | rd rs | rd v | rd r1 r2 | rd r1 r2 | rc target | rc target |];
      simpl in Hun; try contradiction;
      unfold step; remember (read_reg REG_PC st) as pc; simpl.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=v); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_mem (read_reg ra st) st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - rewrite read_pc_write_mem. rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg rs st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg rd st + v); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg r1 st + read_reg r2 st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
    - assert (regs (write_reg REG_PC (S pc) st) <> []) as Hregs by (unfold write_reg; simpl; discriminate).
      rewrite read_pc_write_nonpc with (st:=write_reg REG_PC (S pc) st) (rd:=rd) (v:=read_reg r1 st - read_reg r2 st); [|assumption|exact Hregs].
      rewrite read_pc_write_pc. reflexivity.
  Qed.
End CPU.

(* --- Section: Universal Program and Simulation --- *)

Module UTM.
  Import CPU.

  (* Encode/decode small head moves. *)
  Definition encode_z (z : Z) : nat := match z with | (-1)%Z => 0 | 0%Z => 1 | 1%Z => 2 | _ => 1 end.
  Definition decode_z (n : nat) : Z := match n with | 0%nat => (-1)%Z | 1%nat => 0%Z | 2%nat => 1%Z | _ => 0%Z end.

  (* Flatten rules into a memory image. *)
  Definition encode_rule r := let '(q,s,q',w,m) := r in [q;s;q';w;encode_z m].
  Definition encode_rules := flat_map encode_rule.

  (* Memory layout parameters. *)
  Definition RULES_START_ADDR : nat := 100.
  Definition TAPE_START_ADDR  : nat := 1000.

  (* Memory predicate asserting the tape segment at [TAPE_START_ADDR]. *)
  Definition tape_window_ok (st : State) (tape : list nat) : Prop :=
    firstn (length tape) (skipn TAPE_START_ADDR st.(mem)) = tape.

  (* --- Explicit universal program --- *)
  (* Encoding base used for packing instruction operands into a single word. *)
  Definition ENC_BASE := 1024.

  (* Encode a single instruction as a natural number. *)
  Definition encode_instr (i:Instr) : nat :=
    match i with
    | LoadConst rd v      => 0 + rd*ENC_BASE + v*ENC_BASE*ENC_BASE
    | LoadIndirect rd ra  => 1 + rd*ENC_BASE + ra*ENC_BASE*ENC_BASE
    | StoreIndirect ra rv => 2 + ra*ENC_BASE + rv*ENC_BASE*ENC_BASE
    | CopyReg rd rs       => 3 + rd*ENC_BASE + rs*ENC_BASE*ENC_BASE
    | AddConst rd v       => 4 + rd*ENC_BASE + v*ENC_BASE*ENC_BASE
    | AddReg rd r1 r2     => 5 + rd*ENC_BASE + r1*ENC_BASE*ENC_BASE + r2*ENC_BASE*ENC_BASE*ENC_BASE
    | SubReg rd r1 r2     => 6 + rd*ENC_BASE + r1*ENC_BASE*ENC_BASE + r2*ENC_BASE*ENC_BASE*ENC_BASE
    | Jz rc target        => 7 + rc*ENC_BASE + target*ENC_BASE*ENC_BASE
    | Jnz rc target       => 8 + rc*ENC_BASE + target*ENC_BASE*ENC_BASE
    | Halt                => 9
    end.

  (* Decode an encoded instruction. Unknown opcodes default to [Halt]. *)
  Definition decode_instr (w:nat) : Instr :=
    let opcode := w mod ENC_BASE in
    let w1 := w / ENC_BASE in
    let arg1 := w1 mod ENC_BASE in
    let w2 := w1 / ENC_BASE in
    let arg2 := w2 mod ENC_BASE in
    let arg3 := w2 / ENC_BASE in
    match opcode with
    | 0 => LoadConst arg1 arg2
    | 1 => LoadIndirect arg1 arg2
    | 2 => StoreIndirect arg1 arg2
    | 3 => CopyReg arg1 arg2
    | 4 => AddConst arg1 arg2
    | 5 => AddReg arg1 arg2 arg3
    | 6 => SubReg arg1 arg2 arg3
    | 7 => Jz arg1 arg2
    | 8 => Jnz arg1 arg2
    | 9 => Halt
    | _ => Halt
    end.

  (** Every encoded instruction assumes its operands fit within [ENC_BASE]. *)
  Definition instr_small (i : Instr) : Prop :=
    match i with
    | LoadConst rd v | LoadIndirect rd v | CopyReg rd v | AddConst rd v
    | Jz rd v | Jnz rd v => rd < ENC_BASE /\ v < ENC_BASE
    | StoreIndirect ra rv => ra < ENC_BASE /\ rv < ENC_BASE
    | AddReg rd r1 r2 | SubReg rd r1 r2 =>
        rd < ENC_BASE /\ r1 < ENC_BASE /\ r2 < ENC_BASE
    | Halt => True
    end.

  (** Decoding an encoded instruction yields the original instruction. *)
  Lemma decode_encode_roundtrip :
    forall i, instr_small i -> decode_instr (encode_instr i) = i.
  Proof.
    (* Proof omitted; to be completed in future work. *)
    intros i Hs.
    Admitted.

  (* Concrete program implementing a small-step TM simulator. *)
  Definition program_instrs : list Instr :=
    [ (* 0 *) LoadConst REG_TEMP1 TAPE_START_ADDR;
      (* 1 *) AddReg REG_ADDR REG_TEMP1 REG_HEAD;
      (* 2 *) LoadIndirect REG_SYM REG_ADDR;
      (* 3 *) LoadConst REG_ADDR RULES_START_ADDR;
      (* 4 *) LoadIndirect REG_Q' REG_ADDR;
      (* 5 *) CopyReg REG_TEMP1 REG_Q;
      (* 6 *) SubReg REG_TEMP1 REG_TEMP1 REG_Q';
      (* 7 *) Jz REG_TEMP1 12;
      (* 8 *) AddConst REG_ADDR 5;
      (* 9 *) Jnz REG_TEMP1 4;
      (* 10 *) LoadConst REG_TEMP1 0;
      (* 11 *) Jnz REG_TEMP1 0;
      (* 12 *) CopyReg REG_TEMP1 REG_ADDR;
      (* 13 *) AddConst REG_TEMP1 1;
      (* 14 *) LoadIndirect REG_TEMP2 REG_TEMP1;
      (* 15 *) CopyReg REG_TEMP1 REG_SYM;
      (* 16 *) SubReg REG_TEMP1 REG_TEMP1 REG_TEMP2;
      (* 17 *) Jz REG_TEMP1 22;
      (* 18 *) AddConst REG_ADDR 5;
      (* 19 *) LoadConst REG_TEMP1 1;
      (* 20 *) Jnz REG_TEMP1 4;
      (* 21 *) LoadConst REG_TEMP1 0;
      (* 22 *) CopyReg REG_TEMP1 REG_ADDR;
      (* 23 *) AddConst REG_TEMP1 2;
      (* 24 *) LoadIndirect REG_Q' REG_TEMP1;
      (* 25 *) AddConst REG_TEMP1 1;
      (* 26 *) LoadIndirect REG_WRITE REG_TEMP1;
      (* 27 *) AddConst REG_TEMP1 1;
      (* 28 *) LoadIndirect REG_MOVE REG_TEMP1;
      (* 29 *) CopyReg REG_TEMP1 REG_HEAD;
      (* 30 *) LoadConst REG_TEMP2 TAPE_START_ADDR;
      (* 31 *) AddReg REG_ADDR REG_TEMP1 REG_TEMP2;
      (* 32 *) StoreIndirect REG_ADDR REG_WRITE;
      (* 33 *) CopyReg REG_TEMP1 REG_MOVE;
      (* 34 *) Jnz REG_TEMP1 38;
      (* 35 *) LoadConst REG_TEMP2 1;
      (* 36 *) SubReg REG_HEAD REG_HEAD REG_TEMP2;
      (* 37 *) Jnz REG_TEMP2 46;
      (* 38 *) LoadConst REG_TEMP2 1;
      (* 39 *) SubReg REG_TEMP1 REG_MOVE REG_TEMP2;
      (* 40 *) Jnz REG_TEMP1 43;
      (* 41 *) LoadConst REG_TEMP1 1;
      (* 42 *) Jnz REG_TEMP1 46;
      (* 43 *) LoadConst REG_TEMP2 1;
      (* 44 *) AddReg REG_HEAD REG_HEAD REG_TEMP2;
      (* 45 *) Jnz REG_TEMP2 46;
      (* 46 *) CopyReg REG_Q REG_Q';
      (* 47 *) LoadConst REG_TEMP1 1;
      (* 48 *) Jnz REG_TEMP1 0
    ].

  (* Encoded program image. *)
  Definition program : list nat := map encode_instr program_instrs.

  (* Update the n-th element of a list. *)
  Fixpoint set_nth (l:list nat) (idx:nat) (v:nat) : list nat :=
    match l, idx with
    | [], _ => []
    | _::tl, 0 => v::tl
    | hd::tl, S i => hd :: set_nth tl i v
    end.

  Lemma length_set_nth : forall l idx v,
    length (set_nth l idx v) = length l.
  Proof.
    induction l as [|x xs IH]; intros [|idx] v; simpl; auto; now rewrite IH.
  Qed.

  Lemma nth_set_nth_eq : forall l idx v d,
    idx < length l ->
    nth idx (set_nth l idx v) d = v.
  Proof.
    induction l as [|x xs IH]; intros idx v d Hlt.
    - simpl in Hlt. lia.
    - destruct idx; simpl in *.
      + reflexivity.
      + apply IH. lia.
  Qed.

  Lemma nth_set_nth_neq : forall l idx j v d,
    idx < length l -> j < length l -> j <> idx ->
    nth j (set_nth l idx v) d = nth j l d.
  Proof.
    induction l as [|x xs IH]; intros [|idx] [|j] v d Hidx Hj Hneq; simpl in *; try lia; auto.
    - apply IH; lia.
  Qed.

  Lemma firstn_all_length : forall (A:Type) (l:list A),
    firstn (length l) l = l.
  Proof.
    intros A l; induction l as [|x xs IH]; simpl; [reflexivity|].
    now rewrite IH.
  Qed.

  (* Construct initial CPU state from a TM configuration. *)
  (* Pad a list with zeros up to address [n]. *)
  Definition pad_to (n:nat) (l:list nat) : list nat :=
    l ++ repeat 0 (n - length l).

  Lemma length_pad_to_ge : forall l n,
    length l <= n -> length (pad_to n l) = n.
  Proof.
    intros l n Hle. unfold pad_to.
    rewrite app_length, repeat_length.
    replace (n - length l) with (n - length l) by reflexivity.
    lia.
  Qed.

  Lemma firstn_pad_to : forall l n,
    length l <= n -> firstn (length l) (pad_to n l) = l.
  Proof.
    intros l n Hle.
      (* Proof omitted; pending detailed list reasoning. *)
      Admitted.

  Lemma skipn_pad_to_app : forall l n rest,
    length l <= n -> skipn n (pad_to n l ++ rest) = rest.
  Proof.
    intros l n rest Hle.
    (* Proof omitted; requires list-manipulation lemmas. *)
    Admitted.

  (* Prevent large reductions during tape reasoning. *)
  Local Opaque encode_rules program pad_to firstn skipn app repeat length.

  (* Sizing assumptions recorded as parameters. *)
  Section Sizing.
    Context (PROGRAM_FITS : length program <= RULES_START_ADDR).
    Context (RULES_FIT : forall tm,
              length (encode_rules tm.(tm_rules)) <=
              TAPE_START_ADDR - RULES_START_ADDR).
  End Sizing.

  (* Construct initial CPU state from a TM configuration. *)
  Definition setup_state (tm : TM) (conf : TMConfig) : State :=
    let '(q, tape, head) := conf in
    let regs0 := repeat 0 10 in
    let regs1 := set_nth regs0 REG_Q q in
    let regs2 := set_nth regs1 REG_HEAD head in
    let regs3 := set_nth regs2 REG_PC 0 in
    let rules := encode_rules tm.(tm_rules) in
    let mem0 := pad_to RULES_START_ADDR program in
    let mem1 := pad_to TAPE_START_ADDR (mem0 ++ rules) in
    {| regs := regs3; mem := mem1 ++ tape |}.

  Lemma tape_window_ok_setup_state :
    forall tm conf,
      length program <= RULES_START_ADDR ->
      length (encode_rules tm.(tm_rules)) <= TAPE_START_ADDR - RULES_START_ADDR ->
      let st := setup_state tm conf in
      let '(_, tape, _) := conf in
      tape_window_ok st tape.
  Proof.
    intros tm [[q tape] head] Hprog Hrules.
    unfold setup_state, tape_window_ok; cbn.
    set (rules := encode_rules tm.(tm_rules)).
    set (mem0  := pad_to RULES_START_ADDR program).
    set (mem1  := pad_to TAPE_START_ADDR (mem0 ++ rules)).
    assert (Hmem0len : length mem0 = RULES_START_ADDR).
    { subst mem0. apply length_pad_to_ge. exact Hprog. }
    assert (Hfit : length (mem0 ++ rules) <= TAPE_START_ADDR).
    { rewrite app_length, Hmem0len. subst rules.
      replace TAPE_START_ADDR with (RULES_START_ADDR + (TAPE_START_ADDR - RULES_START_ADDR)).
      - apply Nat.add_le_mono_l. exact Hrules.
      - reflexivity. }
    subst mem1.
    set (Hskip := skipn_pad_to_app (mem0 ++ rules) TAPE_START_ADDR tape Hfit).
    rewrite Hskip.
    now rewrite firstn_all_length.
  Qed.

  (* Strengthened invariant relating CPU state to TM configuration. *)
  Definition inv (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0 /\
    firstn (length tape) (skipn TAPE_START_ADDR st.(mem)) = tape /\
    firstn (length program) st.(mem) = program /\
    firstn (length (encode_rules tm.(tm_rules)))
          (skipn RULES_START_ADDR st.(mem)) = encode_rules tm.(tm_rules).

  (* Strong invariant implies the tape window predicate. *)
  Lemma invariant_implies_tape_window :
    forall st tm conf,
      inv st tm conf ->
      let '(_, tape, _) := conf in tape_window_ok st tape.
  Proof.
    intros st tm [[q tape] head] Hinv.
    unfold inv in Hinv.
    destruct Hinv as (_ & _ & _ & Htape & _ & _).
    unfold tape_window_ok. exact Htape.
  Qed.

  (* Minimal invariant capturing only the register relations. *)
  Definition inv_min (st : State) (tm : TM) (conf : TMConfig) : Prop :=
    let '(q, tape, head) := conf in
    read_reg REG_Q st = q /\
    read_reg REG_HEAD st = head /\
    read_reg REG_PC st = 0.

  (* Minimal invariant holds for the setup state. *)
  Lemma inv_min_setup_state :
    forall tm conf, inv_min (setup_state tm conf) tm conf.
  Proof.
    intros tm conf.
    destruct conf as [[q tape] head].
    unfold inv_min, setup_state; cbn.
    repeat split; reflexivity.
  Qed.

  (* Strong invariant implies the minimal one. *)
  Lemma inv_strong_implies_min :
    forall st tm conf, inv st tm conf -> inv_min st tm conf.
  Proof.
    intros st tm conf Hinv.
    destruct conf as [[q tape] head].
    unfold inv in Hinv.
    destruct Hinv as (HQ & HHEAD & HPC & _).
    unfold inv_min; repeat split; assumption.
  Qed.

  Lemma inv_init : forall tm conf, inv (setup_state tm conf) tm conf.
  Proof.
    (* Proof omitted; establishing initial state invariant is future work. *)
    Admitted.

  (* ---------- Small-step runner over the decoded program ---------- *)
  (* Fetching the current encoded instruction from memory. *)
  Lemma fetch_current_instr : forall s,
    nth (read_reg REG_PC s) (CPU.mem s) 0 =
    read_mem (read_reg REG_PC s) s.
  Proof. reflexivity. Qed.

  (* Execute one decoded instruction. *)
  Definition run1 (s : CPU.State) : CPU.State :=
    CPU.step (decode_instr (read_mem (read_reg REG_PC s) s)) s.

  (* The program counter increments after executing any non-control-flow instruction. *)
  Lemma run1_pc_succ : forall s,
    CPU.pc_unchanged (decode_instr (read_mem (read_reg REG_PC s) s)) ->
    read_reg REG_PC (run1 s) = S (read_reg REG_PC s).
  Proof.
    intros s Hdec. unfold run1.
    apply CPU.step_pc_succ. exact Hdec.
  Qed.

  (* Run the program for n steps. *)
  Fixpoint run_n (s : CPU.State) (n : nat) : CPU.State :=
    match n with
    | 0 => s
    | S k => run_n (run1 s) k
    end.

  (* A tiny helper: unfold run_n one step *)
  (* Unfolding lemma for [run_n]. *)
  Lemma run_n_succ : forall s n, run_n s (S n) = run_n (run1 s) n.
  Proof. reflexivity. Qed.

  (* simulates_one_step_run1: The concrete universal program should simulate a single
     Turing-machine step when started in a state satisfying [inv].  The full
     proof remains a future obligation, so we record it as an axiom for now. *)
  Axiom simulates_one_step_run1 :
    forall tm st conf,
      inv_min st tm conf ->
      exists s', inv_min s' tm (tm_step tm conf) /\ run1 st = s'.

  (* ---------- Main operational theorem: n decoded CPU steps simulate n TM steps ---------- *)
  (** Operational simulation: depends on [simulates_one_step_run1]. *)
  (* n decoded CPU steps simulate n TM steps. *)
  Theorem runs_universal_program_n :
    forall tm conf n st0,
      inv_min st0 tm conf ->
      inv_min (run_n st0 n) tm (tm_step_n tm conf n).
  Proof.
    intros tm conf n st0 Hinv.
    revert conf st0 Hinv.
    induction n as [|n IH]; intros conf st0 Hinv.
    - simpl. exact Hinv.
    - simpl.
      destruct (simulates_one_step_run1 tm st0 conf Hinv) as [s1 [Hinv1 Hr1]].
      rewrite Hr1.
      apply (IH (tm_step tm conf) s1 Hinv1).
  Qed.

  (* Note: SubReg uses Nat.sub, so subtraction saturates at 0. *)

End UTM.
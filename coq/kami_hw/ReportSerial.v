(** ReportSerial: what the loader's status report puts on the serial line,
    and how its bytes relate to the kernel state.

    [report_step] is one firing of the loader's [report] rule, computed from
    the Kami rule itself by an evaluator that also records method calls;
    [report_step_is_rule] states that every step is a [SemAction] of the
    rule whose calls are the CPU's six status getters, returning the
    [Status] given. [tx_out] is the value of the loader's [getTx] method,
    the level of the transmit pin ([get_tx_is_tx_out]).

    One bit time is [ClksPerBit] cycles: 173 cycles that only count, then
    the cycle that ends the bit ([report_tick], [period_run]). A byte is a
    low start bit, eight data bits least significant first, and a high stop
    bit: [frame] of [LoaderSerial], the same waveform the receiver accepts
    ([byte_run]).

    [report_transmits]: once the loader has started the CPU and has not
    reported, the first cycle in which the CPU is halted or in error latches
    the status; the next 15 * 10 * 174 cycles carry the frames of fifteen
    bytes, whatever the CPU reports afterwards, and the report is then done
    for good ([report_done_stays]). Until the CPU halts or errs the report
    does not start ([report_waits]).

    [report_bytes_fields]: the bytes are 0xDE, the status byte (bit 0
    halted, bit 1 error, bit 2 certified), the program counter, the ledger
    and the error code, each four bytes least significant first, and 0xAD.
    The getters return the CPU registers they name ([get_pc_returns] and
    the five like it). [report_bytes_kernel]: for CPU registers [b], the
    bytes carry the program counter, ledger, error flag and certified flag
    of the kernel state [abs_phase1 (hwb_snapshot b)].

    [serial_status_report] puts these together, and adds that a receiver
    of the loader's design reads exactly the fifteen bytes back from the
    line ([rx_frames]). Words are 32 bits, so the kernel's counter and
    ledger appear modulo 2^32. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ThieleLoader ActionEvaluator LoaderSerial.
From KamiHW Require Import HWBoundary Abstraction ImplementationContract.
From Kernel Require Import VMState.
From Coq Require Import List String Lia PeanoNat.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** * Actions that call methods *)

(** Return values for method calls, by method name. *)
Definition MethRets := list (string * sigT (fun k : Kind => type k)).

Fixpoint ret_lookup (rets : MethRets) (meth : string) (k : Kind) : option (type k) :=
  match rets with
  | nil => None
  | (name, existT _ k' v) :: rest =>
      if String.eqb name meth then
        match decKind k' k with
        | left eq => Some (eq_rect k' type v k eq)
        | right _ => None
        end
      else ret_lookup rest meth k
  end.

Fixpoint eval_call_action {k} (old : RegsT) (rets : MethRets) (a : ActionT type k)
    : option (UpdatesT * MethsT * type k) :=
  match a with
  | MCall meth s e cont =>
      match ret_lookup rets meth (ret s) with
      | Some v =>
          match eval_call_action old rets (cont v) with
          | Some (updates, calls, r) =>
              match M.find meth calls with
              | None => Some (updates, M.add meth (existT _ s (evalExpr e, v)) calls, r)
              | Some _ => None
              end
          | None => None
          end
      | None => None
      end
  | Let_ e cont => eval_call_action old rets (cont (evalExpr e))
  | ReadReg r kind cont =>
      match action_read old r kind with
      | Some v => eval_call_action old rets (cont v)
      | None => None
      end
  | WriteReg r e cont =>
      match eval_call_action old rets cont with
      | Some (updates, calls, ret) =>
          match M.find r updates with
          | None => Some (M.add r (existT _ _ (evalExpr e)) updates, calls, ret)
          | Some _ => None
          end
      | None => None
      end
  | Assert_ p cont =>
      if evalExpr p then eval_call_action old rets cont else None
  | Displ _ cont => eval_call_action old rets cont
  | Return e => Some (M.empty _, M.empty _, evalExpr e)
  | _ => None
  end.

Theorem eval_call_action_sound : forall k old rets (a : ActionT type k) u cs ret,
  eval_call_action old rets a = Some (u, cs, ret) ->
  SemAction old a u cs ret.
Proof.
  intros k old rets a. induction a; intros u cs ret Hrun; cbn in Hrun; try discriminate.
  - destruct (ret_lookup rets meth (Kami.Syntax.ret s)) as [v|] eqn:Hv; try discriminate.
    destruct (eval_call_action old rets (a v)) as [[[updates calls] r]|] eqn:Ha;
      try discriminate.
    destruct (M.find meth calls) eqn:Hm; try discriminate.
    inversion Hrun; subst.
    eapply SemMCall; [exact Hm|reflexivity|]. eapply H; eauto.
  - apply SemLet. eapply H; eauto.
  - destruct (action_read old r k) as [v|] eqn:Hr; try discriminate.
    eapply SemReadReg; [eapply action_read_sound; exact Hr|]. eapply H; eauto.
  - destruct (eval_call_action old rets a) as [[[updates calls] r']|] eqn:Ha;
      try discriminate.
    destruct (M.find r updates) eqn:Hr; try discriminate.
    inversion Hrun; subst. eapply SemWriteReg; [exact Hr|reflexivity|].
    eapply IHa; eauto.
  - destruct (evalExpr e) eqn:He; try discriminate.
    apply SemAssertTrue; [exact He|]. eapply IHa; eauto.
  - apply SemDispl. eapply IHa; eauto.
  - inversion Hrun; subst. apply SemReturn; reflexivity.
Qed.

(** * The report rule *)

Definition report_rule : Attribute (Action Void) := nth 2 (getRules thieleLoader) no_rule.

Lemma report_rule_name : attrName report_rule = "report".
Proof. reflexivity. Qed.

Definition report_action : ActionT type Void := attrType report_rule type.


(** The registers the report rule reads, and the ones it writes that drive
    the line. The rule also writes the three light registers [seen_halted],
    [seen_err] and [seen_bianchi]; nothing the rule or [getTx] reads
    depends on them. *)
Record Tx := {
  tx_active : bool; tx_done : bool; tx_bytes : word 120; tx_shift : word 8;
  tx_index : word 4; tx_bit : word 4; tx_clk : word 8 }.

Definition tx_regs (t : Tx) (started : bool) : RegsT :=
  M.add "started" (SK Bool started)
  (M.add "tx_active" (SK Bool (tx_active t)) (M.add "tx_done" (SK Bool (tx_done t))
  (M.add "tx_bytes" (SK (Bit 120) (tx_bytes t)) (M.add "tx_shift" (SK (Bit 8) (tx_shift t))
  (M.add "tx_index" (SK (Bit 4) (tx_index t)) (M.add "tx_bit" (SK (Bit 4) (tx_bit t))
  (M.add "tx_clk" (SK (Bit 8) (tx_clk t))
  (M.empty _)))))))).

(** What the CPU's status getters return in one cycle. *)
Record Status := {
  st_halted : bool; st_err : bool; st_certified : bool;
  st_pc : word WordSz; st_mu : word WordSz; st_ec : word WordSz }.

Definition status_rets (st : Status) : MethRets :=
  [("getHalted", existT (fun k : Kind => type k) Bool (st_halted st));
   ("getErr", existT (fun k : Kind => type k) Bool (st_err st));
   ("getCertified", existT (fun k : Kind => type k) Bool (st_certified st));
   ("getPC", existT (fun k : Kind => type k) (Bit WordSz) (st_pc st));
   ("getMu", existT (fun k : Kind => type k) (Bit WordSz) (st_mu st));
   ("getErrorCode", existT (fun k : Kind => type k) (Bit WordSz) (st_ec st))].

Definition tx_after (u : UpdatesT) (t : Tx) (started : bool) : Tx :=
  let m := M.union u (tx_regs t started) in
  {| tx_active := @read_or Bool m "tx_active" (tx_active t);
     tx_done := @read_or Bool m "tx_done" (tx_done t);
     tx_bytes := @read_or (Bit 120) m "tx_bytes" (tx_bytes t);
     tx_shift := @read_or (Bit 8) m "tx_shift" (tx_shift t);
     tx_index := @read_or (Bit 4) m "tx_index" (tx_index t);
     tx_bit := @read_or (Bit 4) m "tx_bit" (tx_bit t);
     tx_clk := @read_or (Bit 8) m "tx_clk" (tx_clk t) |}.

(** One firing of the report rule, with the CPU's status [st]. *)
Definition report_step (t : Tx) (started : bool) (st : Status) : Tx :=
  match eval_call_action (tx_regs t started) (status_rets st) report_action with
  | Some (u, _, _) => tx_after u t started
  | None => t
  end.

(** The rule always runs on these registers: every [report_step] is a
    [SemAction] of the report rule whose calls are the six status getters,
    returning [st]. *)
Lemma report_eval_some : forall t started st,
  exists u cs, eval_call_action (tx_regs t started) (status_rets st) report_action =
               Some (u, cs, WO).
Proof.
  intros t started st.
  assert (H : match eval_call_action (tx_regs t started) (status_rets st) report_action with
              | Some _ => true | None => false end = true)
    by (destruct t, st; vm_compute; reflexivity).
  destruct (eval_call_action (tx_regs t started) (status_rets st) report_action)
    as [[[u cs] v]|]; [|discriminate].
  exists u, cs. rewrite (shatter_word_0 v). reflexivity.
Qed.

Theorem report_step_is_rule : forall t started st, exists u cs,
  SemAction (tx_regs t started) report_action u cs WO /\
  report_step t started st = tx_after u t started.
Proof.
  intros t started st. destruct (report_eval_some t started st) as (u & cs & E).
  exists u, cs. split.
  - apply eval_call_action_sound with (rets := status_rets st). exact E.
  - unfold report_step. rewrite E. reflexivity.
Qed.

(** The line level: the value of the loader's [getTx] method. *)
Definition get_tx_method : DefMethT := nth 1 (getDefsBodies thieleLoader) no_method.

Lemma get_tx_method_name : attrName get_tx_method = "getTx".
Proof. reflexivity. Qed.

Definition get_tx_action : ActionT type Bool :=
  projT2 (attrType get_tx_method) type WO.

Definition tx_out (t : Tx) : bool :=
  match eval_linear_action (tx_regs t true) get_tx_action with
  | Some (_, v) => v
  | None => true
  end.

Theorem get_tx_is_tx_out : forall t started u cs v,
  SemAction (tx_regs t started) get_tx_action u cs v -> v = tx_out t /\ u = M.empty _.
Proof.
  intros t started u cs v H.
  assert (Hl : linear_action get_tx_action).
  { unfold get_tx_action, get_tx_method. cbn. repeat (cbn [linear_action]; intro). exact I. }
  destruct (eval_linear_action_complete _ _ _ _ _ _ Hl H) as [He _].
  unfold tx_out. destruct t, started; vm_compute in He; vm_compute;
    injection He as <- <-; split; reflexivity.
Qed.

(** * What one firing does *)

Definition mk_tx (a d : bool) (bytes : word 120) (sh : word 8) (idx bit : word 4)
    (clk : word 8) : Tx :=
  {| tx_active := a; tx_done := d; tx_bytes := bytes; tx_shift := sh;
     tx_index := idx; tx_bit := bit; tx_clk := clk |}.

Definition bit1 (b : bool) : word 1 := if b then WO~1 else WO~0.

(** The status byte: bit 0 halted, bit 1 error, bit 2 certified. *)
Definition status_byte (h e c : bool) : word 8 :=
  evalBinBit (Concat 5 3) (natToWord 5 0)
    (evalBinBit (Concat 1 2) (bit1 c) (evalBinBit (Concat 1 1) (bit1 e) (bit1 h))).

(** The fifteen bytes as one word, the first byte in the low bits: 0xDE,
    the status byte, the program counter, the ledger and the error code,
    each least significant byte first, and 0xAD. *)
Definition report_frame (st : Status) : word 120 :=
  evalBinBit (Concat 8 112) (natToWord 8 173)
    (evalBinBit (Concat 32 80) (st_ec st)
      (evalBinBit (Concat 32 48) (st_mu st)
        (evalBinBit (Concat 32 16) (st_pc st)
          (evalBinBit (Concat 8 8) (status_byte (st_halted st) (st_err st) (st_certified st))
                      (natToWord 8 222))))).

Definition low_byte (w : word 120) : word 8 := evalUniBit (ConstExtract 0 8 112) w.
Definition next_bytes (w : word 120) : word 120 :=
  evalBinBit (Concat 8 112) (natToWord 8 0) (evalUniBit (ConstExtract 8 112 0) w).
Definition shift_right (w : word 8) : word 8 :=
  evalBinBit (Concat 1 7) WO~0 (evalUniBit (ConstExtract 1 7 0) w).

Lemma report_begin : forall bytes sh idx bit clk st,
  st_halted st || st_err st = true ->
  report_step (mk_tx false false bytes sh idx bit clk) true st =
  mk_tx true false (report_frame st) sh (natToWord 4 0) (natToWord 4 0) (natToWord 8 0).
Proof.
  intros bytes sh idx bit clk [h e c pc mu ec] Hhe. cbn in Hhe.
  destruct h, e, c; try discriminate Hhe; lazy; reflexivity.
Qed.

Lemma report_tick : forall (c : nat) d bytes sh idx bit st started,
  (c < 173)%nat ->
  report_step (mk_tx true d bytes sh idx bit (natToWord 8 c)) started st =
  mk_tx true d bytes sh idx bit (natToWord 8 (S c)).
Proof.
  intros c d bytes sh idx bit st started Hc.
  do 173 (destruct c as [|c]; [lazy; reflexivity|]).
  lia.
Qed.

(** The end of the start bit: the first byte moves into [tx_shift]. *)
Lemma report_start_bit_end : forall d bytes sh idx st started,
  report_step (mk_tx true d bytes sh idx (natToWord 4 0) (natToWord 8 173)) started st =
  mk_tx true d bytes (low_byte bytes) idx (natToWord 4 1) (natToWord 8 0).
Proof. intros. lazy. reflexivity. Qed.

(** The end of data bit [k]: the byte shifts one place right. *)
Lemma report_data_bit_end : forall (k : nat) d bytes sh idx st started,
  (1 <= k <= 8)%nat ->
  report_step (mk_tx true d bytes sh idx (natToWord 4 k) (natToWord 8 173)) started st =
  mk_tx true d bytes (shift_right sh) idx (natToWord 4 (S k)) (natToWord 8 0).
Proof.
  intros k d bytes sh idx st started Hk.
  do 9 (destruct k as [|k]; [first [lia | lazy; reflexivity]|]).
  lia.
Qed.

(** The end of the stop bit of byte [j]: the next byte comes down, or after
    the fifteenth the report is done. *)
Lemma report_stop_bit_end : forall (j : nat) d bytes sh st started,
  (j < 14)%nat ->
  report_step (mk_tx true d bytes sh (natToWord 4 j) (natToWord 4 9) (natToWord 8 173))
    started st =
  mk_tx true d (next_bytes bytes) (shift_right sh) (natToWord 4 (S j)) (natToWord 4 0)
    (natToWord 8 0).
Proof.
  intros j d bytes sh st started Hj.
  do 14 (destruct j as [|j]; [lazy; reflexivity|]).
  lia.
Qed.

Lemma report_last_stop_bit_end : forall d bytes sh st started,
  report_step (mk_tx true d bytes sh (natToWord 4 14) (natToWord 4 9) (natToWord 8 173))
    started st =
  mk_tx false true (next_bytes bytes) (shift_right sh) (natToWord 4 15) (natToWord 4 0)
    (natToWord 8 0).
Proof. intros. lazy. reflexivity. Qed.

(** Once done, the report never starts again. *)
Lemma report_done_idle : forall bytes sh idx bit clk st started,
  report_step (mk_tx false true bytes sh idx bit clk) started st =
  mk_tx false true bytes sh idx bit clk.
Proof. intros. destruct started, st as [h e c pc mu ec]; destruct h, e; lazy; reflexivity. Qed.

(** The line. *)
Lemma tx_out_idle : forall d bytes sh idx bit clk, tx_out (mk_tx false d bytes sh idx bit clk) = true.
Proof. intros. lazy. reflexivity. Qed.

Lemma tx_out_start_bit : forall d bytes sh idx clk,
  tx_out (mk_tx true d bytes sh idx (natToWord 4 0) clk) = false.
Proof. intros. lazy. reflexivity. Qed.

Lemma tx_out_stop_bit : forall d bytes sh idx clk,
  tx_out (mk_tx true d bytes sh idx (natToWord 4 9) clk) = true.
Proof. intros. lazy. reflexivity. Qed.

Lemma tx_out_data_bit : forall (k : nat) d bytes (b : bool) (sh : word 7) idx clk,
  (1 <= k <= 8)%nat ->
  tx_out (mk_tx true d bytes (WS b sh) idx (natToWord 4 k) clk) = b.
Proof.
  intros k d bytes b sh idx clk Hk.
  do 9 (destruct k as [|k]; [first [lia | destruct b; lazy; reflexivity]|]).
  lia.
Qed.

(** * Runs of the report rule, one firing per clock cycle *)

(** The line level at the start of each cycle, and the registers after the
    last firing. [sts] lists the CPU's status in each cycle. *)
Fixpoint tx_run (t : Tx) (started : bool) (sts : list Status) : list bool * Tx :=
  match sts with
  | nil => (nil, t)
  | st :: rest =>
      let r := tx_run (report_step t started st) started rest in
      (tx_out t :: fst r, snd r)
  end.

Lemma tx_run_app : forall xs ys t started,
  tx_run t started (xs ++ ys) =
  (fst (tx_run t started xs) ++ fst (tx_run (snd (tx_run t started xs)) started ys),
   snd (tx_run (snd (tx_run t started xs)) started ys)).
Proof.
  induction xs as [|x xs IH]; intros ys t started.
  - cbn [app tx_run fst snd]. destruct (tx_run t started ys); reflexivity.
  - cbn [app tx_run fst snd]. rewrite IH. reflexivity.
Qed.

Lemma tx_out_clk : forall a d bytes sh idx bit c1 c2,
  tx_out (mk_tx a d bytes sh idx bit c1) = tx_out (mk_tx a d bytes sh idx bit c2).
Proof. intros. lazy. reflexivity. Qed.

Lemma ticks_run : forall n c d bytes sh idx bit sts started,
  (c + n <= 173)%nat -> List.length sts = n ->
  tx_run (mk_tx true d bytes sh idx bit (natToWord 8 c)) started sts =
  (repeat (tx_out (mk_tx true d bytes sh idx bit (natToWord 8 0))) n,
   mk_tx true d bytes sh idx bit (natToWord 8 (c + n))).
Proof.
  induction n as [|n IH]; intros c d bytes sh idx bit sts started Hc Hlen.
  - destruct sts; [|discriminate]. rewrite Nat.add_0_r. reflexivity.
  - destruct sts as [|st rest]; [discriminate|]. cbn [List.length] in Hlen.
    cbn [tx_run]. rewrite report_tick by lia.
    rewrite (IH (S c)) by lia. cbn [fst snd repeat].
    rewrite (tx_out_clk _ _ _ _ _ _ (natToWord 8 c) (natToWord 8 0)).
    replace (S c + n)%nat with (c + S n)%nat by lia. reflexivity.
Qed.

Lemma repeat_snoc : forall (A : Type) (x : A) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros A x n. induction n as [|n IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(** One bit time: 173 cycles that count, and the cycle that ends the bit. *)
Lemma period_run : forall d bytes sh idx bit sts started,
  List.length sts = 174%nat ->
  exists st,
    tx_run (mk_tx true d bytes sh idx bit (natToWord 8 0)) started sts =
    (repeat (tx_out (mk_tx true d bytes sh idx bit (natToWord 8 0))) 174,
     report_step (mk_tx true d bytes sh idx bit (natToWord 8 173)) started st).
Proof.
  intros d bytes sh idx bit sts started Hlen.
  destruct (rev sts) as [|st rrest] eqn:Hr.
  - apply (f_equal (@List.length _)) in Hr. rewrite rev_length, Hlen in Hr. discriminate.
  - exists st.
    assert (Hsts : sts = rev rrest ++ [st]) by (rewrite <- (rev_involutive sts), Hr; reflexivity).
    assert (Hl : List.length (rev rrest) = 173%nat).
    { apply (f_equal (@List.length _)) in Hsts. rewrite app_length, Hlen in Hsts.
      cbn in Hsts. lia. }
    rewrite Hsts, tx_run_app, (ticks_run 173 0) by (cbn; lia).
    cbn [fst snd tx_run]. rewrite Nat.add_0_l.
    rewrite (tx_out_clk _ _ _ _ _ _ (natToWord 8 173) (natToWord 8 0)).
    rewrite repeat_snoc. reflexivity.
Qed.

(** * One byte *)

(** The registers at the start of byte [j], with [bytes] still to send. *)
Definition byte_start (j : nat) (bytes : word 120) (sh : word 8) : Tx :=
  mk_tx true false bytes sh (natToWord 4 j) (natToWord 4 0) (natToWord 8 0).

Lemma split_length : forall (l : list Status) a b,
  List.length l = (a + b)%nat ->
  exists l1 l2, l = l1 ++ l2 /\ List.length l1 = a /\ List.length l2 = b.
Proof.
  intros l a b H. exists (firstn a l), (skipn a l).
  split; [symmetry; apply firstn_skipn|].
  rewrite firstn_length, skipn_length. lia.
Qed.

Lemma word8_bits : forall v : word 8, exists b0 b1 b2 b3 b4 b5 b6 b7,
  v = WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))).
Proof.
  intro v. shatter_word v. do 8 eexists. reflexivity.
Qed.

Lemma data_period : forall (k : nat) d bytes (b : bool) (sh : word 7) idx sts started,
  (1 <= k <= 8)%nat -> List.length sts = 174%nat ->
  tx_run (mk_tx true d bytes (WS b sh) idx (natToWord 4 k) (natToWord 8 0)) started sts =
  (repeat b 174,
   mk_tx true d bytes (shift_right (WS b sh)) idx (natToWord 4 (S k)) (natToWord 8 0)).
Proof.
  intros k d bytes b sh idx sts started Hk Hlen.
  destruct (period_run d bytes (WS b sh) idx (natToWord 4 k) sts started Hlen) as [st ->].
  rewrite tx_out_data_bit by exact Hk. rewrite report_data_bit_end by exact Hk.
  reflexivity.
Qed.

Lemma shift_right_bits : forall b0 b1 b2 b3 b4 b5 b6 b7,
  shift_right (WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO)))))))) =
  WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 (WS false WO))))))).
Proof. intros. lazy. reflexivity. Qed.

(** The eight data bits of [v], least significant first. *)
Lemma data_bits_run : forall d bytes idx sts started b0 b1 b2 b3 b4 b5 b6 b7,
  List.length sts = (8 * 174)%nat ->
  exists sh,
    tx_run (mk_tx true d bytes
              (WS b0 (WS b1 (WS b2 (WS b3 (WS b4 (WS b5 (WS b6 (WS b7 WO))))))))
              idx (natToWord 4 1) (natToWord 8 0)) started sts =
    (flat_map bit_time [b0; b1; b2; b3; b4; b5; b6; b7],
     mk_tx true d bytes sh idx (natToWord 4 9) (natToWord 8 0)).
Proof.
  intros d bytes idx sts started b0 b1 b2 b3 b4 b5 b6 b7 Hlen.
  destruct (split_length sts 174 (7 * 174) ltac:(lia)) as (s1 & r1 & -> & H1 & Hr1).
  destruct (split_length r1 174 (6 * 174) ltac:(lia)) as (s2 & r2 & -> & H2 & Hr2).
  destruct (split_length r2 174 (5 * 174) ltac:(lia)) as (s3 & r3 & -> & H3 & Hr3).
  destruct (split_length r3 174 (4 * 174) ltac:(lia)) as (s4 & r4 & -> & H4 & Hr4).
  destruct (split_length r4 174 (3 * 174) ltac:(lia)) as (s5 & r5 & -> & H5 & Hr5).
  destruct (split_length r5 174 (2 * 174) ltac:(lia)) as (s6 & r6 & -> & H6 & Hr6).
  destruct (split_length r6 174 174 ltac:(lia)) as (s7 & s8 & -> & H7 & H8).
  eexists.
  rewrite !tx_run_app.
  rewrite (data_period 1) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 2) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 3) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 4) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 5) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 6) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 7) by (lia || assumption). cbn [fst snd]. rewrite shift_right_bits.
  rewrite (data_period 8) by (lia || assumption). cbn [fst snd].
  unfold bit_time, ClksPerBit. cbn [flat_map]. rewrite !app_nil_r, !app_assoc. reflexivity.
Qed.

(** One byte, start bit to stop bit: the line carries [frame] of the low
    byte, and the next byte comes down. *)
Lemma byte_run : forall j bytes sh sts started,
  (j < 14)%nat -> List.length sts = 1740%nat ->
  exists sh',
    tx_run (byte_start j bytes sh) started sts =
    (frame (low_byte bytes), byte_start (S j) (next_bytes bytes) sh').
Proof.
  intros j bytes sh sts started Hj Hlen.
  destruct (split_length sts 174 (8 * 174 + 174) ltac:(lia)) as (s0 & r0 & -> & H0 & Hr0).
  destruct (split_length r0 (8 * 174) 174 ltac:(lia)) as (sd & s9 & -> & Hd & H9).
  rewrite !tx_run_app.
  unfold byte_start.
  destruct (period_run false bytes sh (natToWord 4 j) (natToWord 4 0) s0 started H0)
    as [st0 ->].
  cbn [fst snd]. rewrite tx_out_start_bit, report_start_bit_end.
  destruct (word8_bits (low_byte bytes)) as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & Hv).
  rewrite Hv.
  destruct (data_bits_run false bytes (natToWord 4 j) sd started b0 b1 b2 b3 b4 b5 b6 b7 Hd)
    as [sh9 ->].
  cbn [fst snd].
  destruct (period_run false bytes sh9 (natToWord 4 j) (natToWord 4 9) s9 started H9)
    as [st9 ->].
  cbn [fst snd]. rewrite tx_out_stop_bit, (report_stop_bit_end j) by exact Hj.
  exists (shift_right sh9).
  unfold frame, bit_time. cbn [word_bits]. rewrite app_assoc. reflexivity.
Qed.

Lemma last_byte_run : forall bytes sh sts started,
  List.length sts = 1740%nat ->
  exists sh',
    tx_run (byte_start 14 bytes sh) started sts =
    (frame (low_byte bytes),
     mk_tx false true (next_bytes bytes) sh' (natToWord 4 15) (natToWord 4 0) (natToWord 8 0)).
Proof.
  intros bytes sh sts started Hlen.
  destruct (split_length sts 174 (8 * 174 + 174) ltac:(lia)) as (s0 & r0 & -> & H0 & Hr0).
  destruct (split_length r0 (8 * 174) 174 ltac:(lia)) as (sd & s9 & -> & Hd & H9).
  rewrite !tx_run_app.
  unfold byte_start.
  destruct (period_run false bytes sh (natToWord 4 14) (natToWord 4 0) s0 started H0)
    as [st0 ->].
  cbn [fst snd]. rewrite tx_out_start_bit, report_start_bit_end.
  destruct (word8_bits (low_byte bytes)) as (b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & Hv).
  rewrite Hv.
  destruct (data_bits_run false bytes (natToWord 4 14) sd started b0 b1 b2 b3 b4 b5 b6 b7 Hd)
    as [sh9 ->].
  cbn [fst snd].
  destruct (period_run false bytes sh9 (natToWord 4 14) (natToWord 4 9) s9 started H9)
    as [st9 ->].
  cbn [fst snd]. rewrite tx_out_stop_bit, report_last_stop_bit_end.
  exists (shift_right sh9).
  unfold frame, bit_time. cbn [word_bits]. rewrite app_assoc. reflexivity.
Qed.

(** The bytes the report sends, first to last: the low byte of [bytes], then
    the low byte of what comes down after it, and so on. *)
Fixpoint report_byte_list (n : nat) (bytes : word 120) : list (word 8) :=
  match n with
  | O => nil
  | S n' => low_byte bytes :: report_byte_list n' (next_bytes bytes)
  end.

Lemma bytes_run : forall k j bytes sh sts started,
  (j + k = 14)%nat -> List.length sts = (1740 * S k)%nat ->
  exists tf,
    tx_run (byte_start j bytes sh) started sts =
    (flat_map frame (report_byte_list (S k) bytes), tf) /\
    tx_active tf = false /\ tx_done tf = true.
Proof.
  induction k as [|k IH]; intros j bytes sh sts started Hj Hlen.
  - replace j with 14%nat by lia.
    destruct (last_byte_run bytes sh sts started ltac:(lia)) as [sh' ->].
    eexists. split; [cbn [report_byte_list flat_map]; rewrite app_nil_r; reflexivity|].
    split; reflexivity.
  - destruct (split_length sts 1740 (1740 * S k) ltac:(lia)) as (s1 & r1 & -> & H1 & Hr1).
    rewrite tx_run_app.
    destruct (byte_run j bytes sh s1 started ltac:(lia) H1) as [sh' ->].
    cbn [fst snd].
    destruct (IH (S j) (next_bytes bytes) sh' r1 started ltac:(lia) Hr1)
      as (tf & -> & Ha & Hd).
    exists tf. split; [reflexivity|]. split; assumption.
Qed.

(** * The report *)

(** report_transmits. The loader has started the CPU and has not reported.
    In the first cycle in which the CPU reports halted or in error, the line
    is still idle and the report rule latches the status. For the next
    15 * 10 * 174 cycles the line carries the frames of the fifteen bytes,
    the status the CPU gave in that first cycle, whatever it reports
    afterwards; then the report is done. *)
Theorem report_transmits : forall bytes sh idx bit clk st0 sts,
  st_halted st0 || st_err st0 = true -> List.length sts = (15 * 10 * ClksPerBit)%nat ->
  exists tf,
    tx_run (mk_tx false false bytes sh idx bit clk) true (st0 :: sts) =
    (true :: flat_map frame (report_byte_list 15 (report_frame st0)), tf) /\
    tx_active tf = false /\ tx_done tf = true.
Proof.
  intros bytes sh idx bit clk st0 sts Hhe Hlen.
  cbn [tx_run]. rewrite tx_out_idle, (report_begin bytes sh idx bit clk st0 Hhe).
  unfold ClksPerBit in Hlen.
  destruct (bytes_run 14 0 (report_frame st0) sh sts true eq_refl ltac:(lia))
    as (tf & Hrun & Ha & Hd).
  unfold byte_start in Hrun. rewrite Hrun. exists tf. auto.
Qed.

(** After the report the line stays idle and the registers stay put. *)
Theorem report_done_stays : forall tf sts started,
  tx_active tf = false -> tx_done tf = true ->
  tx_run tf started sts = (repeat true (List.length sts), tf).
Proof.
  intros [a d bytes sh idx bit clk] sts started Ha Hd. cbn in Ha, Hd. subst a d.
  change (tx_run (mk_tx false true bytes sh idx bit clk) started sts =
          (repeat true (List.length sts), mk_tx false true bytes sh idx bit clk)).
  induction sts as [|st rest IH]; [reflexivity|].
  cbn [tx_run]. rewrite report_done_idle, IH, tx_out_idle. reflexivity.
Qed.

(** Before the CPU halts or errs, the report does not start. *)
Theorem report_waits : forall bytes sh idx bit clk st started,
  st_halted st = false -> st_err st = false ->
  report_step (mk_tx false false bytes sh idx bit clk) started st =
  mk_tx false false bytes sh idx bit clk.
Proof.
  intros bytes sh idx bit clk [h e c pc mu ec] started Hh He. cbn in Hh, He. subst h e.
  destruct started, c; lazy; reflexivity.
Qed.

(** * What the fifteen bytes say *)

Definition le_bytes32 (w : word 32) : list (word 8) := split_bytes 4 w.

Theorem report_bytes_fields : forall st,
  report_byte_list 15 (report_frame st) =
  natToWord 8 222 :: status_byte (st_halted st) (st_err st) (st_certified st) ::
  le_bytes32 (st_pc st) ++ le_bytes32 (st_mu st) ++ le_bytes32 (st_ec st) ++
  natToWord 8 173 :: nil.
Proof.
  intros [h e c pc mu ec]. cbn [st_halted st_err st_certified st_pc st_mu st_ec].
  unfold WordSz in pc, mu, ec. shatter_word pc. shatter_word mu. shatter_word ec.
  destruct h, e, c; lazy; reflexivity.
Qed.

(** The status byte: bit 0 halted, bit 1 error, bit 2 certified, as a
    number. *)
Theorem status_byte_value : forall h e c,
  wordToNat (status_byte h e c) =
  ((if h then 1 else 0) + 2 * (if e then 1 else 0) + 4 * (if c then 1 else 0))%nat.
Proof. intros h e c; destruct h, e, c; reflexivity. Qed.

(** * The CPU's status getters *)

Definition cpu_method (i : nat) : DefMethT := nth i (getDefsBodies thieleCore) no_method.

Lemma cpu_getter_names :
  attrName (cpu_method 2) = "getPC" /\ attrName (cpu_method 3) = "getMu" /\
  attrName (cpu_method 4) = "getErr" /\ attrName (cpu_method 5) = "getHalted" /\
  attrName (cpu_method 6) = "getCertified" /\ attrName (cpu_method 18) = "getErrorCode".
Proof. repeat split; reflexivity. Qed.

Definition get_pc_action : ActionT type (Bit WordSz) := projT2 (attrType (cpu_method 2)) type WO.
Definition get_mu_action : ActionT type (Bit WordSz) := projT2 (attrType (cpu_method 3)) type WO.
Definition get_err_action : ActionT type Bool := projT2 (attrType (cpu_method 4)) type WO.
Definition get_halted_action : ActionT type Bool := projT2 (attrType (cpu_method 5)) type WO.
Definition get_certified_action : ActionT type Bool := projT2 (attrType (cpu_method 6)) type WO.
Definition get_error_code_action : ActionT type (Bit WordSz) :=
  projT2 (attrType (cpu_method 18)) type WO.

(** The status the getters return on the CPU registers [b]. *)
Definition status_of (b : HWB) : Status :=
  {| st_halted := hw_halted b; st_err := hw_err b; st_certified := hw_certified b;
     st_pc := hw_pc b; st_mu := hw_mu b; st_ec := hw_error_code b |}.

Ltac getter_proof :=
  let Hl := fresh "Hl" in let He := fresh "He" in let Hs := fresh "Hs" in
  intros ? ? ? ? Hs;
  match type of Hs with SemAction _ ?a _ _ _ =>
    assert (Hl : linear_action a) by (lazy; repeat intro; exact I) end;
  destruct (eval_linear_action_complete _ _ _ _ _ _ Hl Hs) as [He ->];
  lazy in He; injection He as <- <-; auto.

(** Each getter, run on the CPU registers, returns its register and changes
    nothing. *)
Lemma get_pc_returns : forall b u cs v,
  SemAction (hwb_regs b) get_pc_action u cs v -> v = hw_pc b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

Lemma get_mu_returns : forall b u cs v,
  SemAction (hwb_regs b) get_mu_action u cs v -> v = hw_mu b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

Lemma get_err_returns : forall b u cs v,
  SemAction (hwb_regs b) get_err_action u cs v -> v = hw_err b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

Lemma get_halted_returns : forall b u cs v,
  SemAction (hwb_regs b) get_halted_action u cs v ->
  v = hw_halted b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

Lemma get_certified_returns : forall b u cs v,
  SemAction (hwb_regs b) get_certified_action u cs v ->
  v = hw_certified b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

Lemma get_error_code_returns : forall b u cs v,
  SemAction (hwb_regs b) get_error_code_action u cs v ->
  v = hw_error_code b /\ u = M.empty _ /\ cs = M.empty _.
Proof. getter_proof. Qed.

(** The six getters run on any CPU registers. *)
Lemma getters_run : forall b,
  SemAction (hwb_regs b) get_pc_action (M.empty _) (M.empty _) (hw_pc b) /\
  SemAction (hwb_regs b) get_mu_action (M.empty _) (M.empty _) (hw_mu b) /\
  SemAction (hwb_regs b) get_err_action (M.empty _) (M.empty _) (hw_err b) /\
  SemAction (hwb_regs b) get_halted_action (M.empty _) (M.empty _) (hw_halted b) /\
  SemAction (hwb_regs b) get_certified_action (M.empty _) (M.empty _) (hw_certified b) /\
  SemAction (hwb_regs b) get_error_code_action (M.empty _) (M.empty _) (hw_error_code b).
Proof.
  intro b. repeat split; apply eval_linear_action_sound; lazy; reflexivity.
Qed.

(** * The report against the kernel state *)

(** report_bytes_kernel. With the CPU registers [b] and the kernel state
    [s] the abstraction gives for them, the fifteen bytes are 0xDE, the
    status byte (halted, the kernel's error flag, the kernel's certified
    flag), the kernel's program counter and ledger and the CPU's error code
    as 32-bit words, least significant byte first, and 0xAD. *)
Theorem report_bytes_kernel : forall b,
  let s := abs_phase1 (hwb_snapshot b) in
  report_byte_list 15 (report_frame (status_of b)) =
  natToWord 8 222 :: status_byte (hw_halted b) (vm_err s) (vm_certified s) ::
  le_bytes32 (natToWord 32 (vm_pc s)) ++ le_bytes32 (natToWord 32 (vm_mu s)) ++
  le_bytes32 (natToWord 32 (snap_error_code (hwb_snapshot b))) ++
  natToWord 8 173 :: nil.
Proof.
  intros b s. rewrite report_bytes_fields. unfold s.
  cbn [abs_phase1 hwb_snapshot vm_pc vm_mu vm_err vm_certified snap_pc snap_mu snap_err
       snap_certified snap_error_code status_of st_halted st_err st_certified st_pc st_mu
       st_ec].
  unfold WordSz. rewrite !natToWord_wordToNat. reflexivity.
Qed.

(** * The host's receiver reads the fifteen bytes back *)

Lemma rx_bytes_app : forall xs ys r,
  rx_bytes r (xs ++ ys) = rx_bytes r xs ++ rx_bytes (rx_run r xs) ys.
Proof.
  induction xs as [|x xs IH]; intros ys r; [reflexivity|].
  cbn [app rx_bytes rx_run]. rewrite IH, app_assoc. reflexivity.
Qed.

Lemma rx_frames : forall bs s, rx_bytes (rx_idle s) (flat_map frame bs) = bs.
Proof.
  induction bs as [|b bs IH]; intros s; [reflexivity|].
  cbn [flat_map]. rewrite rx_bytes_app, frame_rx_bytes, frame_rx_state, IH.
  reflexivity.
Qed.

Lemma rx_idle_high : forall s, rx_step (rx_idle s) true = rx_idle s /\ rx_done (rx_idle s) = false.
Proof. intro s. shatter_word s. split; vm_compute; reflexivity. Qed.

(** serial_status_report. The CPU registers [b] are halted or in error in
    the first cycle after the loader has started the CPU and before it has
    reported. Running the report rule once per cycle for the next
    1 + 15 * 10 * 174 cycles, with the getters returning [b] in the first
    of them and anything afterwards, the line is idle for one cycle and
    then carries the frames of the fifteen bytes of [report_bytes_kernel];
    a receiver of the loader's design that starts idle reads exactly those
    bytes; and the line stays idle from then on. *)
Theorem serial_status_report : forall b bytes sh idx bit clk sts rx0,
  hw_halted b || hw_err b = true -> List.length sts = (15 * 10 * ClksPerBit)%nat ->
  let s := abs_phase1 (hwb_snapshot b) in
  let report := natToWord 8 222 :: status_byte (hw_halted b) (vm_err s) (vm_certified s) ::
                le_bytes32 (natToWord 32 (vm_pc s)) ++ le_bytes32 (natToWord 32 (vm_mu s)) ++
                le_bytes32 (natToWord 32 (snap_error_code (hwb_snapshot b))) ++
                natToWord 8 173 :: nil in
  exists tf,
    tx_run (mk_tx false false bytes sh idx bit clk) true (status_of b :: sts) =
      (true :: flat_map frame report, tf) /\
    rx_bytes (rx_idle rx0) (true :: flat_map frame report) = report /\
    (forall later started, tx_run tf started later = (repeat true (List.length later), tf)).
Proof.
  intros b bytes sh idx bit clk sts rx0 Hhe Hlen s report.
  destruct (report_transmits bytes sh idx bit clk (status_of b) sts Hhe Hlen)
    as (tf & Hrun & Ha & Hd).
  rewrite report_bytes_kernel in Hrun.
  exists tf. split; [exact Hrun|]. split.
  - destruct (rx_idle_high rx0) as [Hstep Hdone].
    cbn [rx_bytes]. rewrite Hdone, Hstep. apply rx_frames.
  - intros later started. apply report_done_stays; assumption.
Qed.


(** LoaderSerial: what the serial loader of [ThieleLoader] does with a
    program sent over the pin, and how the program reaches the CPU.

    [step] is one call of the loader's [rxSample] method, computed by
    [ActionEvaluator] from the Kami method itself; [step_is_rxSample] states
    that every step is a [SemAction] of that method. The state is the
    sixteen registers the method reads and writes: the receiver ([Rx]) and
    the program assembler with its hand-off registers ([Prog]).
    [loader_reset_registers] states that [rx_reset] and [prog_reset] are the
    Kami reset values of those registers.

    One byte. [frame v] is the waveform of byte [v] on the line: a low start
    bit, eight data bits least significant first, and a high stop bit, each
    held for [ClksPerBit] cycles. [one_frame]: from an idle receiver,
    whatever byte it holds, the frame leaves the receiver idle holding [v]
    and changes the program registers exactly once, by [byte_step].
    [frames] composes frames sent back to back.

    One program. The host sends the instruction count as two bytes, low
    first, then each instruction as sixteen bytes, least significant first.
    [program_load] and [serial_program_load]: for a program of 1 to 128
    instructions, after the count and instructions 0 to k the loader holds
    instruction k at address k, with [load_req] flipped once per
    instruction, and after the last one it requests the start.

    The hand-off. [load_rule_hands_off]: the [load] rule calls the CPU's
    [loadInstr] with exactly the held address and word and acknowledges the
    request. [load_instr_writes]: [loadInstr] writes the word into
    instruction memory at that address. Kami's semantics allow a rule to
    fire whenever its guard holds and say nothing about when it fires, so
    the file does not state that [load] takes every word before the next
    replaces it; each word stays held while the next sixteen bytes arrive. *)
Require Import Kami.Kami Kami.Semantics.
From KamiHW Require Import ThieleTypes ThieleCPUCore ThieleLoader ActionEvaluator.
From Coq Require Import List String Lia PeanoNat.
Import ListNotations.
Open Scope string_scope.

(** A method body that does nothing, used only as the default of [nth]. *)
Definition no_method : DefMethT :=
  {| attrName := "none";
     attrType := existT MethodT {| arg := Void; ret := Void |}
                   (fun ty (_ : fullType ty (SyntaxKind Void)) =>
                      Return (Const ty (natToWord 0 0))) |}.

Definition rx_sample_method : DefMethT :=
  nth 0 (getDefsBodies thieleLoader) no_method.

Lemma rx_sample_method_name : attrName rx_sample_method = "rxSample".
Proof. reflexivity. Qed.

Lemma rx_sample_method_in : In rx_sample_method (getDefsBodies thieleLoader).
Proof. unfold rx_sample_method. apply nth_In. cbn. repeat constructor. Qed.

Definition rx_sample_action (pin : bool) : ActionT type Void :=
  projT2 (attrType rx_sample_method) type pin.

Lemma rx_sample_action_linear : forall pin, linear_action (rx_sample_action pin).
Proof.
  intro pin. unfold rx_sample_action, rx_sample_method. cbn.
  repeat (cbn [linear_action]; intro).
  exact I.
Qed.

(** The receiver registers. *)
Record Rx := {
  rx_sync1 : bool; rx_sync2 : bool; rx_state : word 2;
  rx_clk : word 8; rx_bit : word 3; rx_shift : word 8 }.

(** The program registers and the hand-off to the CPU. *)
Record Prog := {
  ld_phase : word 2; ld_count_lo : word 8; ld_count_hi : word 8;
  ld_index : word 8; ld_byte : word 4; ld_accum : word InstrSz;
  load_req : bool; load_addr : word MemAddrSz; load_data : word InstrSz;
  start_req : bool }.

Notation SK k v := (existT (fullType type) (SyntaxKind k) v).

Definition regs (r : Rx) (p : Prog) : RegsT :=
  M.add "rx_sync1" (SK Bool (rx_sync1 r)) (M.add "rx_sync2" (SK Bool (rx_sync2 r))
  (M.add "rx_state" (SK (Bit 2) (rx_state r)) (M.add "rx_clk" (SK (Bit 8) (rx_clk r))
  (M.add "rx_bit" (SK (Bit 3) (rx_bit r)) (M.add "rx_shift" (SK (Bit 8) (rx_shift r))
  (M.add "ld_phase" (SK (Bit 2) (ld_phase p))
  (M.add "ld_count_lo" (SK (Bit 8) (ld_count_lo p))
  (M.add "ld_count_hi" (SK (Bit 8) (ld_count_hi p))
  (M.add "ld_index" (SK (Bit 8) (ld_index p))
  (M.add "ld_byte" (SK (Bit 4) (ld_byte p))
  (M.add "ld_accum" (SK (Bit InstrSz) (ld_accum p))
  (M.add "load_req" (SK Bool (load_req p))
  (M.add "load_addr" (SK (Bit MemAddrSz) (load_addr p))
  (M.add "load_data" (SK (Bit InstrSz) (load_data p))
  (M.add "start_req" (SK Bool (start_req p))
  (M.empty _)))))))))))))))).

Definition read_or {k : Kind} (m : RegsT) (name : string) (d : type k) : type k :=
  match action_read m name (SyntaxKind k) with Some v => v | None => d end.

(** The registers after the method's updates [u]. *)
Definition after (u : UpdatesT) (r : Rx) (p : Prog) : Rx * Prog :=
  let m := M.union u (regs r p) in
  ({| rx_sync1 := @read_or Bool m "rx_sync1" (rx_sync1 r);
      rx_sync2 := @read_or Bool m "rx_sync2" (rx_sync2 r);
      rx_state := @read_or (Bit 2) m "rx_state" (rx_state r);
      rx_clk := @read_or (Bit 8) m "rx_clk" (rx_clk r);
      rx_bit := @read_or (Bit 3) m "rx_bit" (rx_bit r);
      rx_shift := @read_or (Bit 8) m "rx_shift" (rx_shift r) |},
   {| ld_phase := @read_or (Bit 2) m "ld_phase" (ld_phase p);
      ld_count_lo := @read_or (Bit 8) m "ld_count_lo" (ld_count_lo p);
      ld_count_hi := @read_or (Bit 8) m "ld_count_hi" (ld_count_hi p);
      ld_index := @read_or (Bit 8) m "ld_index" (ld_index p);
      ld_byte := @read_or (Bit 4) m "ld_byte" (ld_byte p);
      ld_accum := @read_or (Bit InstrSz) m "ld_accum" (ld_accum p);
      load_req := @read_or Bool m "load_req" (load_req p);
      load_addr := @read_or (Bit MemAddrSz) m "load_addr" (load_addr p);
      load_data := @read_or (Bit InstrSz) m "load_data" (load_data p);
      start_req := @read_or Bool m "start_req" (start_req p) |}).

(** One clock cycle: one call of [rxSample] with the pin's level. *)
Definition step (s : Rx * Prog) (pin : bool) : Rx * Prog :=
  let (r, p) := s in
  match eval_linear_action (regs r p) (rx_sample_action pin) with
  | Some (u, _) => after u r p
  | None => s
  end.

(** The method always runs on these registers: every [step] is a
    [SemAction] of [rxSample], with the updates [step] applies. *)
Lemma rx_sample_eval_some : forall r p pin,
  exists u, eval_linear_action (regs r p) (rx_sample_action pin) = Some (u, WO).
Proof.
  intros r p pin.
  assert (H : match eval_linear_action (regs r p) (rx_sample_action pin) with
              | Some _ => true | None => false end = true)
    by (destruct r, p; vm_compute; reflexivity).
  destruct (eval_linear_action (regs r p) (rx_sample_action pin)) as [[u v]|];
    [|discriminate].
  exists u. rewrite (shatter_word_0 v). reflexivity.
Qed.

Theorem step_is_rxSample : forall r p pin, exists u,
  SemAction (regs r p) (rx_sample_action pin) u (M.empty _) WO /\ step (r, p) pin = after u r p.
Proof.
  intros r p pin. destruct (rx_sample_eval_some r p pin) as [u E].
  exists u. split.
  - apply eval_linear_action_sound. exact E.
  - unfold step. rewrite E. reflexivity.
Qed.

(** The same function with the register map evaluated away: the normal
    form of [step] on arbitrary registers. Computing with it costs no map
    operations; [step_fast_eq] states that it is [step]. *)
Definition step_fast : Rx -> Prog -> bool -> Rx * Prog :=
  Eval vm_compute in (fun r p pin => step (r, p) pin).

Lemma step_fast_eq : forall r p pin, step (r, p) pin = step_fast r p pin.
Proof. intros r p pin. vm_compute. reflexivity. Qed.

Fixpoint run (s : Rx * Prog) (samples : list bool) : Rx * Prog :=
  match samples with
  | nil => s
  | x :: xs => run (step s x) xs
  end.

(** The bits of a word, least significant first. *)
Fixpoint word_bits {n} (w : word n) : list bool :=
  match w with
  | WO => nil
  | WS b w' => b :: word_bits w'
  end.

Definition bit_time (level : bool) : list bool := repeat level ClksPerBit.

Definition frame (v : word 8) : list bool :=
  bit_time false ++ flat_map bit_time (word_bits v) ++ bit_time true.

(** The receiver waiting for a start bit, holding [s] from the last byte. *)
Definition rx_idle (s : word 8) : Rx :=
  {| rx_sync1 := true; rx_sync2 := true; rx_state := natToWord 2 0;
     rx_clk := natToWord 8 0; rx_bit := natToWord 3 0; rx_shift := s |}.

(** The receiver at the middle of a high stop bit with [v] assembled: the
    cycle at which [rxSample] completes a byte. *)
Definition rx_byte_done (v : word 8) : Rx :=
  {| rx_sync1 := true; rx_sync2 := true; rx_state := natToWord 2 3;
     rx_clk := bit_last; rx_bit := natToWord 3 0; rx_shift := v |}.

(** What a completed byte [v] does to the program registers. *)
Definition byte_step (p : Prog) (v : word 8) : Prog :=
  snd (step_fast (rx_byte_done v) p true).

(** The program registers at reset. *)
Definition prog_reset : Prog :=
  {| ld_phase := natToWord 2 0; ld_count_lo := natToWord 8 0;
     ld_count_hi := natToWord 8 0; ld_index := natToWord 8 0;
     ld_byte := natToWord 4 0; ld_accum := natToWord InstrSz 0;
     load_req := false; load_addr := natToWord MemAddrSz 0;
     load_data := natToWord InstrSz 0; start_req := false |}.

(** The receiver's next state. It does not depend on the program
    registers ([step_rx]). *)
Definition rx_step (r : Rx) (pin : bool) : Rx := fst (step_fast r prog_reset pin).

Lemma step_rx : forall r p pin, fst (step_fast r p pin) = rx_step r pin.
Proof. intros r p pin. destruct r, p. vm_compute. reflexivity. Qed.

Definition word_eqb {n} (a b : word n) : bool := if weq a b then true else false.

(** [rxSample]'s condition for a completed byte: the stop bit, high, at the
    middle of its bit time. *)
Definition rx_done (r : Rx) : bool :=
  word_eqb (rx_state r) (natToWord 2 3) && word_eqb (rx_clk r) bit_last && rx_sync2 r.

(** The program registers change only on the cycle a byte completes, and
    then by [byte_step] of the received byte. *)
Lemma step_prog : forall r p pin,
  snd (step_fast r p pin) = if rx_done r then byte_step p (rx_shift r) else p.
Proof.
  intros [s1 s2 st c bt sh] p pin.
  unfold rx_done, word_eqb; cbn [rx_state rx_clk rx_sync2 rx_shift].
  destruct (weq st (natToWord 2 3)) as [->|Hst].
  - destruct (weq c bit_last) as [->|Hc].
    + destruct s2; cbn [andb].
      * unfold byte_step. destruct p. vm_compute. reflexivity.
      * destruct p. vm_compute. reflexivity.
    + cbn [andb]. revert s1 pin s2. shatter_word c.
      repeat match goal with b : bool |- _ => destruct b end;
        intros s1 pin s2;
        first [exfalso; apply Hc; reflexivity
              |destruct p; vm_compute; reflexivity].
  - cbn [andb]. revert s1 pin s2. shatter_word st.
    repeat match goal with b : bool |- _ => destruct b end;
      intros s1 pin s2;
      first [exfalso; apply Hst; reflexivity
            |destruct p; vm_compute; reflexivity].
Qed.
Fixpoint rx_run (r : Rx) (samples : list bool) : Rx :=
  match samples with
  | nil => r
  | x :: xs => rx_run (rx_step r x) xs
  end.

(** The bytes the receiver completes, in order. *)
Fixpoint rx_bytes (r : Rx) (samples : list bool) : list (word 8) :=
  match samples with
  | nil => nil
  | x :: xs =>
      (if rx_done r then rx_shift r :: nil else nil) ++ rx_bytes (rx_step r x) xs
  end.

Lemma step_split : forall r p pin,
  step (r, p) pin =
    (rx_step r pin, if rx_done r then byte_step p (rx_shift r) else p).
Proof.
  intros r p pin. rewrite step_fast_eq, <- (step_rx r p pin), <- (step_prog r p pin).
  destruct (step_fast r p pin). reflexivity.
Qed.

(** A run is the receiver's run, with the program registers taking one
    [byte_step] per completed byte. *)
Theorem run_split : forall samples r p,
  run (r, p) samples =
    (rx_run r samples, fold_left byte_step (rx_bytes r samples) p).
Proof.
  induction samples as [|x xs IH]; intros r p; [reflexivity|].
  cbn [run rx_run rx_bytes]. rewrite step_split, IH.
  destruct (rx_done r); reflexivity.
Qed.

(** One frame on the line, from an idle receiver holding any byte. Each
    received bit is the bit of a one-bit word built from the line level; it
    is the level itself in either case, hence the case split on the eight
    data bits after the computation. *)
Lemma frame_rx_state : forall s v : word 8,
  rx_run (rx_idle s) (frame v) = rx_idle v.
Proof.
  intros s v.
  shatter_word v.
  repeat match goal with b : bool |- _ => revert b end.
  intros b0 b1 b2 b3 b4 b5 b6 b7.
  shatter_word s.
  vm_compute.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Lemma frame_rx_bytes : forall s v : word 8,
  rx_bytes (rx_idle s) (frame v) = v :: nil.
Proof.
  intros s v.
  shatter_word v.
  repeat match goal with b : bool |- _ => revert b end.
  intros b0 b1 b2 b3 b4 b5 b6 b7.
  shatter_word s.
  vm_compute.
  destruct b0, b1, b2, b3, b4, b5, b6, b7; reflexivity.
Qed.

Theorem one_frame : forall (s v : word 8) (p : Prog),
  run (rx_idle s, p) (frame v) = (rx_idle v, byte_step p v).
Proof.
  intros s v p. rewrite run_split, frame_rx_state, frame_rx_bytes. reflexivity.
Qed.

Local Open Scope nat_scope.

(** * A program

    The host sends the instruction count N as two bytes, low first, then
    each instruction as sixteen bytes, least significant first. *)

(** Kami's zero extension casts through an opaque arithmetic proof, so it
    does not compute; it equals appending a zero byte. *)
Lemma zext_8_16 : forall w : word 8,
  evalZeroExtendTrunc 16 w = Word.combine w (natToWord 8 0).
Proof.
  intro w. unfold evalZeroExtendTrunc.
  destruct (Compare_dec.lt_dec 8 16) as [l|n]; [|exfalso; apply n; repeat constructor].
  match goal with |- context [eq_rect _ _ _ _ ?H] => generalize H end.
  intro H. cbn in H. rewrite (Eqdep_dec.UIP_refl_nat _ H). reflexivity.
Qed.

(** The bytes of a word of [k] bytes, least significant first. *)
Fixpoint split_bytes (k : nat) : word (k * 8) -> list (word 8) :=
  match k with
  | 0 => fun _ => nil
  | S k' => fun w => split1 8 (k' * 8) w :: split_bytes k' (split2 8 (k' * 8) w)
  end.

Definition bytes_of (w : word InstrSz) : list (word 8) := split_bytes 16 w.

(** The program registers between words: assembling the word at index
    [idx] of a program whose count byte is [lo], with the last hand-off
    ([b], [a], [d]) still in the registers. *)
Definition prog_word (lo idx : word 8) (b : bool) (a : word MemAddrSz)
    (d : word InstrSz) : Prog :=
  {| ld_phase := natToWord 2 2; ld_count_lo := lo; ld_count_hi := natToWord 8 0;
     ld_index := idx; ld_byte := natToWord 4 0; ld_accum := natToWord InstrSz 0;
     load_req := b; load_addr := a; load_data := d; start_req := false |}.

(** The sixteen bytes of [w], as the computation leaves them. *)
Lemma word_bytes_raw : forall lo idx b a d (w : word InstrSz),
  fold_left byte_step (bytes_of w) (prog_word lo idx b a d) =
  let last := word_eqb (evalZeroExtendTrunc 16 (idx ^+ natToWord 8 1))
                       (Word.combine lo (natToWord 8 0)) in
  {| ld_phase := if last then natToWord 2 3 else natToWord 2 2;
     ld_count_lo := lo; ld_count_hi := natToWord 8 0;
     ld_index := idx ^+ natToWord 8 1; ld_byte := natToWord 4 0;
     ld_accum := natToWord InstrSz 0; load_req := negb b;
     load_addr := split2 0 MemAddrSz (split1 (0 + MemAddrSz) 1 idx);
     load_data := w; start_req := if (last || false)%bool then true else false |}.
Proof.
  intros lo idx b a d w. unfold InstrSz in w. shatter_word w.
  vm_compute. reflexivity.
Qed.

(** The sixteen bytes of [w] complete the word: the loader hands [w] to the
    CPU at address [idx] by flipping [load_req], and after the last word
    requests the start. *)
Theorem word_bytes : forall lo idx b a d (w : word InstrSz),
  let last := word_eqb (Word.combine (idx ^+ natToWord 8 1) (natToWord 8 0))
                       (Word.combine lo (natToWord 8 0)) in
  fold_left byte_step (bytes_of w) (prog_word lo idx b a d) =
  {| ld_phase := if last then natToWord 2 3 else natToWord 2 2;
     ld_count_lo := lo; ld_count_hi := natToWord 8 0;
     ld_index := idx ^+ natToWord 8 1; ld_byte := natToWord 4 0;
     ld_accum := natToWord InstrSz 0; load_req := negb b;
     load_addr := split2 0 MemAddrSz (split1 (0 + MemAddrSz) 1 idx);
     load_data := w; start_req := last |}.
Proof.
  intros lo idx b a d w last. rewrite word_bytes_raw. cbv zeta.
  rewrite zext_8_16. subst last.
  destruct (word_eqb _ _); reflexivity.
Qed.

(** The two count bytes, as the computation leaves them. *)
Lemma count_bytes_raw : forall lo hi : word 8,
  fold_left byte_step (lo :: hi :: nil) prog_reset =
  {| ld_phase := if word_eqb (Word.combine lo hi) (natToWord 16 0)
                 then natToWord 2 3 else natToWord 2 2;
     ld_count_lo := lo; ld_count_hi := hi; ld_index := natToWord 8 0;
     ld_byte := natToWord 4 0; ld_accum := natToWord InstrSz 0;
     load_req := false; load_addr := natToWord MemAddrSz 0;
     load_data := natToWord InstrSz 0;
     start_req := if word_eqb (Word.combine lo hi) (natToWord 16 0)
                  then true else false |}.
Proof. intros lo hi. vm_compute. reflexivity. Qed.

Lemma word_eqb_true : forall n (a b : word n), word_eqb a b = true -> a = b.
Proof. intros n a b H. unfold word_eqb in H. destruct (weq a b); congruence. Qed.

Lemma word_eqb_refl : forall n (a : word n), word_eqb a a = true.
Proof. intros n a. unfold word_eqb. destruct (weq a a); congruence. Qed.

(** Index arithmetic for programs of at most 128 instructions, checked for
    every index and count. *)
Lemma next_index_table :
  forallb (fun i => word_eqb (natToWord 8 i ^+ natToWord 8 1) (natToWord 8 (S i)))
          (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma addr_table :
  forallb (fun i => word_eqb (split2 0 MemAddrSz (split1 (0 + MemAddrSz) 1 (natToWord 8 i)))
                             (natToWord MemAddrSz i))
          (seq 0 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma last_table :
  forallb (fun n => forallb (fun i =>
             Bool.eqb (word_eqb (Word.combine (natToWord 8 i ^+ natToWord 8 1) (natToWord 8 0))
                                (Word.combine (natToWord 8 n) (natToWord 8 0)))
                      (Nat.eqb (S i) n))
           (seq 0 128))
          (seq 1 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma count_table :
  forallb (fun n => negb (word_eqb (Word.combine (natToWord 8 n) (natToWord 8 0))
                                   (natToWord 16 0)))
          (seq 1 128) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_range : forall i lo len, lo <= i < lo + len -> In i (seq lo len).
Proof. intros i lo len H. apply in_seq. lia. Qed.

Lemma next_index : forall i, i < 128 ->
  natToWord 8 i ^+ natToWord 8 1 = natToWord 8 (S i).
Proof.
  intros i Hi. apply word_eqb_true.
  pose proof next_index_table as H. rewrite forallb_forall in H.
  apply H, in_range. lia.
Qed.

Lemma addr_of : forall i, i < 128 ->
  split2 0 MemAddrSz (split1 (0 + MemAddrSz) 1 (natToWord 8 i)) = natToWord MemAddrSz i.
Proof.
  intros i Hi. apply word_eqb_true.
  pose proof addr_table as H. rewrite forallb_forall in H.
  apply H, in_range. lia.
Qed.

Lemma last_of : forall n i, 1 <= n <= 128 -> i < 128 ->
  word_eqb (Word.combine (natToWord 8 i ^+ natToWord 8 1) (natToWord 8 0))
           (Word.combine (natToWord 8 n) (natToWord 8 0)) = Nat.eqb (S i) n.
Proof.
  intros n i Hn Hi.
  pose proof last_table as H. rewrite forallb_forall in H.
  specialize (H n (in_range n 1 128 ltac:(lia))).
  rewrite forallb_forall in H. specialize (H i (in_range i 0 128 ltac:(lia))).
  apply Bool.eqb_prop in H. exact H.
Qed.

Lemma count_of : forall n, 1 <= n <= 128 ->
  word_eqb (Word.combine (natToWord 8 n) (natToWord 8 0)) (natToWord 16 0) = false.
Proof.
  intros n Hn.
  pose proof count_table as H. rewrite forallb_forall in H.
  specialize (H n (in_range n 1 128 ltac:(lia))).
  destruct (word_eqb _ _); [discriminate|reflexivity].
Qed.

(** The program registers after each word of [ws]. *)
Fixpoint load_states (p : Prog) (ws : list (word InstrSz)) : list Prog :=
  match ws with
  | nil => nil
  | w :: ws' =>
      let p' := fold_left byte_step (bytes_of w) p in p' :: load_states p' ws'
  end.

Lemma load_states_spec : forall n ws i b a d,
  1 <= n <= 128 -> i + List.length ws = n ->
  forall k w, nth_error ws k = Some w ->
  exists p,
    nth_error (load_states (prog_word (natToWord 8 n) (natToWord 8 i) b a d) ws) k = Some p /\
    load_addr p = natToWord MemAddrSz (i + k) /\ load_data p = w /\
    load_req p = (if Nat.even k then negb b else b) /\
    start_req p = Nat.eqb (S (i + k)) n /\
    ld_phase p = (if Nat.eqb (S (i + k)) n then natToWord 2 3 else natToWord 2 2).
Proof.
  intros n ws. induction ws as [|w0 ws IH]; intros i b a d Hn Hlen k w Hk.
  - destruct k; discriminate.
  - cbn [List.length] in Hlen. assert (Hi : i < 128) by lia.
    cbn [load_states]. rewrite word_bytes, (last_of n i Hn Hi), (next_index i Hi), (addr_of i Hi).
    destruct k as [|k].
    + cbn in Hk. injection Hk as <-. eexists. split; [reflexivity|].
      cbn [load_addr load_data load_req start_req ld_phase].
      rewrite Nat.add_0_r. repeat split; reflexivity.
    + cbn in Hk. destruct (Nat.eqb (S i) n) eqn:E.
      * apply Nat.eqb_eq in E. destruct ws; [destruct k; discriminate|].
        cbn [List.length] in Hlen. lia.
      * replace {| ld_phase := if false then natToWord 2 3 else natToWord 2 2;
                   ld_count_lo := natToWord 8 n; ld_count_hi := natToWord 8 0;
                   ld_index := natToWord 8 (S i); ld_byte := natToWord 4 0;
                   ld_accum := natToWord InstrSz 0; load_req := negb b;
                   load_addr := natToWord MemAddrSz i; load_data := w0;
                   start_req := false |}
          with (prog_word (natToWord 8 n) (natToWord 8 (S i)) (negb b)
                          (natToWord MemAddrSz i) w0) by reflexivity.
        destruct (IH (S i) (negb b) (natToWord MemAddrSz i) w0 Hn ltac:(lia) k w Hk)
          as (p & Hp & Ha & Hd & Hr & Hs & Hph).
        exists p. cbn [nth_error]. split; [exact Hp|].
        replace (i + S k) with (S i + k) by lia.
        split; [exact Ha|]. split; [exact Hd|]. split; [|split; assumption].
        rewrite Hr, Nat.even_succ, <- Nat.negb_even.
        destruct (Nat.even k); cbn; [rewrite Bool.negb_involutive|]; reflexivity.
Qed.

(** The bytes the host sends for program [ws]. *)
Definition program_stream (ws : list (word InstrSz)) : list (word 8) :=
  natToWord 8 (List.length ws) :: natToWord 8 0 :: flat_map bytes_of ws.

(** The program registers once both count bytes of a program of [n]
    instructions, [n] from 1 to 128, have arrived. *)
Definition prog_counted (n : nat) : Prog :=
  prog_word (natToWord 8 n) (natToWord 8 0) false (natToWord MemAddrSz 0)
            (natToWord InstrSz 0).

Lemma count_bytes : forall n, 1 <= n <= 128 ->
  fold_left byte_step (natToWord 8 n :: natToWord 8 0 :: nil) prog_reset = prog_counted n.
Proof.
  intros n Hn. rewrite count_bytes_raw, (count_of n Hn). reflexivity.
Qed.

Lemma load_states_prefix : forall ws p k w,
  nth_error ws k = Some w ->
  nth_error (load_states p ws) k =
    Some (fold_left byte_step (flat_map bytes_of (firstn (S k) ws)) p).
Proof.
  induction ws as [|w0 ws IH]; intros p k w Hk; [destruct k; discriminate|].
  destruct k as [|k].
  - cbn [nth_error load_states firstn flat_map]. rewrite app_nil_r. reflexivity.
  - cbn [nth_error load_states firstn flat_map]. rewrite fold_left_app.
    exact (IH _ k w Hk).
Qed.

Lemma fold_left_cons2 : forall (f : Prog -> word 8 -> Prog) a b l x,
  fold_left f (a :: b :: l) x = fold_left f l (fold_left f (a :: b :: nil) x).
Proof. reflexivity. Qed.

(** A program of 1 to 128 instructions, byte by byte. After the count and
    the bytes of instructions 0 to k, the loader holds instruction k at
    address k for the CPU, with [load_req] flipped once per instruction,
    and it requests the start exactly after the last instruction. *)
Theorem program_load : forall ws k w,
  1 <= List.length ws <= 128 -> nth_error ws k = Some w ->
  let p := fold_left byte_step
             (natToWord 8 (List.length ws) :: natToWord 8 0 :: flat_map bytes_of (firstn (S k) ws))
             prog_reset in
  load_addr p = natToWord MemAddrSz k /\ load_data p = w /\
  load_req p = Nat.even k /\ start_req p = Nat.eqb (S k) (List.length ws) /\
  ld_phase p = (if Nat.eqb (S k) (List.length ws) then natToWord 2 3 else natToWord 2 2).
Proof.
  intros ws k w Hn Hk. cbv zeta. rewrite fold_left_cons2.
  rewrite (count_bytes _ Hn). unfold prog_counted.
  destruct (load_states_spec (List.length ws) ws 0 false (natToWord MemAddrSz 0)
              (natToWord InstrSz 0) Hn eq_refl k w Hk)
    as (p & Hp & Ha & Hd & Hr & Hs & Hph).
  rewrite (load_states_prefix ws _ k w Hk) in Hp.
  assert (Hq : fold_left byte_step (flat_map bytes_of (firstn (S k) ws))
                 (prog_word (natToWord 8 (List.length ws)) (natToWord 8 0) false
                            (natToWord MemAddrSz 0) (natToWord InstrSz 0)) = p)
    by congruence.
  rewrite Hq.
  rewrite Nat.add_0_l in Ha, Hs, Hph.
  repeat split; try assumption.
  rewrite Hr. destruct (Nat.even k); reflexivity.
Qed.

(** An empty program: the count alone requests the start. *)
Theorem empty_program_starts :
  start_req (fold_left byte_step (program_stream nil) prog_reset) = true /\
  ld_phase (fold_left byte_step (program_stream nil) prog_reset) = natToWord 2 3.
Proof. vm_compute. split; reflexivity. Qed.

(** * The serial line *)

Lemma run_app : forall xs ys s, run s (xs ++ ys) = run (run s xs) ys.
Proof. induction xs as [|x xs IH]; intros ys s; [reflexivity|]. exact (IH ys (step s x)). Qed.

Lemma last_cons_default : forall (bs : list (word 8)) b s, last (b :: bs) s = last bs b.
Proof.
  induction bs as [|c bs IH]; intros b s; [reflexivity|].
  change (last (c :: bs) s = last (c :: bs) b).
  rewrite (IH c s), (IH c b). reflexivity.
Qed.

(** Frames sent back to back: the receiver completes each byte in turn and
    the program registers take one [byte_step] per byte. *)
Theorem frames : forall bs s p,
  run (rx_idle s, p) (flat_map frame bs) = (rx_idle (last bs s), fold_left byte_step bs p).
Proof.
  induction bs as [|b bs IH]; intros s p; [reflexivity|].
  cbn [flat_map]. rewrite run_app, one_frame, IH, last_cons_default. reflexivity.
Qed.

(** The loader's reset values of the sixteen registers. *)
Definition rx_reset : Rx := rx_idle (natToWord 8 0).

(** These are the loader's reset values: the Kami register initializers
    give exactly [regs rx_reset prog_reset] on the sixteen registers. *)
Definition loader_reset_state : RegsT := initRegs (getRegInits thieleLoader).

Lemma loader_reset_registers : forall k,
  In k ["rx_sync1"; "rx_sync2"; "rx_state"; "rx_clk"; "rx_bit"; "rx_shift";
        "ld_phase"; "ld_count_lo"; "ld_count_hi"; "ld_index"; "ld_byte"; "ld_accum";
        "load_req"; "load_addr"; "load_data"; "start_req"] ->
  M.find k loader_reset_state = M.find k (regs rx_reset prog_reset).
Proof.
  intros k Hk.
  repeat (destruct Hk as [<-|Hk]; [vm_compute; reflexivity|]).
  destruct Hk.
Qed.

(** A program of 1 to 128 instructions sent over the pin from reset: after
    the frames of the count and of instructions 0 to k, the loader holds
    instruction k at address k for the CPU, and after the last one it
    requests the start. Every cycle of the run is a call of the Kami method
    [rxSample] ([step_is_rxSample]). *)
Theorem serial_program_load : forall ws k w,
  1 <= List.length ws <= 128 -> nth_error ws k = Some w ->
  let p := snd (run (rx_reset, prog_reset)
                 (flat_map frame (natToWord 8 (List.length ws) :: natToWord 8 0 ::
                                  flat_map bytes_of (firstn (S k) ws)))) in
  load_addr p = natToWord MemAddrSz k /\ load_data p = w /\
  load_req p = Nat.even k /\ start_req p = Nat.eqb (S k) (List.length ws).
Proof.
  intros ws k w Hn Hk. cbv zeta. unfold rx_reset. rewrite frames. cbn [snd].
  destruct (program_load ws k w Hn Hk) as (Ha & Hd & Hr & Hs & _).
  repeat split; assumption.
Qed.

(** * The hand-off to the CPU *)

Definition no_rule : Attribute (Action Void) :=
  {| attrName := "none"; attrType := fun ty => Return (Const ty (natToWord 0 0)) |}.

Definition load_rule : Attribute (Action Void) := nth 0 (getRules thieleLoader) no_rule.

Lemma load_rule_name : attrName load_rule = "load".
Proof. reflexivity. Qed.

Definition load_action : ActionT type Void := attrType load_rule type.

(** The argument of [loadInstr]: an instruction word and its address. *)
Definition load_port (a : word MemAddrSz) (d : word InstrSz) : type (Struct LoadInstrPort) :=
  evalExpr (STRUCT { "addr" ::= Var type (SyntaxKind (Bit MemAddrSz)) a;
                     "data" ::= Var type (SyntaxKind (Bit InstrSz)) d })%kami_expr.

Definition loadInstrSigT : SignatureT := {| arg := Struct LoadInstrPort; ret := Void |}.

Lemma find_same : forall (m : RegsT) r k (v1 v2 : type k),
  M.find r m = Some (SK k v1) -> M.find r m = Some (SK k v2) -> v1 = v2.
Proof.
  intros m r k v1 v2 H1 H2.
  apply action_read_complete in H1. apply action_read_complete in H2. congruence.
Qed.

(** When the [load] rule runs, a request is pending, its one call is
    [loadInstr] with the address and word the loader holds, and it
    acknowledges the request. *)
Theorem load_rule_hands_off : forall old u cs ret lr la a d,
  M.find "load_req" old = Some (SK Bool lr) ->
  M.find "load_ack" old = Some (SK Bool la) ->
  M.find "load_addr" old = Some (SK (Bit MemAddrSz) a) ->
  M.find "load_data" old = Some (SK (Bit InstrSz) d) ->
  SemAction old load_action u cs ret ->
  lr <> la /\
  (exists mret, cs = M.add "loadInstr" (existT _ loadInstrSigT (load_port a d, mret)) (M.empty _)) /\
  u = M.add "load_ack" (SK Bool lr) (M.empty _).
Proof.
  intros old u cs ret lr la a d Hr Hk Ha Hd H.
  unfold load_action, load_rule in H. cbn in H.
  apply inversionSemAction in H. destruct H as (vr & Hvr & H).
  apply inversionSemAction in H. destruct H as (vk & Hvk & H).
  apply inversionSemAction in H. destruct H as (H & Hassert).
  apply inversionSemAction in H. destruct H as (va & Hva & H).
  apply inversionSemAction in H. destruct H as (vd & Hvd & H).
  apply inversionSemAction in H. destruct H as (mret & pcalls & Hnone & H & ->).
  apply inversionSemAction in H. destruct H as (pnews & Hpn & H & ->).
  apply inversionSemAction in H. destruct H as (_ & -> & ->).
  rewrite <- (find_same _ _ _ _ _ Hr Hvr), <- (find_same _ _ _ _ _ Hk Hvk),
          <- (find_same _ _ _ _ _ Ha Hva), <- (find_same _ _ _ _ _ Hd Hvd) in *.
  split; [|split; [exists mret; reflexivity|reflexivity]].
  cbn in Hassert. destruct lr, la; cbn in Hassert; congruence.
Qed.

Definition load_instr_method : DefMethT := nth 0 (getDefsBodies thieleCore) no_method.

Lemma load_instr_method_name : attrName load_instr_method = "loadInstr".
Proof. reflexivity. Qed.

Definition load_instr_action (x : type (Struct LoadInstrPort)) : ActionT type Void :=
  projT2 (attrType load_instr_method) type x.

(** The CPU's [loadInstr] writes the word into instruction memory at the
    address and does nothing else. *)
Theorem load_instr_writes : forall old imem a d u cs ret,
  M.find "imem" old = Some (SK (Vector (Bit InstrSz) MemAddrSz) imem) ->
  SemAction old (load_instr_action (load_port a d)) u cs ret ->
  cs = M.empty _ /\
  u = M.add "imem" (SK (Vector (Bit InstrSz) MemAddrSz)
                      (fun i => if weq i a then d else imem i)) (M.empty _).
Proof.
  intros old imem a d u cs ret Him H.
  assert (Hl : linear_action (load_instr_action (load_port a d))).
  { unfold load_instr_action, load_instr_method. cbn.
    repeat (cbn [linear_action]; intro). exact I. }
  destruct (eval_linear_action_complete _ _ _ _ _ _ Hl H) as [He ->].
  split; [reflexivity|].
  unfold load_instr_action, load_instr_method in He. cbn in He.
  pose proof (action_read_complete _ _ _ _ Him) as Hr. cbn [action_read] in Hr.
  rewrite Hr in He. injection He as <- _. reflexivity.
Qed.

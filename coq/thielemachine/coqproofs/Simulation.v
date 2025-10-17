(* ================================================================= *)
(* Containment: any classical Turing Machine has a blind Thiele        *)
(* interpreter that reproduces its execution exactly.                  *)
(* ================================================================= *)
From Coq Require Import List Arith Lia PeanoNat Bool.
From ThieleUniversal Require Import TM UTM_Rules.
From ThieleUniversal Require Import CPU UTM_Program.
From ThieleUniversal Require Import ThieleUniversal.
From ThieleUniversal Require Import UTM_Encode.
From ThieleMachine Require Import ThieleMachine EncodingBridge Axioms.
From ThieleMachine.Modular_Proofs Require Import Encoding EncodingBounds.

Import ListNotations.

Local Open Scope nat_scope.

Module EncodingMod := ThieleMachine.Modular_Proofs.Encoding.

(* ----------------------------------------------------------------- *)
(* Encoding TM configurations into minimalist Thiele states           *)
(* ----------------------------------------------------------------- *)

(* Strip factors of two from a natural number, counting how many     *)
(* times it is divisible by two.  The [fuel] parameter guarantees    *)
(* termination; instantiating it with [n] is sufficient because      *)
(* division by two strictly decreases the argument whenever the      *)
(* number is even. *)
Fixpoint strip_pow2_aux (fuel n acc : nat) : nat * nat :=
  match fuel with
  | 0%nat => (acc, n)
  | S fuel' =>
      match n with
      | 0%nat => (acc, 0%nat)
      | S _ =>
          if Nat.even n then strip_pow2_aux fuel' (Nat.div2 n) (S acc)
          else (acc, n)
      end
  end.

Definition encode_config (_tm : TM) (conf : TMConfig) : State :=
  {| pc := tm_encode_config conf |}.

Definition decode_state (_tm : TM) (st : State) : TMConfig :=
  tm_decode_config st.(pc).

Definition config_ok (_tm : TM) (conf : TMConfig) : Prop :=
  tm_config_ok conf.

Definition tm_config_head (conf : TMConfig) : nat :=
  let '(_, _, head) := conf in head.

Lemma decode_encode_id :
  forall tm conf,
    config_ok tm conf ->
    decode_state tm (encode_config tm conf) = conf.
Proof.
  intros tm conf Hconf.
  unfold encode_config, decode_state, config_ok.
  apply tm_decode_encode_roundtrip; assumption.
Qed.

Lemma digits_ok_firstn :
  forall xs n,
    digits_ok xs ->
    digits_ok (firstn n xs).
Proof.
  intros xs n Hdigits.
  unfold digits_ok in *.
  revert n.
  induction Hdigits; intros [|n]; simpl; constructor; auto.
Qed.

Lemma digits_ok_skipn :
  forall xs n,
    digits_ok xs ->
    digits_ok (skipn n xs).
Proof.
  intros xs n Hdigits.
  unfold digits_ok in *.
  revert xs Hdigits.
  induction n as [|n IH]; intros xs Hdigits; simpl; auto.
  destruct xs as [|x xs]; simpl; auto.
  inversion Hdigits; subst.
  apply IH; assumption.
Qed.

Lemma digits_ok_repeat :
  forall n (v : nat),
    Nat.lt v EncodingMod.BASE ->
    digits_ok (repeat v n).
Proof.
  intros n v Hv.
  unfold digits_ok.
  induction n as [|n IH]; simpl; constructor; auto.
Qed.

Lemma nth_ge_default :
  forall {A} (xs : list A) (d : A) n,
    length xs <= n -> nth n xs d = d.
Proof.
  intros A xs d n Hlen.
  revert xs Hlen.
  induction n as [|n IH]; intros [|x xs] Hlen; simpl in *; auto; try lia.
  apply IH.
  simpl in Hlen. lia.
Qed.

Lemma digits_ok_app :
  forall xs ys,
    digits_ok xs ->
    digits_ok ys ->
    digits_ok (xs ++ ys).
Proof.
  intros xs ys Hxs Hys.
  unfold digits_ok in *.
  apply Forall_app; assumption.
Qed.

(* ----------------------------------------------------------------- *)
(* Blindness discipline                                               *)
(* ----------------------------------------------------------------- *)

(* A predicate describing that a program behaves like a "blind"       *)
(* Thiele Machine: it uses a single partition and never issues        *)
(* insight-generating instructions such as LASSERT.  The concrete     *)
(* checker lives in the executable semantics; here we keep only the   *)
(* logical summary that Coq relies on.                                *)
Parameter Blind : Prog -> Prop.

Parameter thiele_step : Prog -> State -> State.

Definition utm_cpu_state (tm : TM) (conf : TMConfig) : ThieleUniversal.CPU.State :=
  ThieleUniversal.setup_state tm conf.

Lemma utm_cpu_state_regs_length :
  forall tm conf,
    length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) = 10.
Proof.
  intros tm conf.
  unfold utm_cpu_state.
  apply ThieleUniversal.setup_state_regs_length.
Qed.

Lemma utm_cpu_state_reg_bound :
  forall tm conf,
    ThieleUniversal.CPU.REG_Q < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_Q' < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_HEAD < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_ADDR < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_TEMP1 < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_SYM < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)) /\
    ThieleUniversal.CPU.REG_PC < length (ThieleUniversal.CPU.regs (utm_cpu_state tm conf)).
Proof.
  intros tm conf.
  rewrite utm_cpu_state_regs_length.
  repeat split; vm_compute; lia.
Qed.

Lemma utm_cpu_state_inv_min :
  forall tm conf,
    ThieleUniversal.inv_min (utm_cpu_state tm conf) tm conf.
Proof.
  intros tm conf.
  unfold utm_cpu_state.
  apply ThieleUniversal.inv_min_setup_state.
Qed.

Lemma utm_cpu_state_read_q :
  forall tm q tape head,
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q
      (utm_cpu_state tm ((q, tape), head)) = q.
Proof.
  intros tm q tape head.
  specialize (utm_cpu_state_inv_min tm ((q, tape), head)) as Hmin.
  simpl in Hmin.
  destruct Hmin as [Hq _].
  exact Hq.
Qed.

Lemma utm_cpu_state_read_head :
  forall tm q tape head,
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD
      (utm_cpu_state tm ((q, tape), head)) = head.
Proof.
  intros tm q tape head.
  specialize (utm_cpu_state_inv_min tm ((q, tape), head)) as Hmin.
  simpl in Hmin.
  destruct Hmin as [_ [Hhead _]].
  exact Hhead.
Qed.

Definition rules_fit (tm : TM) : Prop :=
  (length (UTM_Encode.encode_rules tm.(tm_rules))
     <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)%nat.

Lemma utm_cpu_state_fetch :
  forall tm conf,
    ThieleUniversal.IS_FetchSymbol
      (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC (utm_cpu_state tm conf)).
Proof.
  intros tm conf.
  unfold ThieleUniversal.IS_FetchSymbol, utm_cpu_state.
  specialize (ThieleUniversal.inv_min_setup_state tm conf) as Hmin.
  destruct conf as ((q, tape), head).
  simpl in Hmin.
  destruct Hmin as (_ & _ & HPC).
  exact HPC.
Qed.

Lemma utm_cpu_state_read_tape :
  forall tm q tape head,
    rules_fit tm ->
    head < length tape ->
    ThieleUniversal.CPU.read_mem
      (UTM_Program.TAPE_START_ADDR + head)
      (utm_cpu_state tm ((q, tape), head))
    = nth head tape tm.(tm_blank).
Proof.
  intros tm q tape head Hfit Hlt.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit) as Hinv.
  destruct Hinv as [_ [_ [_ [Htape _]]]].
  unfold ThieleUniversal.CPU.read_mem, cpu0.
  rewrite ThieleUniversal.nth_add_skipn.
  rewrite <- Htape.
  rewrite (UTM_Program.nth_firstn_lt
             (A:=nat) head (length tape)
             (skipn UTM_Program.TAPE_START_ADDR
                    (ThieleUniversal.CPU.mem (utm_cpu_state tm ((q, tape), head)))) 0)
    by exact Hlt.
  rewrite (List.nth_indep tape head tm.(tm_blank) 0) by exact Hlt.
  reflexivity.
Qed.

Lemma utm_decode_fetch_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr (utm_cpu_state tm ((q, tape), head)) =
      ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
        UTM_Program.TAPE_START_ADDR.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog _]]]]].
  assert (Hmem_prog : forall n, n < length ThieleUniversal.program ->
      ThieleUniversal.CPU.read_mem n cpu0 = nth n ThieleUniversal.program 0).
  { intros n Hn.
    unfold ThieleUniversal.CPU.read_mem.
    rewrite <- Hprog.
    rewrite ThieleUniversal.nth_firstn_lt by exact Hn.
    reflexivity.
  }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc0.
  cbn [ThieleUniversal.CPU.read_reg].
  unfold ThieleUniversal.decode_instr_from_mem.
  cbn [Nat.mul Nat.add].
  change cpu0.(ThieleUniversal.CPU.mem)
    with (ThieleUniversal.CPU.mem cpu0).
  pose proof utm_program_length as Hprog_len.
  assert (Hlen0 : 0 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 0 Hlen0).
  cbn.
  rewrite ThieleUniversal.program_word_0.
  cbn.
  assert (Hlen1 : 1 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 1 Hlen1).
  cbn.
  rewrite ThieleUniversal.program_word_1.
  cbn.
  assert (Hlen2 : 2 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 2 Hlen2).
  cbn.
  rewrite ThieleUniversal.program_word_2.
  reflexivity.
Qed.

Lemma utm_decode_findrule_address_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run1 (utm_cpu_state tm ((q, tape), head))) =
      ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
        ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit)
    as Hdecode0.
  assert (Hpc1 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu0
         (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
            UTM_Program.TAPE_START_ADDR)
         Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged.
    { unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia. }
    specialize (Hsucc Hunchanged).
    rewrite Hpc0 in Hsucc. exact Hsucc. }
  assert (Hmem_prog : forall n,
             n < length ThieleUniversal.program ->
             ThieleUniversal.CPU.read_mem n cpu0 =
             nth n ThieleUniversal.program 0).
  { intros n Hn.
    unfold ThieleUniversal.CPU.read_mem.
    rewrite <- Hprog.
    rewrite ThieleUniversal.nth_firstn_lt by exact Hn.
    reflexivity. }
  assert (Hmem1 :
            ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0; simpl; exact I. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc1.
  cbn [ThieleUniversal.CPU.read_reg].
  unfold ThieleUniversal.decode_instr_from_mem.
  cbn [Nat.mul Nat.add].
  rewrite Hmem1.
    pose proof utm_program_length as Hprog_len.
    assert (Hlen4 : 4 < length ThieleUniversal.program) by
      (rewrite Hprog_len; lia).
    rewrite (Hmem_prog 4 Hlen4).
    cbn.
    rewrite ThieleUniversal.program_word_4.
    cbn.
    assert (Hlen5 : 5 < length ThieleUniversal.program) by
      (rewrite Hprog_len; lia).
    rewrite (Hmem_prog 5 Hlen5).
    cbn.
    rewrite ThieleUniversal.program_word_5.
    cbn.
    assert (Hlen6 : 6 < length ThieleUniversal.program) by
      (rewrite Hprog_len; lia).
    rewrite (Hmem_prog 6 Hlen6).
    cbn.
    rewrite ThieleUniversal.program_word_6.
    cbn.
    assert (Hlen7 : 7 < length ThieleUniversal.program) by
      (rewrite Hprog_len; lia).
    rewrite (Hmem_prog 7 Hlen7).
  cbn.
  rewrite ThieleUniversal.program_word_7.
  reflexivity.
Qed.

Lemma utm_decode_findrule_symbol_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run1
         (ThieleUniversal.run1 (utm_cpu_state tm ((q, tape), head)))) =
      ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
        ThieleUniversal.CPU.REG_ADDR.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit)
    as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  assert (Hpc1 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged.
    { unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia. }
    specialize (Hsucc Hunchanged).
    rewrite Hpc0 in Hsucc. exact Hsucc. }
  assert (Hpc2 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      as Hunchanged.
    { unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia. }
    specialize (Hsucc Hunchanged).
    rewrite Hpc1 in Hsucc. exact Hsucc. }
  assert (Hmem_prog : forall n,
             n < length ThieleUniversal.program ->
             ThieleUniversal.read_mem n cpu0 =
             nth n ThieleUniversal.program 0).
  { intros n Hn.
    unfold ThieleUniversal.read_mem.
    rewrite <- Hprog.
    rewrite ThieleUniversal.nth_firstn_lt by exact Hn.
    reflexivity. }
  assert (Hmem1 :
            ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0; simpl; exact I. }
  assert (Hmem2 :
            ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1; simpl; exact I. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc2.
  cbn [ThieleUniversal.CPU.read_reg].
  unfold ThieleUniversal.decode_instr_from_mem.
  cbn [Nat.mul Nat.add].
  rewrite Hmem2.
  rewrite Hmem1.
  pose proof utm_program_length as Hprog_len.
  assert (Hlen8 : 8 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 8 Hlen8).
  cbn.
  rewrite ThieleUniversal.program_word_8.
  cbn.
  assert (Hlen9 : 9 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 9 Hlen9).
  cbn.
  rewrite ThieleUniversal.program_word_9.
  cbn.
  assert (Hlen10 : 10 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 10 Hlen10).
  cbn.
  rewrite ThieleUniversal.program_word_10.
  cbn.
  assert (Hlen11 : 11 < length ThieleUniversal.program) by
    (rewrite Hprog_len; lia).
  rewrite (Hmem_prog 11 Hlen11).
  cbn.
  rewrite ThieleUniversal.program_word_11.
  reflexivity.
Qed.

Lemma utm_encode_rules_length :
  forall rules,
    length (UTM_Encode.encode_rules rules) = 5 * length rules.
Proof.
  intros rules.
  unfold UTM_Encode.encode_rules.
  induction rules as [|rule rules IH]; simpl; auto.
  rewrite app_length, IH.
  simpl.
  lia.
Qed.

Lemma utm_program_length :
  length ThieleUniversal.program = 196.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma utm_program_fits :
  (length ThieleUniversal.program <= UTM_Program.RULES_START_ADDR)%nat.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma utm_rules_encoded_length :
  length (UTM_Encode.encode_rules utm_tm.(tm_rules)) = 40.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma utm_rules_fit_bounds :
  (length (UTM_Encode.encode_rules utm_tm.(tm_rules))
     <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)%nat.
Proof.
  rewrite utm_rules_encoded_length.
  vm_compute.
  lia.
Qed.

Lemma rules_fit_utm : rules_fit utm_tm.
Proof. exact utm_rules_fit_bounds. Qed.

Lemma utm_cpu_state_inv :
  forall tm conf,
    (length ThieleUniversal.program <= UTM_Program.RULES_START_ADDR)%nat ->
    (length (UTM_Encode.encode_rules tm.(tm_rules))
       <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)%nat ->
    ThieleUniversal.inv (utm_cpu_state tm conf) tm conf.
Proof.
  intros tm conf Hprog Hrules.
  unfold utm_cpu_state.
  apply ThieleUniversal.inv_init; assumption.
Qed.

Lemma utm_cpu_state_inv_full :
  forall tm conf,
    (length (UTM_Encode.encode_rules tm.(tm_rules))
       <= UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)%nat ->
    ThieleUniversal.inv (utm_cpu_state tm conf) tm conf.
Proof.
  intros tm conf Hrules.
  apply utm_cpu_state_inv; [exact utm_program_fits|exact Hrules].
Qed.

Lemma utm_cpu_state_inv_from_rules_fit :
  forall tm conf,
    rules_fit tm ->
    ThieleUniversal.inv (utm_cpu_state tm conf) tm conf.
Proof.
  intros tm conf Hfit.
  apply utm_cpu_state_inv_full.
  exact Hfit.
Qed.

Lemma utm_fetch_pc_after_three_steps :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) = 3.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  pose proof (utm_cpu_state_fetch tm ((q, tape), head)) as Hfetch.
  destruct (ThieleUniversal.transition_Fetch_to_FindRule tm ((q, tape), head)
              cpu0 Hinv Hfetch) as [cpu_find [Hrun Hpc]].
  simpl in Hrun.
  unfold ThieleUniversal.IS_FindRule_Start in Hpc.
  rewrite <- Hrun.
  exact Hpc.
Qed.

Lemma utm_fetch_preserves_q :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) = q.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [Hq_init [Hhead_init [Hpc_init [Htape [Hprog_mem Hrules_mem]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [_ [_ [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  assert (Hq_lt : ThieleUniversal.CPU.REG_Q < 10) by
    (rewrite <- Hregs_len; exact Hq_bound).
  assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10) by
    (rewrite <- Hregs_len; exact Haddr_bound).
  assert (Htemp_lt : ThieleUniversal.CPU.REG_TEMP1 < 10) by
    (rewrite <- Hregs_len; exact Htemp_bound).
  assert (Hsym_lt : ThieleUniversal.CPU.REG_SYM < 10) by
    (rewrite <- Hregs_len; exact Hsym_bound).
  assert (Hpc_lt : ThieleUniversal.CPU.REG_PC < 10) by
    (rewrite <- Hregs_len; exact Hpc_bound).
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hlen_cpu1 : length (ThieleUniversal.CPU.regs cpu1) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc_init. lia.
    - exact Hprog_mem.
    - exact Hregs_len.
  }
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu0 (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                           UTM_Program.TAPE_START_ADDR) Hdecode0)
      as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc_init in Hsucc.
    exact Hsucc.
  }
  assert (Hmem_cpu1 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I.
  }
  assert (Hlen_cpu2 : length (ThieleUniversal.CPU.regs cpu2) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc1. lia.
    - rewrite Hmem_cpu1. exact Hprog_mem.
    - exact Hlen_cpu1.
  }
  assert (HQ1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu1 =
                ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu0).
  { apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu0 ThieleUniversal.CPU.REG_TEMP1
             UTM_Program.TAPE_START_ADDR
             ThieleUniversal.CPU.REG_Q);
      try assumption; try lia.
    - exact Hdecode0.
    - exact Hpc_lt.
    - exact Htemp_lt.
    - exact Hq_lt.
    - discriminate.
    - discriminate.
  }
  assert (HQ2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu2 =
                ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu1).
  { apply (ThieleUniversal.run1_preserves_reg_addreg
             cpu1 ThieleUniversal.CPU.REG_ADDR
             ThieleUniversal.CPU.REG_TEMP1
             ThieleUniversal.CPU.REG_HEAD
             ThieleUniversal.CPU.REG_Q);
      try assumption; try lia.
    - exact Hdecode1.
    - rewrite Hlen_cpu1. lia.
    - rewrite Hlen_cpu1. exact Haddr_lt.
    - rewrite Hlen_cpu1. exact Hq_lt.
    - discriminate.
    - discriminate.
  }
  assert (HQ3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu3 =
                ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu2).
  { apply (ThieleUniversal.run1_preserves_reg_loadindirect
             cpu2 ThieleUniversal.CPU.REG_SYM
             ThieleUniversal.CPU.REG_ADDR
             ThieleUniversal.CPU.REG_Q);
      try assumption; try lia.
    - exact Hdecode2.
    - rewrite Hlen_cpu2. lia.
    - rewrite Hlen_cpu2. exact Hsym_lt.
    - rewrite Hlen_cpu2. exact Hq_lt.
    - discriminate.
    - discriminate.
  }
  unfold ThieleUniversal.run_n.
  simpl.
  rewrite HQ3, HQ2, HQ1.
  exact Hq_init.
Qed.

Lemma utm_fetch_preserves_head :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) = head.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [Hq_init [Hhead_init [Hpc_init [Htape [Hprog_mem Hrules_mem]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [_ [_ [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  assert (Hhead_lt : ThieleUniversal.CPU.REG_HEAD < 10) by
    (rewrite <- Hregs_len; exact Hhead_bound).
  assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10) by
    (rewrite <- Hregs_len; exact Haddr_bound).
  assert (Htemp_lt : ThieleUniversal.CPU.REG_TEMP1 < 10) by
    (rewrite <- Hregs_len; exact Htemp_bound).
  assert (Hsym_lt : ThieleUniversal.CPU.REG_SYM < 10) by
    (rewrite <- Hregs_len; exact Hsym_bound).
  assert (Hpc_lt : ThieleUniversal.CPU.REG_PC < 10) by
    (rewrite <- Hregs_len; exact Hpc_bound).
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hlen_cpu1 : length (ThieleUniversal.CPU.regs cpu1) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc_init. lia.
    - exact Hprog_mem.
    - exact Hregs_len.
  }
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu0 (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                           UTM_Program.TAPE_START_ADDR) Hdecode0)
      as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc_init in Hsucc.
    exact Hsucc.
  }
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { subst cpu1.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hlen_cpu2 : length (ThieleUniversal.CPU.regs cpu2) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc1. lia.
    - rewrite Hmem01. exact Hprog_mem.
    - exact Hlen_cpu1.
  }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { subst cpu2.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { subst cpu3.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hhead1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD cpu1 = head).
  { apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu0 ThieleUniversal.CPU.REG_TEMP1
             UTM_Program.TAPE_START_ADDR
             ThieleUniversal.CPU.REG_HEAD
             Hdecode0 Hpc_lt Htemp_lt Hhead_lt);
      try discriminate. }
  assert (Hhead2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD cpu2 = head).
  { apply (ThieleUniversal.run1_preserves_reg_addreg
             cpu1 ThieleUniversal.CPU.REG_ADDR
             ThieleUniversal.CPU.REG_TEMP1
             ThieleUniversal.CPU.REG_HEAD
             ThieleUniversal.CPU.REG_HEAD);
      try assumption; try lia;
      try discriminate.
    - exact Hdecode1.
    - rewrite Hlen_cpu1. lia.
    - rewrite Hlen_cpu1. exact Haddr_lt.
    - rewrite Hlen_cpu1. exact Hhead_lt.
  }
  assert (Hhead3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD cpu3 = head).
  { apply (ThieleUniversal.run1_preserves_reg_loadindirect
             cpu2 ThieleUniversal.CPU.REG_SYM
             ThieleUniversal.CPU.REG_ADDR
             ThieleUniversal.CPU.REG_HEAD);
      try assumption; try lia;
      try discriminate.
    - exact Hdecode2.
    - rewrite Hlen_cpu2. lia.
    - rewrite Hlen_cpu2. exact Hsym_lt.
    - rewrite Hlen_cpu2. exact Hhead_lt.
  }
  unfold ThieleUniversal.run_n.
  simpl.
  rewrite Hhead3, Hhead2, Hhead1.
  exact Hhead_init.
Qed.

Lemma utm_fetch_addr_after_three_steps :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3)
    = UTM_Program.TAPE_START_ADDR + head.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [Hq'_bound [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hpc0 : ThieleUniversal.CPU.REG_PC < 10) by
    (rewrite <- Hregs_len; exact Hpc_bound).
  assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10) by
    (rewrite <- Hregs_len; exact Haddr_bound).
  assert (Hhead_lt : ThieleUniversal.CPU.REG_HEAD < 10) by
    (rewrite <- Hregs_len; exact Hhead_bound).
  assert (Htemp_lt : ThieleUniversal.CPU.REG_TEMP1 < 10) by
    (rewrite <- Hregs_len; exact Htemp_bound).
  assert (Hdecode_pc0 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu0 = 0).
  { destruct Hinv as [_ [_ [Hpc _]]]. exact Hpc. }
  pose proof (ThieleUniversal.run1_loadconst_result
                cpu0 ThieleUniversal.CPU.REG_TEMP1
                UTM_Program.TAPE_START_ADDR
                Hdecode0 Hpc0 Htemp_lt) as Htemp1.
  pose proof (ThieleUniversal.run1_preserves_reg_loadconst
                cpu0 ThieleUniversal.CPU.REG_TEMP1
                UTM_Program.TAPE_START_ADDR
                ThieleUniversal.CPU.REG_HEAD Hdecode0 Hpc0 Htemp_lt Hhead_lt
                ltac:(discriminate) ltac:(discriminate)) as Hhead_pres.
  pose proof (ThieleUniversal.run1_preserves_reg_loadconst
                cpu0 ThieleUniversal.CPU.REG_TEMP1
                UTM_Program.TAPE_START_ADDR
                ThieleUniversal.CPU.REG_ADDR Hdecode0 Hpc0 Htemp_lt Haddr_lt
                ltac:(discriminate) ltac:(discriminate)) as Haddr_pres.
  pose proof (ThieleUniversal.run1_addreg_result
                cpu1 ThieleUniversal.CPU.REG_ADDR
                ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD
                Hdecode1
                (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0
                   (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                Haddr_lt) as Haddr_cpu2.
  pose proof (ThieleUniversal.run1_preserves_reg_loadindirect
                cpu2 ThieleUniversal.CPU.REG_SYM ThieleUniversal.CPU.REG_ADDR
                ThieleUniversal.CPU.REG_ADDR Hdecode2
                (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1
                   (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                Hsym_bound Haddr_lt Haddr_lt ltac:(discriminate) ltac:(discriminate))
    as Haddr_cpu3.
  simpl in Haddr_cpu3.
  rewrite Haddr_cpu3.
  rewrite Haddr_cpu2.
  rewrite Htemp1.
  rewrite Hhead_pres.
  rewrite Haddr_pres.
  pose proof (utm_cpu_state_read_head tm q tape head) as Hhead_init.
  rewrite Hhead_init.
  reflexivity.
Qed.

Lemma utm_fetch_loads_symbol :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    head < length tape ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3)
    = nth head tape tm.(tm_blank).
Proof.
  intros tm q tape head conf Hfit Hlt.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [Hq'_bound [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hpc0 : ThieleUniversal.CPU.REG_PC < 10) by
    (rewrite <- Hregs_len; exact Hpc_bound).
  assert (Htemp_lt : ThieleUniversal.CPU.REG_TEMP1 < 10) by
    (rewrite <- Hregs_len; exact Htemp_bound).
  assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10) by
    (rewrite <- Hregs_len; exact Haddr_bound).
  assert (Hsym_lt : ThieleUniversal.CPU.REG_SYM < 10) by
    (rewrite <- Hregs_len; exact Hsym_bound).
  assert (Hnostore0 :
            match ThieleUniversal.decode_instr cpu0 with
            | ThieleUniversal.StoreIndirect _ _ => False
            | _ => True
            end).
  { rewrite Hdecode0. simpl. exact I. }
  pose proof (ThieleUniversal.run1_mem_preserved_if_no_store cpu0 Hnostore0)
    as Hmem01.
  assert (Hnostore1 :
            match ThieleUniversal.decode_instr cpu1 with
            | ThieleUniversal.StoreIndirect _ _ => False
            | _ => True
            end).
  { rewrite Hdecode1. simpl. exact I. }
  pose proof (ThieleUniversal.run1_mem_preserved_if_no_store cpu1 Hnostore1)
    as Hmem12.
  pose proof (ThieleUniversal.run1_loadconst_result
                cpu0 ThieleUniversal.CPU.REG_TEMP1
                UTM_Program.TAPE_START_ADDR
                Hdecode0 Hpc0 Htemp_lt) as Htemp1.
  pose proof (ThieleUniversal.run1_preserves_reg_loadconst
                cpu0 ThieleUniversal.CPU.REG_TEMP1
                UTM_Program.TAPE_START_ADDR
                ThieleUniversal.CPU.REG_HEAD Hdecode0 Hpc0 Htemp_lt
                Hhead_lt
                ltac:(discriminate) ltac:(discriminate)) as Hhead_pres.
  pose proof (ThieleUniversal.run1_addreg_result
                cpu1 ThieleUniversal.CPU.REG_ADDR
                ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD
                Hdecode1
                (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0
                   (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                Haddr_lt) as Haddr_cpu2.
  pose proof (ThieleUniversal.run1_preserves_reg_loadindirect
                cpu2 ThieleUniversal.CPU.REG_SYM ThieleUniversal.CPU.REG_ADDR
                ThieleUniversal.CPU.REG_ADDR Hdecode2
                (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1
                   (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                Hsym_lt Haddr_lt Haddr_lt ltac:(discriminate) ltac:(discriminate))
    as Haddr_cpu3.
  pose proof (ThieleUniversal.run1_loadindirect_result
                cpu2 ThieleUniversal.CPU.REG_SYM ThieleUniversal.CPU.REG_ADDR
                Hdecode2
                (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1
                   (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                Hsym_lt) as Hsym_cpu3.
  simpl in Haddr_cpu3.
  rewrite Haddr_cpu3 in Hsym_cpu3.
  rewrite Haddr_cpu2 in Hsym_cpu3.
  rewrite Htemp1 in Hsym_cpu3.
  rewrite Hhead_pres in Hsym_cpu3.
  pose proof (utm_cpu_state_read_head tm q tape head) as Hhead_init.
  rewrite Hhead_init in Hsym_cpu3.
  assert (Haddr_val : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR cpu2
                      = UTM_Program.TAPE_START_ADDR + head).
  { pose proof (utm_fetch_addr_after_three_steps tm q tape head Hfit) as Haddr3.
    unfold ThieleUniversal.run_n in Haddr3.
    simpl in Haddr3.
    rewrite Haddr_cpu3 in Haddr3.
    exact Haddr3. }
  rewrite Haddr_val in Hsym_cpu3.
  assert (Hmem_cpu2 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu0).
  { rewrite Hmem12, Hmem01. reflexivity. }
  unfold ThieleUniversal.CPU.read_mem in Hsym_cpu3.
  rewrite Hmem_cpu2 in Hsym_cpu3.
  apply utm_cpu_state_read_tape in Hsym_cpu3; try assumption.
  exact Hsym_cpu3.
Qed.

Lemma utm_fetch_mem_unchanged :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.mem (ThieleUniversal.run_n (utm_cpu_state tm conf) 3)
    = ThieleUniversal.CPU.mem (utm_cpu_state tm conf).
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { subst cpu1.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { subst cpu2.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { subst cpu3.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  unfold ThieleUniversal.run_n.
  simpl.
  rewrite Hmem23, Hmem12, Hmem01.
  reflexivity.
Qed.

Lemma utm_fetch_preserves_program_image :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    firstn (length ThieleUniversal.program)
          (ThieleUniversal.CPU.mem (ThieleUniversal.run_n (utm_cpu_state tm conf) 3))
    = ThieleUniversal.program.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit) as Hinv.
  destruct Hinv as [_ [_ [_ [Htape [Hprog_mem _]]]]].
  pose proof (utm_fetch_mem_unchanged tm q tape head Hfit) as Hmem.
  rewrite Hmem.
  exact Hprog_mem.
Qed.

Lemma utm_run1_preserves_program_image_before_apply :
  forall st,
    firstn (length ThieleUniversal.program)
           (ThieleUniversal.CPU.mem st) = ThieleUniversal.program ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st < 29 ->
    firstn (length ThieleUniversal.program)
           (ThieleUniversal.CPU.mem (ThieleUniversal.run1 st))
    = ThieleUniversal.program.
Proof.
  intros st Hprog Hpc_lt.
  pose proof (ThieleUniversal.program_instrs_length_gt_29) as Hlen_prog.
  assert (Hpc_len : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st
                    < length ThieleUniversal.program_instrs) by lia.
  pose proof (ThieleUniversal.decode_instr_program_state st Hpc_len Hprog)
    as Hdecode.
  pose proof (ThieleUniversal.program_instrs_before_apply_not_store
                (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st)
                Hpc_lt) as Hnostore.
  unfold ThieleUniversal.run1.
  rewrite Hdecode.
  apply ThieleUniversal.run1_mem_preserved_if_no_store.
  rewrite Hdecode.
  simpl in Hnostore.
  exact Hnostore.
Qed.

Lemma utm_fetch_inv_core :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.inv_core
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) tm conf.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  repeat split.
  - apply utm_fetch_preserves_q; assumption.
  - apply utm_fetch_preserves_head; assumption.
  - apply utm_fetch_preserves_tape_window; assumption.
  - apply utm_fetch_preserves_program_image; assumption.
  - apply utm_fetch_preserves_rule_table; assumption.
Qed.

Lemma utm_fetch_preserves_rule_table :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
          (skipn UTM_Program.RULES_START_ADDR
                 (ThieleUniversal.CPU.mem (ThieleUniversal.run_n (utm_cpu_state tm conf) 3)))
    = UTM_Encode.encode_rules tm.(tm_rules).
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit) as Hinv.
  destruct Hinv as [_ [_ [_ [_ [Hprog_mem Hrules_mem]]]]].
  pose proof (utm_fetch_mem_unchanged tm q tape head Hfit) as Hmem.
  rewrite Hmem.
  exact Hrules_mem.
Qed.

Definition utm_pc_prefix_lt
  (st : ThieleUniversal.CPU.State) (k : nat) : Prop :=
  forall j,
    j < k ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n st j) < 29.

Lemma utm_pc_prefix_lt_of_le :
  forall st n,
    (forall j,
        j <= n ->
        ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
          (ThieleUniversal.run_n st j) < 29) ->
    utm_pc_prefix_lt st (S n).
Proof.
  intros st n Hle j Hj.
  apply Hle.
  lia.
Qed.

Lemma utm_pc_prefix_lt_monotone :
  forall st k1 k2,
    utm_pc_prefix_lt st k2 ->
    k1 <= k2 ->
    utm_pc_prefix_lt st k1.
Proof.
  intros st k1 k2 Hlt Hle j Hj.
  apply Hlt.
  lia.
Qed.

Lemma utm_pc_prefix_lt_succ :
  forall st k,
    utm_pc_prefix_lt st k ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n st k) < 29 ->
    utm_pc_prefix_lt st (S k).
Proof.
  intros st k Hprefix Hpc j Hj.
  apply Nat.lt_succ_r in Hj.
  destruct Hj as [Hj | Hj].
  - apply Hprefix; assumption.
  - subst j.
    exact Hpc.
Qed.

Lemma utm_pc_prefix_add :
  forall st k1 k2,
    utm_pc_prefix_lt st k1 ->
    utm_pc_prefix_lt (ThieleUniversal.run_n st k1) k2 ->
    utm_pc_prefix_lt st (k1 + k2).
Proof.
  intros st k1 k2 Hprefix1 Hprefix2 j Hj.
  destruct (lt_dec j k1) as [Hj_lt | Hj_ge].
  - apply Hprefix1; exact Hj_lt.
  - assert (Hj_ge_k1 : k1 <= j) by lia.
    set (j' := j - k1).
    assert (Hj_eq : j = k1 + j') by (subst j'; lia).
    assert (Hj'_lt : j' < k2) by (subst j'; lia).
    rewrite Hj_eq.
    rewrite ThieleUniversal.run_n_add.
    apply Hprefix2; exact Hj'_lt.
Qed.

Lemma utm_rule_table_preserved_until :
  forall tm conf k,
    rules_fit tm ->
    utm_pc_prefix_lt (utm_cpu_state tm conf) k ->
    firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
          (skipn UTM_Program.RULES_START_ADDR
                 (ThieleUniversal.CPU.mem (ThieleUniversal.run_n (utm_cpu_state tm conf) k)))
    = UTM_Encode.encode_rules tm.(tm_rules).
Proof.
  intros tm conf k Hfit Hprefix.
  pose (cpu0 := utm_cpu_state tm conf).
  pose proof (utm_cpu_state_inv_from_rules_fit tm conf Hfit) as Hinv.
  apply (ThieleUniversal.rule_table_preserved_until_apply tm conf cpu0 k);
    assumption.
Qed.

Lemma utm_fetch_preserves_tape_window :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.tape_window_ok
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) tape.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit) as Hinv.
  destruct Hinv as [_ [_ [_ [Htape _]]]].
  pose proof (utm_fetch_mem_unchanged tm q tape head Hfit) as Hmem.
  unfold ThieleUniversal.tape_window_ok in *.
  rewrite Hmem.
  exact Htape.
Qed.

Lemma utm_fetch_state_in_bounds :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    head < length tape ->
    let st := ThieleUniversal.run_n (utm_cpu_state tm conf) 3 in
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q st = q /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM st =
      nth head tape tm.(tm_blank) /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR st =
      UTM_Program.TAPE_START_ADDR + head /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st = 3.
Proof.
  intros tm q tape head conf Hfit Hlt st.
  subst conf st.
  repeat split.
  - apply utm_fetch_preserves_q; assumption.
  - apply utm_fetch_loads_symbol; assumption.
  - apply utm_fetch_addr_after_three_steps; assumption.
  - apply utm_fetch_pc_after_three_steps; assumption.
Qed.

Lemma utm_fetch_state_out_of_bounds :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    length tape <= head ->
    let st := ThieleUniversal.run_n (utm_cpu_state tm conf) 3 in
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q st = q /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM st = tm.(tm_blank) /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR st =
      UTM_Program.TAPE_START_ADDR + head /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st = 3.
Proof.
  intros tm q tape head conf Hfit Hle st.
  subst conf st.
  repeat split.
  - apply utm_fetch_preserves_q; assumption.
  - set (cpu0 := utm_cpu_state tm ((q, tape), head)).
    set (cpu1 := ThieleUniversal.run1 cpu0).
    set (cpu2 := ThieleUniversal.run1 cpu1).
    set (cpu3 := ThieleUniversal.run1 cpu2).
    pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
      [Hq_bound [Hq'_bound [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
    pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
    pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
    pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
      as Hdecode1.
    pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
      as Hdecode2.
    assert (Hpc0 : ThieleUniversal.CPU.REG_PC < 10) by
      (rewrite <- Hregs_len; exact Hpc_bound).
    assert (Htemp_lt : ThieleUniversal.CPU.REG_TEMP1 < 10) by
      (rewrite <- Hregs_len; exact Htemp_bound).
    assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10) by
      (rewrite <- Hregs_len; exact Haddr_bound).
    assert (Hsym_lt : ThieleUniversal.CPU.REG_SYM < 10) by
      (rewrite <- Hregs_len; exact Hsym_bound).
    assert (Hnostore0 :
              match ThieleUniversal.decode_instr cpu0 with
              | ThieleUniversal.StoreIndirect _ _ => False
              | _ => True
              end).
    { rewrite Hdecode0. simpl. exact I. }
    pose proof (ThieleUniversal.run1_mem_preserved_if_no_store cpu0 Hnostore0)
      as Hmem01.
    assert (Hnostore1 :
              match ThieleUniversal.decode_instr cpu1 with
              | ThieleUniversal.StoreIndirect _ _ => False
              | _ => True
              end).
    { rewrite Hdecode1. simpl. exact I. }
    pose proof (ThieleUniversal.run1_mem_preserved_if_no_store cpu1 Hnostore1)
      as Hmem12.
    pose proof (ThieleUniversal.run1_loadconst_result
                  cpu0 ThieleUniversal.CPU.REG_TEMP1
                  UTM_Program.TAPE_START_ADDR
                  Hdecode0 Hpc0 Htemp_lt) as Htemp1.
    pose proof (ThieleUniversal.run1_preserves_reg_loadconst
                  cpu0 ThieleUniversal.CPU.REG_TEMP1
                  UTM_Program.TAPE_START_ADDR
                  ThieleUniversal.CPU.REG_HEAD Hdecode0 Hpc0 Htemp_lt
                  (ltac:(rewrite <- Hregs_len; exact Hhead_bound))
                  ltac:(discriminate) ltac:(discriminate)) as Hhead_pres.
    pose proof (ThieleUniversal.run1_addreg_result
                  cpu1 ThieleUniversal.CPU.REG_ADDR
                  ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD
                  Hdecode1
                  (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0
                     (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                  Haddr_lt) as Haddr_cpu2.
    pose proof (ThieleUniversal.run1_preserves_reg_loadindirect
                  cpu2 ThieleUniversal.CPU.REG_SYM ThieleUniversal.CPU.REG_ADDR
                  ThieleUniversal.CPU.REG_ADDR Hdecode2
                  (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1
                     (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                  Hsym_lt Haddr_lt Haddr_lt ltac:(discriminate) ltac:(discriminate))
      as Haddr_cpu3.
    pose proof (ThieleUniversal.run1_loadindirect_result
                  cpu2 ThieleUniversal.CPU.REG_SYM ThieleUniversal.CPU.REG_ADDR
                  Hdecode2
                  (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1
                     (ltac:(unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia)))
                  Hsym_lt) as Hsym_cpu3.
    simpl in Haddr_cpu3.
    rewrite Haddr_cpu3 in Hsym_cpu3.
    rewrite Haddr_cpu2 in Hsym_cpu3.
    rewrite Htemp1 in Hsym_cpu3.
    rewrite Hhead_pres in Hsym_cpu3.
    pose proof (utm_cpu_state_read_head tm q tape head) as Hhead_init.
    rewrite Hhead_init in Hsym_cpu3.
    assert (Haddr_val : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR cpu2
                        = UTM_Program.TAPE_START_ADDR + head).
    { pose proof (utm_fetch_addr_after_three_steps tm q tape head Hfit) as Haddr3.
      unfold ThieleUniversal.run_n in Haddr3.
      simpl in Haddr3.
      rewrite Haddr_cpu3 in Haddr3.
      exact Haddr3. }
    rewrite Haddr_val in Hsym_cpu3.
    assert (Hmem_cpu2 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu0).
    { rewrite Hmem12, Hmem01. reflexivity. }
    unfold ThieleUniversal.CPU.read_mem in Hsym_cpu3.
    rewrite Hmem_cpu2 in Hsym_cpu3.
    subst cpu0.
    unfold utm_cpu_state in Hsym_cpu3.
    unfold ThieleUniversal.setup_state in Hsym_cpu3.
    cbn [ThieleUniversal.CPU.mem] in Hsym_cpu3.
    set (rules := UTM_Encode.encode_rules tm.(tm_rules)) in *.
    set (mem0 := ThieleUniversal.pad_to UTM_Program.RULES_START_ADDR ThieleUniversal.program) in *.
    set (mem1 := ThieleUniversal.pad_to UTM_Program.TAPE_START_ADDR (mem0 ++ rules)) in *.
    assert (Hmem0_len : length mem0 = UTM_Program.RULES_START_ADDR).
    { subst mem0.
      apply ThieleUniversal.length_pad_to_ge.
      exact utm_program_fits.
    }
    assert (Hmem1_len : length mem1 = UTM_Program.TAPE_START_ADDR).
    { subst mem1.
      apply ThieleUniversal.length_pad_to_ge.
      rewrite length_app, Hmem0_len.
      replace UTM_Program.TAPE_START_ADDR
        with (UTM_Program.RULES_START_ADDR + (UTM_Program.TAPE_START_ADDR - UTM_Program.RULES_START_ADDR)) by lia.
      apply Nat.add_le_mono_l.
      exact Hfit.
    }
    rewrite app_nth2 in Hsym_cpu3 by lia.
    replace (UTM_Program.TAPE_START_ADDR + head - length mem1)
      with head in Hsym_cpu3 by lia.
    rewrite nth_ge_default in Hsym_cpu3 by exact Hle.
    subst rules mem0 mem1.
    exact Hsym_cpu3.
  - apply utm_fetch_addr_after_three_steps; assumption.
  - apply utm_fetch_pc_after_three_steps; assumption.
Qed.

Lemma utm_run1_pc_lt_29_if_lt_29 :
  forall tm conf st,
    ThieleUniversal.inv_core st tm conf ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st < 29 ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run1 st) < 29.
Proof.
  intros tm conf st Hcore Hpc_lt.
  destruct conf as [[q tape] head].
  destruct Hcore as [Hq [Hhead [Htape [Hprog Hrules]]]].
  set (pc := ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st).
  pose proof (ThieleUniversal.decode_instr_before_apply_pc_unchanged
                st Hpc_lt Hprog) as Hunchanged.
  pose proof (ThieleUniversal.decode_instr_before_apply_jump_target_lt
                st Hpc_lt Hprog) as Hjump.
  pose proof (ThieleUniversal.decode_instr_before_apply_not_store
                st Hpc_lt Hprog) as Hnostore.
  remember (ThieleUniversal.decode_instr st) as instr eqn:Hinstr.
  destruct instr;
    try (rewrite Hinstr in Hunchanged;
         pose proof (ThieleUniversal.run1_pc_succ_instr st _ Hinstr Hunchanged)
           as Hsucc;
         rewrite Hsucc;
         lia).
  - rewrite Hinstr in Hnostore. simpl in Hnostore. contradiction.
  - rewrite Hinstr in Hjump.
    simpl in Hjump.
    unfold ThieleUniversal.run1.
    rewrite Hinstr.
    simpl.
    destruct (Nat.eqb (ThieleUniversal.CPU.read_reg n st) 0) eqn:Hz.
    + rewrite (ThieleUniversal.CPU.step_jz_true _ _ st Hz).
      lia.
    + rewrite (ThieleUniversal.CPU.step_jz_false _ _ st Hz).
      subst pc. lia.
  - rewrite Hinstr in Hjump.
    simpl in Hjump.
    unfold ThieleUniversal.run1.
    rewrite Hinstr.
    simpl.
    destruct (Nat.eqb (ThieleUniversal.CPU.read_reg n st) 0) eqn:Hz.
    + rewrite (ThieleUniversal.CPU.step_jnz_true _ _ st Hz).
      subst pc. lia.
    + rewrite (ThieleUniversal.CPU.step_jnz_false _ _ st Hz).
      lia.
  - unfold ThieleUniversal.run1.
    rewrite Hinstr.
    simpl.
    subst pc.
    lia.
Qed.

Lemma utm_fetch_pc_prefix_lt_29 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    forall j,
      j <= 3 ->
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
        (ThieleUniversal.run_n (utm_cpu_state tm conf) j) < 29.
Proof.
  intros tm q tape head conf Hfit j Hj.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc_init [_ [Hprog_mem _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit)
    as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hpc1 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu0
         (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
            UTM_Program.TAPE_START_ADDR)
         Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged.
    { unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia. }
    specialize (Hsucc Hunchanged).
    rewrite Hpc_init in Hsucc.
    exact Hsucc. }
  assert (Hpc2 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu1
         (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
            ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD)
         Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      as Hunchanged by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof
      (ThieleUniversal.run1_pc_succ_instr cpu2
         (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
            ThieleUniversal.CPU.REG_ADDR)
         Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR))
      as Hunchanged by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  subst cpu1 cpu2 cpu3.
  destruct j as [|j1].
  - simpl. rewrite Hpc_init. lia.
  - assert (Hj1 : j1 <= 2) by lia.
    simpl.
    destruct j1 as [|j2].
    + rewrite Hpc1. lia.
    + assert (Hj2 : j2 <= 1) by lia.
      simpl.
      destruct j2 as [|j3].
      * rewrite Hpc2. lia.
      * assert (Hj3 : j3 <= 0) by lia.
        simpl.
        destruct j3 as [|j4].
        -- rewrite Hpc3. lia.
        -- lia.
Qed.

Lemma utm_fetch_pc_prefix_le4_lt_29 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    forall j,
      j <= 4 ->
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
        (ThieleUniversal.run_n (utm_cpu_state tm conf) j) < 29.
Proof.
  intros tm q tape head conf Hfit j Hj.
  destruct (Nat.eq_dec j 4) as [Hj_eq | Hj_neq].
  - subst j.
    pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit)
      as [_ [_ [_ Hpc4]]].
    simpl in Hpc4.
    lia.
  - assert (j <= 3) by lia.
    apply utm_fetch_pc_prefix_lt_29; assumption.
Qed.

Lemma utm_fetch_pc_prefix_lt_4 :
  forall tm q tape head,
    rules_fit tm ->
    utm_pc_prefix_lt (utm_cpu_state tm ((q, tape), head)) 4.
Proof.
  intros tm q tape head Hfit j Hj.
  apply utm_fetch_pc_prefix_lt_29; try assumption.
  lia.
Qed.

Lemma utm_fetch_establishes_find_rule_start_inv_in_bounds :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    head < length tape ->
    ThieleUniversal.find_rule_start_inv tm conf
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3).
Proof.
  intros tm q tape head conf Hfit Hlt.
  subst conf.
  pose proof (utm_fetch_state_in_bounds tm q tape head Hfit Hlt)
    as [Hq_fetch [Hsym_fetch [Haddr_fetch Hpc_fetch]]].
  unfold ThieleUniversal.find_rule_start_inv.
  repeat split; assumption.
Qed.

Lemma utm_fetch_establishes_find_rule_start_inv_out_of_bounds :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    length tape <= head ->
    ThieleUniversal.find_rule_start_inv tm conf
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 3).
Proof.
  intros tm q tape head conf Hfit Hle.
  subst conf.
  pose proof (utm_fetch_state_out_of_bounds tm q tape head Hfit Hle)
    as [Hq_fetch [Hsym_fetch [Haddr_fetch Hpc_fetch]]].
  unfold ThieleUniversal.find_rule_start_inv.
  repeat split; assumption.
Qed.

Lemma utm_apply_phase_registers_from_axioms :
  forall tm q tape head
         (cpu0 cpu_apply : ThieleUniversal.CPU.State)
         (k_total : nat) q' write move,
    let conf := ((q, tape), head) in
    ThieleUniversal.inv cpu0 tm conf ->
    cpu_apply = ThieleUniversal.run_n cpu0 k_total ->
    (forall j,
        j < k_total ->
        ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
          (ThieleUniversal.run_n cpu0 j) < 29) ->
    ThieleUniversal.IS_ApplyRule_Start
      (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu_apply) ->
    firstn (length (UTM_Encode.encode_rules tm.(tm_rules)))
          (skipn UTM_Program.RULES_START_ADDR
                 (ThieleUniversal.CPU.mem cpu_apply))
      = UTM_Encode.encode_rules tm.(tm_rules) ->
    find_rule tm.(tm_rules) q (nth head tape tm.(tm_blank))
      = Some (q', write, move) ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q' cpu_apply = q' /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_WRITE cpu_apply = write /\
    UTM_Encode.decode_z
      (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_MOVE cpu_apply) = move.
Proof.
  intros tm q tape head cpu0 cpu_apply k_total q' write move conf
         Hinv Hrun_total Hpc_bound Hpc_apply Hrules_final Hfind.
  subst conf.
  pose proof (ThieleUniversal.pc_29_implies_registers_from_rule_table
                tm ((q, tape), head) cpu0 k_total cpu_apply
                Hinv Hrun_total Hpc_bound Hpc_apply)
    as [i [Hi [Hmem_q' [Hmem_write Hmem_move]]]].
  pose proof (ThieleUniversal.find_rule_from_memory_components
                tm ((q, tape), head) i cpu_apply
                Hi Hmem_q' Hmem_write Hmem_move Hrules_final)
    as Hrule_components.
  rewrite Hfind in Hrule_components.
  inversion Hrule_components as [Htuple].
  inversion Htuple as [Hq'_eq Hrest].
  inversion Hrest as [Hwrite_eq Hmove_eq].
  subst.
  repeat split; reflexivity.
Qed.

Lemma utm_fetch_establishes_find_rule_loop_inv :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    head < length tape ->
    ThieleUniversal.find_rule_loop_inv tm conf
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 4) 0.
Proof.
  intros tm q tape head conf Hfit Hhead_lt.
  subst conf.
  set (st3 := ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3).
  set (st4 := ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4).
  pose proof (utm_fetch_state_in_bounds tm q tape head Hfit Hhead_lt)
    as [Hq_fetch [Hsym_fetch [_ Hpc_fetch]]].
  pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit)
    as [Haddr_reset [Hq_reset [Hsym_reset Hpc_reset]]].
  subst st3 st4.
  unfold ThieleUniversal.find_rule_loop_inv.
  repeat split.
  - rewrite Hq_reset.
    rewrite Hq_fetch.
    reflexivity.
  - rewrite Hsym_reset.
    rewrite Hsym_fetch.
    reflexivity.
  - rewrite Haddr_reset.
    simpl.
    lia.
  - rewrite Hpc_reset.
    reflexivity.
Qed.

Lemma utm_fetch_reset_inv_core :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.inv_core
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 4) tm conf.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [Hq0 [Hhead0 [Hpc0 [Htape0 [Hprog0 Hrules0]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len0.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [_ [Hhead_bound [Haddr_bound [Htemp_bound [_ Hpc_bound]]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  assert (Hpc0_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu0 < 29)
    by (rewrite Hpc0; lia).
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { subst cpu1.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { subst cpu2.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { subst cpu3.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hlen_cpu1 : length (ThieleUniversal.CPU.regs cpu1) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply;
      try assumption.
    - exact Hpc0_lt.
    - exact Hprog0.
    - exact Hregs_len0.
  }
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc1_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 < 29)
    by (rewrite Hpc1; lia).
  assert (Hprog1 : firstn (length ThieleUniversal.program)
                         (ThieleUniversal.CPU.mem cpu1)
                   = ThieleUniversal.program).
  { rewrite Hmem01. exact Hprog0. }
  assert (Hlen_cpu2 : length (ThieleUniversal.CPU.regs cpu2) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply;
      try assumption.
    - exact Hpc1_lt.
    - exact Hprog1.
    - exact Hlen_cpu1.
  }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc2_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 < 29)
    by (rewrite Hpc2; lia).
  assert (Hprog2 : firstn (length ThieleUniversal.program)
                         (ThieleUniversal.CPU.mem cpu2)
                   = ThieleUniversal.program).
  { rewrite Hmem12, Hmem01. exact Hprog0. }
  assert (Hlen_cpu3 : length (ThieleUniversal.CPU.regs cpu3) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply;
      try assumption.
    - exact Hpc2_lt.
    - exact Hprog2.
    - exact Hlen_cpu2.
  }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { unfold ThieleUniversal.run_n in *.
    simpl in *.
    pose proof (utm_fetch_pc_after_three_steps tm q tape head Hfit) as Hpc_fetch.
    exact Hpc_fetch. }
  assert (Hmem34 : ThieleUniversal.CPU.mem cpu4 = ThieleUniversal.CPU.mem cpu3).
  { subst cpu4.
    apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode3. simpl. exact I. }
  assert (Hregs_len3 : length (ThieleUniversal.CPU.regs cpu3) = 10) by exact Hlen_cpu3.
  assert (Hq_lt : ThieleUniversal.CPU.REG_Q < 10)
    by (rewrite <- Hregs_len0; exact Hq_bound).
  assert (Hhead_lt : ThieleUniversal.CPU.REG_HEAD < 10)
    by (rewrite <- Hregs_len0; exact Hhead_bound).
  assert (Haddr_lt : ThieleUniversal.CPU.REG_ADDR < 10)
    by (rewrite <- Hregs_len0; exact Haddr_bound).
  assert (Hpc_lt : ThieleUniversal.CPU.REG_PC < 10)
    by (rewrite <- Hregs_len0; exact Hpc_bound).
  assert (Hq_pres : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu4 =
                    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu3).
  { subst cpu4.
    apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu3 ThieleUniversal.CPU.REG_ADDR UTM_Program.RULES_START_ADDR
             ThieleUniversal.CPU.REG_Q);
      try assumption; try lia.
    - exact Hdecode3.
    - rewrite Hregs_len3. exact Hpc_lt.
    - rewrite Hregs_len3. exact Haddr_lt.
    - rewrite Hregs_len3. exact Hq_lt.
    - discriminate.
    - discriminate.
  }
  assert (Hhead_pres : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD cpu4 =
                        ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_HEAD cpu3).
  { subst cpu4.
    apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu3 ThieleUniversal.CPU.REG_ADDR UTM_Program.RULES_START_ADDR
             ThieleUniversal.CPU.REG_HEAD);
      try assumption; try lia.
    - exact Hdecode3.
    - rewrite Hregs_len3. exact Hpc_lt.
    - rewrite Hregs_len3. exact Haddr_lt.
    - rewrite Hregs_len3. exact Hhead_lt.
    - discriminate.
    - discriminate.
  }
  unfold ThieleUniversal.inv_core.
  subst cpu4.
  repeat split.
  - rewrite Hq_pres.
    change cpu3 with (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3).
    rewrite (utm_fetch_preserves_q tm q tape head Hfit).
    exact Hq0.
  - rewrite Hhead_pres.
    change cpu3 with (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3).
    rewrite (utm_fetch_preserves_head tm q tape head Hfit).
    exact Hhead0.
  - rewrite Hmem34, Hmem23, Hmem12, Hmem01.
    exact Htape0.
  - rewrite Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hprog0.
  - rewrite Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hrules0.
Qed.

Lemma utm_run_n_last_step :
  forall st n,
    ThieleUniversal.run_n st (S n) =
    ThieleUniversal.run_n (ThieleUniversal.run_n st n) 1.
Proof.
  intros st n.
  rewrite <- Nat.add_1_r.
  apply ThieleUniversal.run_n_add.
Qed.

Lemma utm_find_rule_loop_some_reaches_apply :
  forall tm conf st i q' write move,
    ThieleUniversal.inv st tm conf ->
    ThieleUniversal.find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    ThieleUniversal.rule_table_q_monotone tm ->
    ThieleUniversal.rule_table_symbol_monotone tm ->
    length (ThieleUniversal.CPU.regs st) = 10 ->
    find_rule (skipn i (tm_rules tm))
      (let '((q, _), _) := conf in q)
      (let '((_, tape), head) := conf in nth head tape tm.(tm_blank))
    = Some (q', write, move) ->
    exists st',
      st' = ThieleUniversal.run_n st 17 /\
      ThieleUniversal.IS_ApplyRule_Start
        (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st').
Proof.
  intros tm conf st i q' write move Hinv Hloop Hi Hmono_q Hmono_sym Hlen Hfind.
  pose proof
    (ThieleUniversal.find_rule_loop_preserves_inv tm conf st i
       Hinv Hloop Hi Hmono_q Hmono_sym Hlen) as Hcases.
  rewrite Hfind in Hcases.
  destruct Hcases as [st' [Hrun Happly]].
  exists st'.
  split; assumption.
Qed.

Lemma utm_find_rule_loop_none_progress :
  forall tm conf st i,
    ThieleUniversal.inv st tm conf ->
    ThieleUniversal.find_rule_loop_inv tm conf st i ->
    i < length (tm_rules tm) ->
    ThieleUniversal.rule_table_q_monotone tm ->
    ThieleUniversal.rule_table_symbol_monotone tm ->
    length (ThieleUniversal.CPU.regs st) = 10 ->
    find_rule (skipn i (tm_rules tm))
      (let '((q, _), _) := conf in q)
      (let '((_, tape), head) := conf in nth head tape tm.(tm_blank)) = None ->
    exists k st',
      st' = ThieleUniversal.run_n st k /\
      ThieleUniversal.find_rule_loop_inv tm conf st' (S i) /\
      (k = 6 \/ k = 13).
Proof.
  intros tm conf st i Hinv Hloop Hi Hmono_q Hmono_sym Hlen Hfind.
  pose proof
    (ThieleUniversal.find_rule_loop_preserves_inv tm conf st i
       Hinv Hloop Hi Hmono_q Hmono_sym Hlen) as Hcases.
  rewrite Hfind in Hcases.
  exact Hcases.
Qed.

Lemma utm_find_rule_start_pc_prefix_step0 :
  forall tm conf st,
    ThieleUniversal.inv_core st tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf st ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st < 29 /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n st 1) < 29.
Proof.
  intros tm conf st Hcore Hstart.
  destruct conf as [[q tape] head].
  simpl in Hcore.
  unfold ThieleUniversal.find_rule_start_inv in Hstart.
  destruct Hstart as [_ [_ [_ Hpc]]].
  split.
  - rewrite Hpc. lia.
  - change (ThieleUniversal.run_n st 1) with (ThieleUniversal.run1 st).
    apply (utm_run1_pc_lt_29_if_lt_29 tm ((q, tape), head) st);
      try assumption.
    rewrite Hpc. lia.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step1 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n
         (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) 2) < 29.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu4 := ThieleUniversal.run_n cpu0 4).
  pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit)
    as [_ [_ [_ Hpc4]]].
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode4.
  pose proof (ThieleUniversal.run1_pc_succ_instr
                cpu4
                (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
                   ThieleUniversal.CPU.REG_ADDR)
                Hdecode4) as Hsucc.
  assert (ThieleUniversal.CPU.pc_unchanged
            (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
               ThieleUniversal.CPU.REG_ADDR)) as Hunchanged
    by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
  specialize (Hsucc Hunchanged).
  rewrite Hpc4 in Hsucc.
  rewrite <- (ThieleUniversal.run_n_add cpu0 3 2).
  replace (3 + 2)%nat with 5%nat by lia.
  replace 5%nat with (4 + 1)%nat by lia.
  rewrite (ThieleUniversal.run_n_add cpu0 4 1).
  simpl.
  change (ThieleUniversal.run_n (ThieleUniversal.run_n cpu0 4) 1)
    with (ThieleUniversal.run1 cpu4).
  rewrite Hsucc.
  lia.
Qed.

Lemma utm_find_rule_loop_pc_prefix_base :
  forall tm q tape head,
    rules_fit tm ->
    head < length tape ->
    forall j,
      j <= 2 ->
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
        (ThieleUniversal.run_n
           (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) j) < 29.
Proof.
  intros tm q tape head Hfit Hhead_lt j Hj.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu_find := ThieleUniversal.run_n cpu0 3).
  pose proof (utm_fetch_inv_core tm q tape head Hfit) as Hinv_core.
  pose proof (utm_fetch_establishes_find_rule_start_inv_in_bounds
                 tm q tape head Hfit Hhead_lt) as Hstart_inv.
  pose proof (utm_find_rule_start_pc_prefix_step0 tm ((q, tape), head) cpu_find
                 Hinv_core Hstart_inv) as [Hpc_find_lt Hpc_loop_step0].
  destruct j as [|j1].
  - simpl. subst cpu_find cpu0. exact Hpc_find_lt.
  - simpl.
    destruct j1 as [|j2].
    + subst cpu_find cpu0. exact Hpc_loop_step0.
    + assert (Hj2_zero : j2 = 0) by lia.
      subst j2.
      simpl.
      replace (S (S 0)) with 2%nat by lia.
      subst cpu_find cpu0.
      apply (utm_find_rule_loop_pc_prefix_step1 tm q tape head Hfit).
Qed.

Lemma utm_pc_prefix_total_from_loop :
  forall cpu0 cpu_find k_apply,
    cpu_find = ThieleUniversal.run_n cpu0 3 ->
    utm_pc_prefix_lt cpu0 5 ->
    utm_pc_prefix_lt cpu_find k_apply ->
    utm_pc_prefix_lt cpu0 (3 + k_apply).
Proof.
  intros cpu0 cpu_find k_apply Hrun_fetch Hfetch_prefix Hloop_prefix j Hj.
  unfold utm_pc_prefix_lt in *.
  destruct (lt_dec j 5) as [Hj_lt5 | Hj_ge5].
  - apply Hfetch_prefix.
    assumption.
  - assert (Hj_ge3 : 3 <= j) by lia.
    set (j' := j - 3).
    assert (Hdecomp : j = 3 + j') by (subst j'; lia).
    assert (Hj'_lt : j' < k_apply) by (subst j'; lia).
    rewrite Hdecomp.
    rewrite (ThieleUniversal.run_n_add cpu0 3 j').
    rewrite Hrun_fetch.
    apply Hloop_prefix.
    exact Hj'_lt.
Qed.

Lemma utm_decode_findrule_reset_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) =
    ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
      UTM_Program.RULES_START_ADDR.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog_mem Hrules_mem]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  assert (Hmem1 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem2 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem3 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hprog_cpu3 :
            firstn (length ThieleUniversal.program) (ThieleUniversal.CPU.mem cpu3)
            = ThieleUniversal.program).
  { rewrite Hmem3, Hmem2, Hmem1.
    exact Hprog_mem. }
  assert (Hpc_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3
                   < length ThieleUniversal.program_instrs) by (rewrite Hpc3; pose proof ThieleUniversal.program_instrs_length_gt_29; lia).
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc3.
  cbn [ThieleUniversal.CPU.read_reg].
  pose proof (ThieleUniversal.decode_instr_program_state
                cpu3 Hpc_lt Hprog_cpu3) as Hdecode_prog.
  rewrite Hdecode_prog.
  rewrite ThieleUniversal.decode_instr_program_at_pc by exact Hpc_lt.
  change (nth 3 ThieleUniversal.program_instrs ThieleUniversal.Halt)
    with (nth 3 UTM_Program.program_instrs ThieleUniversal.Halt).
    cbn [UTM_Program.program_instrs].
    reflexivity.
  Qed.

Lemma utm_decode_findrule_load_rule_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4) =
    ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
      ThieleUniversal.CPU.REG_ADDR.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog_mem _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  assert (Hpc4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4 = 4).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu3 _ Hdecode3) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
                 UTM_Program.RULES_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc3 in Hsucc.
    exact Hsucc. }
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hmem34 : ThieleUniversal.CPU.mem cpu4 = ThieleUniversal.CPU.mem cpu3).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode3. simpl. exact I. }
  assert (Hprog_cpu4 :
            firstn (length ThieleUniversal.program) (ThieleUniversal.CPU.mem cpu4)
            = ThieleUniversal.program).
  { rewrite Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hprog_mem. }
  assert (Hpc_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4
                   < length ThieleUniversal.program_instrs).
  { rewrite Hpc4. apply ThieleUniversal.program_instrs_length_gt_29. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc4.
  cbn [ThieleUniversal.CPU.read_reg].
  pose proof (ThieleUniversal.decode_instr_program_state
                cpu4 Hpc_lt Hprog_cpu4) as Hdecode_prog.
  rewrite Hdecode_prog.
  rewrite ThieleUniversal.decode_instr_program_at_pc by exact Hpc_lt.
  change (nth 4 ThieleUniversal.program_instrs ThieleUniversal.Halt)
    with (nth 4 UTM_Program.program_instrs ThieleUniversal.Halt).
  cbn [UTM_Program.program_instrs].
  reflexivity.
Qed.

Lemma utm_decode_findrule_copy_q_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 5) =
    ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
      ThieleUniversal.CPU.REG_Q.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  set (cpu5 := ThieleUniversal.run1 cpu4).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog_mem _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode4.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  assert (Hpc4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4 = 4).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu3 _ Hdecode3) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
                 UTM_Program.RULES_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc3 in Hsucc.
    exact Hsucc. }
  assert (Hpc5 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu5 = 5).
  { pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu4 _ Hdecode4) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
                 ThieleUniversal.CPU.REG_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc4 in Hsucc.
    exact Hsucc. }
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hmem34 : ThieleUniversal.CPU.mem cpu4 = ThieleUniversal.CPU.mem cpu3).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode3. simpl. exact I. }
  assert (Hmem45 : ThieleUniversal.CPU.mem cpu5 = ThieleUniversal.CPU.mem cpu4).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode4. simpl. exact I. }
  assert (Hprog_cpu5 :
            firstn (length ThieleUniversal.program) (ThieleUniversal.CPU.mem cpu5)
            = ThieleUniversal.program).
  { rewrite Hmem45, Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hprog_mem. }
  assert (Hpc_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu5
                   < length ThieleUniversal.program_instrs).
  { rewrite Hpc5. apply ThieleUniversal.program_instrs_length_gt_29. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc5.
  cbn [ThieleUniversal.CPU.read_reg].
  pose proof (ThieleUniversal.decode_instr_program_state
                cpu5 Hpc_lt Hprog_cpu5) as Hdecode_prog.
  rewrite Hdecode_prog.
  rewrite ThieleUniversal.decode_instr_program_at_pc by exact Hpc_lt.
  change (nth 5 ThieleUniversal.program_instrs ThieleUniversal.Halt)
    with (nth 5 UTM_Program.program_instrs ThieleUniversal.Halt).
  cbn [UTM_Program.program_instrs].
  reflexivity.
Qed.

Lemma utm_decode_findrule_subtract_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 6) =
    ThieleUniversal.CPU.SubReg ThieleUniversal.CPU.REG_TEMP1
      ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_Q'.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  set (cpu5 := ThieleUniversal.run1 cpu4).
  set (cpu6 := ThieleUniversal.run1 cpu5).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [_ [_ [Hpc0 [_ [Hprog_mem _]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode4.
  pose proof (utm_decode_findrule_copy_q_instruction tm q tape head Hfit)
    as Hdecode5.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc0 in Hsucc. exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc1 in Hsucc. exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc2 in Hsucc. exact Hsucc. }
  assert (Hpc4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4 = 4).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu3 _ Hdecode3) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
                 UTM_Program.RULES_START_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc3 in Hsucc. exact Hsucc. }
  assert (Hpc5 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu5 = 5).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu4 _ Hdecode4) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
                 ThieleUniversal.CPU.REG_ADDR)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc4 in Hsucc. exact Hsucc. }
  assert (Hpc6 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu6 = 6).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu5 _ Hdecode5) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
                 ThieleUniversal.CPU.REG_Q)) as Hunchanged by
        (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc5 in Hsucc. exact Hsucc. }
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hmem34 : ThieleUniversal.CPU.mem cpu4 = ThieleUniversal.CPU.mem cpu3).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode3. simpl. exact I. }
  assert (Hmem45 : ThieleUniversal.CPU.mem cpu5 = ThieleUniversal.CPU.mem cpu4).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode4. simpl. exact I. }
  assert (Hmem56 : ThieleUniversal.CPU.mem cpu6 = ThieleUniversal.CPU.mem cpu5).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode5. simpl. exact I. }
  assert (Hprog_cpu6 :
            firstn (length ThieleUniversal.program) (ThieleUniversal.CPU.mem cpu6)
            = ThieleUniversal.program).
  { rewrite Hmem56, Hmem45, Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hprog_mem. }
  assert (Hpc_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu6
                   < length ThieleUniversal.program_instrs).
  { rewrite Hpc6. apply ThieleUniversal.program_instrs_length_gt_29. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc6.
  cbn [ThieleUniversal.CPU.read_reg].
  pose proof (ThieleUniversal.decode_instr_program_state
                cpu6 Hpc_lt Hprog_cpu6) as Hdecode_prog.
  rewrite Hdecode_prog.
  rewrite ThieleUniversal.decode_instr_program_at_pc by exact Hpc_lt.
  change (nth 6 ThieleUniversal.program_instrs ThieleUniversal.Halt)
    with (nth 6 UTM_Program.program_instrs ThieleUniversal.Halt).
  cbn [UTM_Program.program_instrs].
  reflexivity.
Qed.

Lemma utm_decode_findrule_jump_zero_instruction :
  forall tm q tape head,
    rules_fit tm ->
    ThieleUniversal.decode_instr
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 7) =
    ThieleUniversal.CPU.Jz ThieleUniversal.CPU.REG_TEMP1 12.
Proof.
  intros tm q tape head Hfit.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  set (cpu5 := ThieleUniversal.run1 cpu4).
  set (cpu6 := ThieleUniversal.run1 cpu5).
  set (cpu7 := ThieleUniversal.run1 cpu6).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [Hq0 [Hhead0 [Hpc0 [Htape0 [Hprog0 Hrules0]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode4.
  pose proof (utm_decode_findrule_subtract_instruction tm q tape head Hfit)
    as Hdecode6.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  assert (Hpc4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4 = 4).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu3 _ Hdecode3) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
                 UTM_Program.RULES_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc3 in Hsucc.
    exact Hsucc. }
  assert (Hpc5 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu5 = 5).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu4 _ Hdecode4) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
                 ThieleUniversal.CPU.REG_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc4 in Hsucc.
    exact Hsucc. }
  assert (Hpc6 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu6 = 6).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu5 _ Hdecode5) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
                 ThieleUniversal.CPU.REG_Q)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc5 in Hsucc.
    exact Hsucc. }
  assert (Hpc7 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu7 = 7).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu6 _ Hdecode6) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.SubReg ThieleUniversal.CPU.REG_TEMP1
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_Q'))
      by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc6 in Hsucc.
    exact Hsucc. }
  assert (Hmem01 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem12 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem23 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hmem34 : ThieleUniversal.CPU.mem cpu4 = ThieleUniversal.CPU.mem cpu3).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode3. simpl. exact I. }
  assert (Hmem45 : ThieleUniversal.CPU.mem cpu5 = ThieleUniversal.CPU.mem cpu4).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode4. simpl. exact I. }
  assert (Hmem56 : ThieleUniversal.CPU.mem cpu6 = ThieleUniversal.CPU.mem cpu5).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode5. simpl. exact I. }
  assert (Hmem67 : ThieleUniversal.CPU.mem cpu7 = ThieleUniversal.CPU.mem cpu6).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode6. simpl. exact I. }
  assert (Hprog_cpu7 :
            firstn (length ThieleUniversal.program)
                   (ThieleUniversal.CPU.mem cpu7)
            = ThieleUniversal.program).
  { rewrite Hmem67, Hmem56, Hmem45, Hmem34, Hmem23, Hmem12, Hmem01.
    exact Hprog0. }
  assert (Hpc_lt : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu7
                   < length ThieleUniversal.program_instrs).
  { rewrite Hpc7. apply ThieleUniversal.program_instrs_length_gt_29. }
  unfold ThieleUniversal.decode_instr.
  rewrite Hpc7.
  cbn [ThieleUniversal.CPU.read_reg].
  pose proof (ThieleUniversal.decode_instr_program_state
                cpu7 Hpc_lt Hprog_cpu7) as Hdecode_prog.
  rewrite Hdecode_prog.
  rewrite ThieleUniversal.decode_instr_program_at_pc by exact Hpc_lt.
  change (nth 7 ThieleUniversal.program_instrs ThieleUniversal.Halt)
    with (nth 7 UTM_Program.program_instrs ThieleUniversal.Halt).
  cbn [UTM_Program.program_instrs].
  reflexivity.
Qed.

Lemma utm_fetch_pc_after_five_steps :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 5) = 5.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit)
    as [_ [_ [_ Hpc4]]].
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode4.
  pose proof (ThieleUniversal.run1_pc_succ_instr
                (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4)
                _ Hdecode4) as Hsucc.
  assert (ThieleUniversal.CPU.pc_unchanged
            (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_Q'
               ThieleUniversal.CPU.REG_ADDR)) by
    (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
  specialize (Hsucc H).
  change (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 5)
    with (ThieleUniversal.run1
            (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4)).
  rewrite Hsucc.
  exact Hpc4.
Qed.

Lemma utm_fetch_pc_after_seven_steps :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n (utm_cpu_state tm conf) 7) = 7.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu5 := ThieleUniversal.run_n cpu0 5).
  set (cpu6 := ThieleUniversal.run1 cpu5).
  set (cpu7 := ThieleUniversal.run1 cpu6).
  pose proof (utm_decode_findrule_subtract_instruction tm q tape head Hfit)
    as Hdecode6.
  assert (Hpc_succ6 :
            ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu7 = 7).
  { subst cpu7.
    apply (ThieleUniversal.run1_pc_succ_instr
             cpu6
             (ThieleUniversal.CPU.SubReg ThieleUniversal.CPU.REG_TEMP1
                ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_Q')).
    - exact Hdecode6.
    - unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia.
  }
  subst cpu5 cpu6 cpu7.
  change (ThieleUniversal.run_n cpu0 7)
    with (ThieleUniversal.run1 (ThieleUniversal.run1 (ThieleUniversal.run_n cpu0 5))).
  rewrite Hpc_succ6.
  reflexivity.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step2 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n
         (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) 3) < 29.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  pose proof (utm_fetch_pc_after_five_steps tm q tape head Hfit) as Hpc5.
  pose proof (utm_decode_findrule_copy_q_instruction tm q tape head Hfit)
    as Hdecode5.
  pose proof (ThieleUniversal.run1_pc_succ_instr
                (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 5)
                _ Hdecode5) as Hsucc.
  assert (ThieleUniversal.CPU.pc_unchanged
            (ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
               ThieleUniversal.CPU.REG_Q)) by
    (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
  specialize (Hsucc H).
  rewrite Hpc5 in Hsucc.
  change (ThieleUniversal.run_n
            (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) 3)
    with (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 6).
  rewrite (ThieleUniversal.run_n_add (utm_cpu_state tm ((q, tape), head)) 5 1).
  simpl.
  change (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 6)
    with (ThieleUniversal.run1
            (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 5)).
  rewrite Hsucc.
  lia.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step3 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n
         (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) 4) < 29.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_fetch_pc_after_five_steps tm q tape head Hfit) as Hpc5.
  pose proof (utm_decode_findrule_copy_q_instruction tm q tape head Hfit)
    as Hdecode5.
  pose proof (ThieleUniversal.run1_pc_succ_instr
                (ThieleUniversal.run_n cpu0 5)
                (ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
                   ThieleUniversal.CPU.REG_Q)
                Hdecode5) as Hsucc5.
  assert (Hunchanged5 : ThieleUniversal.CPU.pc_unchanged
                           (ThieleUniversal.CPU.CopyReg
                              ThieleUniversal.CPU.REG_TEMP1
                              ThieleUniversal.CPU.REG_Q))
    by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
  specialize (Hsucc5 Hunchanged5).
  change (ThieleUniversal.run_n cpu0 6)
    with (ThieleUniversal.run1 (ThieleUniversal.run_n cpu0 5)) in Hsucc5.
  rewrite Hpc5 in Hsucc5.
  pose proof (utm_decode_findrule_subtract_instruction tm q tape head Hfit)
    as Hdecode6.
  pose proof (ThieleUniversal.run1_pc_succ_instr
                (ThieleUniversal.run_n cpu0 6)
                (ThieleUniversal.CPU.SubReg ThieleUniversal.CPU.REG_TEMP1
                   ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_Q')
                Hdecode6) as Hsucc6.
  assert (Hunchanged6 : ThieleUniversal.CPU.pc_unchanged
                           (ThieleUniversal.CPU.SubReg
                              ThieleUniversal.CPU.REG_TEMP1
                              ThieleUniversal.CPU.REG_TEMP1
                              ThieleUniversal.CPU.REG_Q'))
    by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
  specialize (Hsucc6 Hunchanged6).
  change (ThieleUniversal.run_n cpu0 7)
    with (ThieleUniversal.run1 (ThieleUniversal.run_n cpu0 6)) in Hsucc6.
  rewrite Hsucc5 in Hsucc6.
  change (ThieleUniversal.run_n cpu0 7)
    with (ThieleUniversal.run_n (ThieleUniversal.run_n cpu0 3) 4).
  rewrite Hsucc6.
  lia.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step4 :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n
         (ThieleUniversal.run_n (utm_cpu_state tm conf) 3) 5) < 29.
Proof.
  intros tm q tape head conf Hfit.
  subst conf.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_decode_findrule_jump_zero_instruction tm q tape head Hfit)
    as Hdecode7.
  pose proof (utm_fetch_pc_after_seven_steps tm q tape head Hfit) as Hpc7.
  set (cpu7 := ThieleUniversal.run_n cpu0 7).
  change (ThieleUniversal.run_n (ThieleUniversal.run_n cpu0 3) 5)
    with (ThieleUniversal.run_n cpu0 8).
  destruct (Nat.eqb (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_TEMP1 cpu7) 0)
    eqn:Hz.
  - pose proof (ThieleUniversal.run1_jz_true_read
                  cpu7 ThieleUniversal.CPU.REG_TEMP1 12 ThieleUniversal.CPU.REG_PC
                  Hdecode7 Hz) as Hpc_run.
    change (ThieleUniversal.run_n cpu0 8)
      with (ThieleUniversal.run1 cpu7).
    rewrite Hpc_run.
    rewrite ThieleUniversal.CPU.read_pc_write_pc.
    lia.
  - pose proof (ThieleUniversal.run1_jz_false_read
                  cpu7 ThieleUniversal.CPU.REG_TEMP1 12 ThieleUniversal.CPU.REG_PC
                  Hdecode7 Hz) as Hpc_run.
    change (ThieleUniversal.run_n cpu0 8)
      with (ThieleUniversal.run1 cpu7).
      rewrite Hpc_run.
      rewrite ThieleUniversal.CPU.read_pc_write_pc.
      rewrite Hpc7.
      lia.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step5 :
  forall tm q tape head,
    rules_fit tm ->
    head < length tape ->
    utm_pc_prefix_lt
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) 6.
Proof.
  intros tm q tape head Hfit Hhead_lt.
  set (cpu_find :=
         ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3).
  pose proof (utm_find_rule_loop_pc_prefix_base tm q tape head Hfit Hhead_lt)
    as Hbase.
  pose proof (utm_pc_prefix_lt_of_le cpu_find 2 Hbase) as Hprefix3.
  pose proof (utm_find_rule_loop_pc_prefix_step2 tm q tape head Hfit)
    as Hpc3.
  pose proof (utm_pc_prefix_lt_succ cpu_find 3 Hprefix3 Hpc3)
    as Hprefix4.
  pose proof (utm_find_rule_loop_pc_prefix_step3 tm q tape head Hfit)
    as Hpc4.
  pose proof (utm_pc_prefix_lt_succ cpu_find 4 Hprefix4 Hpc4)
    as Hprefix5.
  pose proof (utm_find_rule_loop_pc_prefix_step4 tm q tape head Hfit)
    as Hpc5.
  pose proof (utm_pc_prefix_lt_succ cpu_find 5 Hprefix5 Hpc5)
    as Hprefix6.
  exact Hprefix6.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step6 :
  forall tm q tape head,
    rules_fit tm ->
    head < length tape ->
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
      (ThieleUniversal.run_n
         (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) 6)
    < 29.
Proof.
  intros tm q tape head Hfit Hhead_lt.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu7 := ThieleUniversal.run_n cpu0 7).
  pose proof (utm_decode_findrule_jump_zero_instruction tm q tape head Hfit)
    as Hdecode7.
  pose proof (utm_fetch_pc_after_seven_steps tm q tape head Hfit) as Hpc7.
  set (cpu8 := ThieleUniversal.run1 cpu7).
  assert (Hprog7 :
            firstn (length ThieleUniversal.program)
              (ThieleUniversal.CPU.mem cpu7)
          = ThieleUniversal.program).
  {
    pose proof (utm_fetch_preserves_program_image tm q tape head Hfit)
      as Hprog3.
    pose proof (utm_fetch_pc_after_three_steps tm q tape head Hfit)
      as Hpc3.
    pose proof (utm_run1_preserves_program_image_before_apply
                  (ThieleUniversal.run_n cpu0 3) Hprog3 Hpc3)
      as Hprog4.
    pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit)
      as [_ [_ [_ Hpc4]]].
    pose proof (utm_run1_preserves_program_image_before_apply
                  (ThieleUniversal.run_n cpu0 4) Hprog4 Hpc4)
      as Hprog5.
    pose proof (utm_fetch_pc_after_five_steps tm q tape head Hfit)
      as Hpc5.
    pose proof (utm_run1_preserves_program_image_before_apply
                  (ThieleUniversal.run_n cpu0 5) Hprog5 Hpc5)
      as Hprog6.
    pose proof (utm_find_rule_loop_pc_prefix_step2 tm q tape head Hfit)
      as Hpc6.
    change (ThieleUniversal.run_n cpu0 6)
      with (ThieleUniversal.run_n (ThieleUniversal.run_n cpu0 3) 3)
      in Hprog6, Hpc6.
    pose proof (utm_run1_preserves_program_image_before_apply
                  (ThieleUniversal.run_n cpu0 6) Hprog6 Hpc6)
      as Hprog7'.
    exact Hprog7'.
  }
  pose proof (utm_run1_preserves_program_image_before_apply
                cpu7 Hprog7 Hpc7) as Hprog8.
  change (ThieleUniversal.run_n cpu0 9)
    with (ThieleUniversal.run_n cpu8 1).
  change (ThieleUniversal.run_n cpu0 8)
    with cpu8.
  destruct (Nat.eqb (ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_TEMP1
                       cpu7) 0) eqn:Hz.
  - pose proof (ThieleUniversal.run1_jz_true_read
                  cpu7 ThieleUniversal.CPU.REG_TEMP1 12
                  ThieleUniversal.CPU.REG_PC Hdecode7 Hz) as Hpc8.
    change (ThieleUniversal.run_n cpu0 8)
      with cpu8 in Hpc8.
    assert (Hpc_lt :
              ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu8
              < length ThieleUniversal.program_instrs).
    { rewrite Hpc8.
      apply ThieleUniversal.program_instrs_length_gt_29.
    }
    pose proof (ThieleUniversal.decode_instr_program_state cpu8 Hpc_lt Hprog8)
      as Hdecode8.
    rewrite Hpc8 in Hdecode8.
    rewrite ThieleUniversal.decode_instr_program_at_pc with (pc := 12) in Hdecode8
      by (pose proof ThieleUniversal.program_instrs_length_gt_48; lia).
    change (nth 12 ThieleUniversal.program_instrs ThieleUniversal.Halt)
      with (ThieleUniversal.CPU.CopyReg ThieleUniversal.CPU.REG_TEMP1
              ThieleUniversal.CPU.REG_ADDR) in Hdecode8.
    pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu8 _ Hdecode8) as Hsucc.
    assert (Hunchanged : ThieleUniversal.CPU.pc_unchanged
                            (ThieleUniversal.CPU.CopyReg
                               ThieleUniversal.CPU.REG_TEMP1
                               ThieleUniversal.CPU.REG_ADDR))
      by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc8 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
  - pose proof (ThieleUniversal.run1_jz_false_read
                  cpu7 ThieleUniversal.CPU.REG_TEMP1 12
                  ThieleUniversal.CPU.REG_PC Hdecode7 Hz) as Hpc8.
    change (ThieleUniversal.run_n cpu0 8)
      with cpu8 in Hpc8.
    assert (Hpc_lt :
              ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu8
              < length ThieleUniversal.program_instrs).
    { rewrite Hpc8.
      apply ThieleUniversal.program_instrs_length_gt_29.
    }
    pose proof (ThieleUniversal.decode_instr_program_state cpu8 Hpc_lt Hprog8)
      as Hdecode8.
    rewrite Hpc8 in Hdecode8.
    rewrite ThieleUniversal.decode_instr_program_at_pc with (pc := 8) in Hdecode8
      by (pose proof ThieleUniversal.program_instrs_length_gt_29; lia).
    change (nth 8 ThieleUniversal.program_instrs ThieleUniversal.Halt)
      with (ThieleUniversal.CPU.AddConst ThieleUniversal.CPU.REG_ADDR 5)
      in Hdecode8.
    pose proof (ThieleUniversal.run1_pc_succ_instr
                  cpu8 _ Hdecode8) as Hsucc.
    assert (Hunchanged : ThieleUniversal.CPU.pc_unchanged
                            (ThieleUniversal.CPU.AddConst
                               ThieleUniversal.CPU.REG_ADDR 5))
      by (unfold ThieleUniversal.CPU.pc_unchanged; simpl; lia).
    specialize (Hsucc Hunchanged).
    rewrite Hpc8 in Hsucc.
    simpl in Hsucc.
    exact Hsucc.
Qed.

Lemma utm_find_rule_loop_pc_prefix_step7 :
  forall tm q tape head,
    rules_fit tm ->
    head < length tape ->
    utm_pc_prefix_lt
      (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3) 7.
Proof.
  intros tm q tape head Hfit Hhead_lt.
  set (cpu_find := ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 3).
  pose proof (utm_find_rule_loop_pc_prefix_step5 tm q tape head Hfit Hhead_lt)
    as Hprefix6.
  pose proof (utm_find_rule_loop_pc_prefix_step6 tm q tape head Hfit Hhead_lt)
    as Hpc6.
  exact (utm_pc_prefix_lt_succ cpu_find 6 Hprefix6 Hpc6).
Qed.

Lemma utm_fetch_reset_addr_after_four_steps :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    let st3 := ThieleUniversal.run_n (utm_cpu_state tm conf) 3 in
    let st4 := ThieleUniversal.run_n (utm_cpu_state tm conf) 4 in
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR st4 =
      UTM_Program.RULES_START_ADDR /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q st4 =
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q st3 /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM st4 =
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM st3 /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC st4 = 4.
Proof.
  intros tm q tape head conf Hfit st3 st4.
  subst conf st3 st4.
  set (cpu0 := utm_cpu_state tm ((q, tape), head)).
  set (cpu1 := ThieleUniversal.run1 cpu0).
  set (cpu2 := ThieleUniversal.run1 cpu1).
  set (cpu3 := ThieleUniversal.run1 cpu2).
  set (cpu4 := ThieleUniversal.run1 cpu3).
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv.
  destruct Hinv as [Hq_init [Hhead_init [Hpc0 [Htape [Hprog_mem Hrules_mem]]]]].
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [Hq'_bound [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode0.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode1.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode2.
  pose proof (utm_decode_findrule_reset_instruction tm q tape head Hfit)
    as Hdecode3.
  assert (Hpc1 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu1 = 1).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu0 _ Hdecode0) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_TEMP1
                 UTM_Program.TAPE_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc0 in Hsucc.
    exact Hsucc. }
  assert (Hpc2 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu2 = 2).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu1 _ Hdecode1) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.AddReg ThieleUniversal.CPU.REG_ADDR
                 ThieleUniversal.CPU.REG_TEMP1 ThieleUniversal.CPU.REG_HEAD))
      by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc1 in Hsucc.
    exact Hsucc. }
  assert (Hpc3 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu3 = 3).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu2 _ Hdecode2) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadIndirect ThieleUniversal.CPU.REG_SYM
                 ThieleUniversal.CPU.REG_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc2 in Hsucc.
    exact Hsucc. }
  assert (Hmem1 : ThieleUniversal.CPU.mem cpu1 = ThieleUniversal.CPU.mem cpu0).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode0. simpl. exact I. }
  assert (Hmem2 : ThieleUniversal.CPU.mem cpu2 = ThieleUniversal.CPU.mem cpu1).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode1. simpl. exact I. }
  assert (Hmem3 : ThieleUniversal.CPU.mem cpu3 = ThieleUniversal.CPU.mem cpu2).
  { apply ThieleUniversal.run1_mem_preserved_if_no_store.
    rewrite Hdecode2. simpl. exact I. }
  assert (Hlen_cpu1 : length (ThieleUniversal.CPU.regs cpu1) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc0. lia.
    - exact Hprog_mem.
    - exact Hregs_len.
  }
  assert (Hlen_cpu2 : length (ThieleUniversal.CPU.regs cpu2) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc1. lia.
    - rewrite Hmem1. exact Hprog_mem.
    - exact Hlen_cpu1.
  }
  assert (Hlen_cpu3 : length (ThieleUniversal.CPU.regs cpu3) = 10).
  { apply ThieleUniversal.run1_regs_length_before_apply; try assumption.
    - rewrite Hpc2. lia.
    - rewrite Hmem2, Hmem1. exact Hprog_mem.
    - exact Hlen_cpu2.
  }
  assert (Hpc4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu4 = 4).
  { pose proof (ThieleUniversal.run1_pc_succ_instr cpu3 _ Hdecode3) as Hsucc.
    assert (ThieleUniversal.CPU.pc_unchanged
              (ThieleUniversal.CPU.LoadConst ThieleUniversal.CPU.REG_ADDR
                 UTM_Program.RULES_START_ADDR)) by (simpl; lia).
    specialize (Hsucc H).
    rewrite Hpc3 in Hsucc.
    exact Hsucc. }
  assert (Hpc_bound_cpu3 : ThieleUniversal.CPU.REG_PC < length (ThieleUniversal.CPU.regs cpu3)).
  { rewrite Hlen_cpu3. lia. }
  assert (Haddr_bound_cpu3 : ThieleUniversal.CPU.REG_ADDR < length (ThieleUniversal.CPU.regs cpu3)).
  { rewrite Hlen_cpu3. rewrite <- Hregs_len in Haddr_bound. exact Haddr_bound. }
  assert (Hq_bound_cpu3 : ThieleUniversal.CPU.REG_Q < length (ThieleUniversal.CPU.regs cpu3)).
  { rewrite Hlen_cpu3. rewrite <- Hregs_len in Hq_bound. exact Hq_bound. }
  assert (Hsym_bound_cpu3 : ThieleUniversal.CPU.REG_SYM < length (ThieleUniversal.CPU.regs cpu3)).
  { rewrite Hlen_cpu3. rewrite <- Hregs_len in Hsym_bound. exact Hsym_bound. }
  assert (Haddr_cpu4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR cpu4 =
          UTM_Program.RULES_START_ADDR).
  { apply (ThieleUniversal.run1_loadconst_result
             cpu3 ThieleUniversal.CPU.REG_ADDR
             UTM_Program.RULES_START_ADDR);
      try assumption.
    - exact Hdecode3.
    - exact Hpc_bound_cpu3.
    - exact Haddr_bound_cpu3.
  }
  assert (Hq_cpu4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu4 =
          ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu3).
  { apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu3 ThieleUniversal.CPU.REG_ADDR
             UTM_Program.RULES_START_ADDR
             ThieleUniversal.CPU.REG_Q);
      try assumption; try lia.
    - exact Hdecode3.
    - exact Hpc_bound_cpu3.
    - exact Haddr_bound_cpu3.
    - exact Hq_bound_cpu3.
    - discriminate.
    - discriminate.
  }
  assert (Hsym_cpu4 : ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM cpu4 =
          ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM cpu3).
  { apply (ThieleUniversal.run1_preserves_reg_loadconst
             cpu3 ThieleUniversal.CPU.REG_ADDR
             UTM_Program.RULES_START_ADDR
             ThieleUniversal.CPU.REG_SYM);
      try assumption; try lia.
    - exact Hdecode3.
    - exact Hpc_bound_cpu3.
    - exact Haddr_bound_cpu3.
    - exact Hsym_bound_cpu3.
    - discriminate.
    - discriminate.
  }
  simpl in Haddr_cpu4, Hq_cpu4, Hsym_cpu4, Hpc4.
  repeat split; try assumption.
  - unfold ThieleUniversal.run_n.
    simpl.
    exact Haddr_cpu4.
  - unfold ThieleUniversal.run_n.
    simpl.
    exact Hq_cpu4.
  - unfold ThieleUniversal.run_n.
    simpl.
    exact Hsym_cpu4.
  - unfold ThieleUniversal.run_n.
    simpl.
    exact Hpc4.
Qed.

Lemma utm_fetch_reset_state :
  forall tm q tape head,
    let conf := ((q, tape), head) in
    rules_fit tm ->
    let cpu0 := utm_cpu_state tm conf in
    let cpu_find := ThieleUniversal.run_n cpu0 3 in
    let cpu_reset := ThieleUniversal.run_n cpu0 4 in
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_ADDR cpu_reset =
      UTM_Program.RULES_START_ADDR /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu_reset =
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_Q cpu_find /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM cpu_reset =
      ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_SYM cpu_find /\
    ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC cpu_reset = 4.
Proof.
  intros tm q tape head conf Hfit cpu0 cpu_find cpu_reset.
  subst conf cpu0 cpu_find cpu_reset.
  pose proof (utm_fetch_reset_addr_after_four_steps tm q tape head Hfit) as Hreset.
  simpl in Hreset.
  exact Hreset.
Qed.

(* Executing a Thiele program for [k] steps.  The full small-step      *)
(* semantics lives in [ThieleMachine.v]; we expose a bounded-run      *)
(* iterator so that containment theorems can reason about finite      *)
(* prefixes of the execution.                                         *)
Fixpoint thiele_step_n (p : Prog) (st : State) (n : nat) : State :=
  match n with
  | 0 => st
  | S n' => thiele_step_n p (thiele_step p st) n'
  end.

Parameter utm_program : Prog.
Parameter utm_program_blind : Blind utm_program.

Lemma thiele_step_n_S_n : forall p st n,
  thiele_step_n p st (S n) = thiele_step_n p (thiele_step p st) n.
Proof. reflexivity. Qed.

Record InterpreterObligations (tm : TM) := {
  interpreter_preserves_ok :
    forall conf, config_ok tm conf -> config_ok tm (tm_step tm conf);
  interpreter_simulate_one_step :
    forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf;
  interpreter_simulation_steps :
    forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k
}.

Record StepInvariantBoundsTM (tm : TM) := {
  bounds_step_digits :
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in digits_ok tape';
  bounds_step_length :
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in (length tape' <= EncodingMod.SHIFT_LEN)%nat;
  bounds_step_head :
    forall conf,
      config_ok tm conf ->
      let '(_, _, head') := tm_step tm conf in (head' < EncodingMod.SHIFT_BIG)%nat
}.

Lemma bounds_preserve_ok :
  forall tm (B : StepInvariantBoundsTM tm) conf,
    config_ok tm conf -> config_ok tm (tm_step tm conf).
Proof.
  intros tm B [[q tape] head] Hok.
  simpl in *.
  remember (tm_step tm (q, tape, head)) as step eqn:Hstep.
  destruct step as [[q' tape'] head'].
  simpl in *.
  pose proof (bounds_step_digits B (q, tape, head) Hok) as Hdigs.
  pose proof (bounds_step_length B (q, tape, head) Hok) as Hlen.
  pose proof (bounds_step_head B (q, tape, head) Hok) as Hhead.
  rewrite Hstep in Hdigs, Hlen, Hhead.
  simpl in Hdigs, Hlen, Hhead.
  repeat split; assumption.
Qed.

Lemma bounds_from_preservation :
  forall tm,
    (forall conf, config_ok tm conf -> config_ok tm (tm_step tm conf)) ->
    StepInvariantBoundsTM tm.
Proof.
  intros tm Hpres.
  refine
    {| bounds_step_digits := _;
       bounds_step_length := _;
       bounds_step_head := _ |};
    intros [[q tape] head] Hok;
    simpl in *.
  all: specialize (Hpres (q, tape, head) Hok) as [Hdigs' [Hlen' Hhead']];
       destruct Hok as [Hdigs [Hlen Hhead]];
       simpl in *;
       assumption.
Qed.

Lemma find_rule_in :
  forall rules q sym q' write move,
    find_rule rules q sym = Some (q', write, move) ->
    In (q, sym, q', write, move) rules.
Proof.
  intros rules q sym q' write move Hfind.
  induction rules as [|rule rules IH]; simpl in *; try discriminate.
  destruct rule as [[[[q_rule sym_rule] q_next] write_rule] move_rule].
  destruct (andb (Nat.eqb q_rule q) (Nat.eqb sym_rule sym)) eqn:Hmatch.
  - inversion Hfind; subst.
    apply andb_true_iff in Hmatch as [Hq Hsym].
    apply Nat.eqb_eq in Hq.
    apply Nat.eqb_eq in Hsym.
    subst.
    simpl.
    left; reflexivity.
  - right.
    apply IH; assumption.
Qed.

Lemma find_rule_forall :
  forall (rules : list (nat * nat * nat * nat * Z))
         (P : nat * nat * nat * nat * Z -> Prop)
         q sym q' write move,
    Forall P rules ->
    find_rule rules q sym = Some (q', write, move) ->
    P (q, sym, q', write, move).
Proof.
  intros rules P q sym q' write move Hforall Hfind.
  pose proof Hforall as Hforall'.
  apply Forall_forall with (x := (q, sym, q', write, move)) in Hforall'.
  - exact Hforall'.
  - apply find_rule_in; assumption.
Qed.

Lemma tm_step_digits_from_rule_bounds :
  forall tm conf,
    config_ok tm conf ->
    (tm.(tm_blank) < EncodingMod.BASE)%nat ->
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (write < EncodingMod.BASE)%nat) ->
    let '(_, tape', _) := tm_step tm conf in digits_ok tape'.
Proof.
  intros tm [[q tape] head] [Hdigs [Hlen Hhead]] Hblank Hwrite.
  simpl in *.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. exact Hdigs. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[ [q' write] move] |] eqn:Hrule.
  - simpl.
    set (tape_ext := if Nat.ltb head (length tape)
                     then tape
                     else tape ++ repeat tm.(tm_blank) (head - length tape)).
    assert (Hext : digits_ok tape_ext).
    { unfold tape_ext.
      destruct (Nat.ltb head (length tape)).
      - exact Hdigs.
      - apply digits_ok_app; [exact Hdigs|].
        apply digits_ok_repeat; exact Hblank.
    }
    assert (Hfirst : digits_ok (firstn head tape_ext)).
    { apply digits_ok_firstn; exact Hext. }
    assert (Hskip : digits_ok (skipn (S head) tape_ext)).
    { apply digits_ok_skipn; exact Hext. }
    assert (Hwrite_lt : (write < EncodingMod.BASE)%nat).
    { apply Hwrite with (q:=q) (sym:=sym) (q':=q') (move:=move).
      exact Hrule.
    }
    apply digits_ok_app.
    * apply digits_ok_app; [exact Hfirst|].
      unfold digits_ok.
      constructor; [exact Hwrite_lt|constructor].
    * exact Hskip.
  - simpl. exact Hdigs.
Qed.

Lemma length_update_within :
  forall (tape : list nat) (head write : nat),
    head < length tape ->
    length (firstn head tape ++ write :: skipn (S head) tape) = length tape.
Proof.
  intros tape head write Hlt.
  rewrite app_length, app_length.
  simpl.
  rewrite firstn_length, skipn_length.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma length_update_extend :
  forall (tape : list nat) (head blank write : nat),
    length tape <= head ->
    length (firstn head (tape ++ repeat blank (head - length tape)) ++
            write :: skipn (S head) (tape ++ repeat blank (head - length tape))) =
    S head.
Proof.
  intros tape head blank write Hle.
  set (tape_ext := tape ++ repeat blank (head - length tape)).
  assert (Hlen_ext : length tape_ext = head).
  { unfold tape_ext.
    rewrite app_length, repeat_length.
    lia.
  }
  rewrite app_length, app_length.
  simpl.
  rewrite firstn_length, skipn_length.
  rewrite Hlen_ext.
  rewrite Nat.min_l by lia.
  lia.
Qed.

Lemma tm_step_length_from_head_bound :
  forall tm,
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    forall conf,
      config_ok tm conf ->
      let '(_, tape', _) := tm_step tm conf in (length tape' <= EncodingMod.SHIFT_LEN)%nat.
Proof.
  intros tm Hhead conf Hok.
  destruct conf as [[q tape] head].
  simpl in *.
  destruct Hok as [Hdigs [Hlen Hhead_big]].
  specialize (Hhead _ (conj Hdigs (conj Hlen Hhead_big))) as Hhead_lt.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. exact Hlen. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[[q' write] move]|] eqn:Hrule.
  - simpl.
    set (tape_ext := if Nat.ltb head (length tape)
                     then tape
                     else tape ++ repeat tm.(tm_blank) (head - length tape)).
    destruct (Nat.ltb head (length tape)) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      replace tape_ext with tape by (unfold tape_ext; rewrite Hlt; reflexivity).
      rewrite (length_update_within tape head write Hlt).
      exact Hlen.
    + apply Nat.ltb_ge in Hlt.
      replace tape_ext with (tape ++ repeat tm.(tm_blank) (head - length tape))
        by (unfold tape_ext; rewrite Hlt; reflexivity).
      rewrite (length_update_extend tape head tm.(tm_blank) write Hlt).
      lia.
  - simpl. exact Hlen.
Qed.

Record StepInvariantBoundsCatalogue (tm : TM) := {
  sibc_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sibc_rule_write_lt_base :
    Forall (fun rule => let '(_, _, _, write, _) := rule in (write < EncodingMod.BASE)%nat)
           (tm_rules tm);
  sibc_rule_move_le_one :
    Forall (fun rule => let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z)
           (tm_rules tm);
  sibc_head_lt_shift_len :
    forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat
}.

Record StepInvariantBoundsCatalogueWitness (tm : TM) := {
  sibcw_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sibcw_rule_bounds :
    forall q sym q' write move,
      In (q, sym, q', write, move) (tm_rules tm) ->
      (write < EncodingMod.BASE)%nat /\ (Z.abs move <= 1)%Z;
  sibcw_head_lt_shift_len :
    forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat;
  sibcw_rules_fit : rules_fit tm
}.

Definition rule_write_lt_base_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  let '(_, _, _, write, _) := rule in Nat.ltb write EncodingMod.BASE.

Definition rule_move_le_one_check
  (rule : nat * nat * nat * nat * Z) : bool :=
  let '(_, _, _, _, move) := rule in Z.leb (Z.abs move) 1%Z.

Definition catalogue_static_check (tm : TM) : bool :=
  Nat.ltb (tm_blank tm) EncodingMod.BASE &&
  forallb rule_write_lt_base_check (tm_rules tm) &&
  forallb rule_move_le_one_check (tm_rules tm).

Lemma forallb_true_iff :
  forall (A : Type) (f : A -> bool) (xs : list A),
    forallb f xs = true -> Forall (fun x => f x = true) xs.
Proof.
  intros A f xs Hfor.
  induction xs as [|x xs IH] in Hfor |- *; simpl in *.
  - constructor.
  - apply Bool.andb_true_iff in Hfor as [Hx Htail].
    constructor; [assumption|].
    apply IH. assumption.
Qed.

Lemma rule_write_lt_base_check_true :
  forall rule,
    rule_write_lt_base_check rule = true ->
    let '(_, _, _, write, _) := rule in (write < EncodingMod.BASE)%nat.
Proof.
  intros [[[[q sym] q'] write] move] Hcheck. simpl in *.
  apply Nat.ltb_lt in Hcheck. exact Hcheck.
Qed.

Lemma rule_move_le_one_check_true :
  forall rule,
    rule_move_le_one_check rule = true ->
    let '(_, _, _, _, move) := rule in (Z.abs move <= 1)%Z.
Proof.
  intros [[[[q sym] q'] write] move] Hcheck. simpl in *.
  apply Z.leb_le in Hcheck. exact Hcheck.
Qed.

Lemma catalogue_static_check_witness :
  forall tm,
    catalogue_static_check tm = true ->
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    rules_fit tm ->
    StepInvariantBoundsCatalogueWitness tm.
Proof.
  intros tm Hcheck Hhead Hfit.
  unfold catalogue_static_check in Hcheck.
  apply Bool.andb_true_iff in Hcheck as [Hblank Hrest].
  apply Bool.andb_true_iff in Hrest as [Hwrite_bool Hmove_bool].
  pose proof (forallb_true_iff _ _ Hwrite_bool) as Hwrite_forall.
  pose proof (forallb_true_iff _ _ Hmove_bool) as Hmove_forall.
  refine {| sibcw_blank_lt_base := Nat.ltb_lt (tm_blank tm) EncodingMod.BASE Hblank;
            sibcw_rule_bounds := _;
            sibcw_head_lt_shift_len := Hhead;
            sibcw_rules_fit := Hfit |}.
  intros q sym q' write move Hin.
  split.
  - specialize (Forall_forall Hwrite_forall (q, sym, q', write, move) Hin) as Hwrite.
    apply rule_write_lt_base_check_true. exact Hwrite.
  - specialize (Forall_forall Hmove_forall (q, sym, q', write, move) Hin) as Hmove.
    apply rule_move_le_one_check_true. exact Hmove.
Qed.

Lemma catalogue_from_static_check :
  forall tm,
    catalogue_static_check tm = true ->
    (forall conf, config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat) ->
    rules_fit tm ->
    StepInvariantBoundsCatalogue tm.
Proof.
  intros tm Hcheck Hhead Hfit.
  apply catalogue_from_witness.
  apply catalogue_static_check_witness; assumption.
Qed.

Lemma catalogue_from_witness :
  forall tm (W : StepInvariantBoundsCatalogueWitness tm),
    StepInvariantBoundsCatalogue tm.
Proof.
  intros tm [Hblank Hbounds Hhead _].
  refine
    {| sibc_blank_lt_base := Hblank;
       sibc_rule_write_lt_base := _;
       sibc_rule_move_le_one := _;
       sibc_head_lt_shift_len := Hhead |}.
  - apply Forall_forall. intros rule Hin.
    destruct rule as [[[[q sym] q'] write] move].
    specialize (Hbounds q sym q' write move Hin) as [Hwrite _].
    exact Hwrite.
  - apply Forall_forall. intros rule Hin.
    destruct rule as [[[[q sym] q'] write] move].
    specialize (Hbounds q sym q' write move Hin) as [_ Hmove].
    exact Hmove.
Qed.

Lemma catalogue_static_check_of_witness :
  forall tm (W : StepInvariantBoundsCatalogueWitness tm),
    catalogue_static_check tm = true.
Proof.
  intros tm [Hblank Hbounds Hhead _].
  unfold catalogue_static_check.
  apply Bool.andb_true_iff; split.
  - apply Nat.ltb_lt. exact Hblank.
  - apply Bool.andb_true_iff; split.
    + apply forallb_forall. intros rule Hin.
      destruct rule as [[[[q sym] q'] write] move].
      specialize (Hbounds q sym q' write move Hin) as [Hwrite _].
      simpl. apply Nat.ltb_lt. exact Hwrite.
    + apply forallb_forall. intros rule Hin.
      destruct rule as [[[[q sym] q'] write] move].
      specialize (Hbounds q sym q' write move Hin) as [_ Hmove].
      simpl. apply Z.leb_le. exact Hmove.
Qed.

Record StepInvariantBoundsData (tm : TM) := {
  sib_blank_lt_base : (tm_blank tm < EncodingMod.BASE)%nat;
  sib_rule_write_lt_base :
    forall q sym q' write move,
      find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
      (write < EncodingMod.BASE)%nat;
  sib_rule_move_le_one :
    forall q sym q' write move,
      find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
      (Z.abs move <= 1)%Z;
  sib_head_lt_shift_len :
    forall conf,
      config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat
}.

Lemma step_data_from_catalogue :
  forall tm (C : StepInvariantBoundsCatalogue tm),
    StepInvariantBoundsData tm.
Proof.
  intros tm [Hblank Hwrite Hmove Hhead].
  refine
    {| sib_blank_lt_base := Hblank;
       sib_rule_write_lt_base := _;
       sib_rule_move_le_one := _;
       sib_head_lt_shift_len := Hhead |}.
  - intros q sym q' write move Hfind.
    pose proof (find_rule_forall (tm_rules tm)
                  (fun rule => let '(_, _, _, write0, _) := rule in (write0 < EncodingMod.BASE)%nat)
                  q sym q' write move Hwrite Hfind) as H.
    simpl in H.
    exact H.
  - intros q sym q' write move Hfind.
    pose proof (find_rule_forall (tm_rules tm)
                  (fun rule => let '(_, _, _, _, move0) := rule in (Z.abs move0 <= 1)%Z)
                  q sym q' write move Hmove Hfind) as H.
    simpl in H.
    exact H.
Qed.

Lemma move_abs_le_one_to_nat :
  forall head move,
    (Z.abs move <= 1)%Z ->
    Z.to_nat (Z.max 0%Z (Z.of_nat head + move)%Z) <= S head.
Proof.
  intros head move Habs.
  assert (Hrange : (-1 <= move <= 1)%Z) by (apply Z.abs_le; lia).
  destruct Hrange as [_ Hupper].
  assert (Hmax_le : (Z.max 0%Z (Z.of_nat head + move)%Z <= Z.of_nat head + 1)%Z).
  { apply Z.max_lub; lia. }
  replace (Z.of_nat head + 1)%Z with (Z.of_nat (S head)) in Hmax_le by lia.
  pose proof (Z.le_max_l 0%Z (Z.of_nat head + move)%Z) as Hnonneg.
  pose proof (Nat2Z.is_nonneg (S head)) as Hs_nonneg.
  pose proof (Z2Nat.inj_le _ _ Hnonneg Hs_nonneg Hmax_le) as Hnat.
  rewrite Z2Nat.id in Hnat by lia.
  exact Hnat.
Qed.

Lemma tm_step_head_le_succ :
  forall tm,
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (Z.abs move <= 1)%Z) ->
    forall conf,
      let '(_, _, head') := tm_step tm conf in
      let '(_, _, head) := conf in
      head' <= S head.
Proof.
  intros tm Hmove [[q tape] head].
  simpl in *.
  unfold tm_step.
  destruct (Nat.eqb q (tm_accept tm) || Nat.eqb q (tm_reject tm)) eqn:Hhalt.
  { simpl. lia. }
  set (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule (tm_rules tm) q sym) as [[[q' write] move]|] eqn:Hrule.
  - simpl.
    apply move_abs_le_one_to_nat.
    apply Hmove with (q:=q) (sym:=sym) (q':=q') (write:=write) (move:=move).
    exact Hrule.
  - simpl. lia.
Qed.

Lemma tm_step_head_within_big_from_moves :
  forall tm,
    (forall q sym q' write move,
        find_rule tm.(tm_rules) q sym = Some (q', write, move) ->
        (Z.abs move <= 1)%Z) ->
    forall conf,
      config_ok tm conf ->
      let '(_, _, head') := tm_step tm conf in (head' < EncodingMod.SHIFT_BIG)%nat.
Proof.
  intros tm Hmove [[q tape] head] Hok.
  simpl in *.
  pose proof (tm_step_head_le_succ tm Hmove (q, tape, head)) as Hle.
  simpl in Hle.
  destruct Hok as [_ [_ Hhead]].
  pose proof (EncodingBounds.lt_SHIFT_LEN_succ_lt_SHIFT_BIG
                EncodingMod.BASE EncodingMod.SHIFT_LEN EncodingMod.BASE_ge_2 EncodingMod.SHIFT_LEN_ge_1
                head Hhead) as Hmargin.
  apply Nat.le_lt_trans with (m := S head); assumption.
Qed.

Lemma step_bounds_from_data :
  forall tm (D : StepInvariantBoundsData tm),
    StepInvariantBoundsTM tm.
Proof.
  intros tm D.
  refine
    {| bounds_step_digits := _;
       bounds_step_length := _;
       bounds_step_head := _ |}.
  - intros conf Hok.
    apply (tm_step_digits_from_rule_bounds tm conf Hok).
    + apply sib_blank_lt_base.
    + apply sib_rule_write_lt_base.
  - intros conf Hok.
    apply (tm_step_length_from_head_bound tm (sib_head_lt_shift_len D) conf Hok).
  - intros conf Hok.
    apply (tm_step_head_within_big_from_moves tm (sib_rule_move_le_one D) conf Hok).
Qed.

Definition interpreter_obligations_from_bounds
  (tm : TM)
  (B : StepInvariantBoundsTM tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  {| interpreter_preserves_ok := bounds_preserve_ok tm B;
     interpreter_simulate_one_step := one_step;
     interpreter_simulation_steps := multi_step |}.

Definition interpreter_obligations_from_catalogue
  (tm : TM)
  (C : StepInvariantBoundsCatalogue tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  interpreter_obligations_from_bounds tm
    (step_bounds_from_data tm (step_data_from_catalogue tm C))
    one_step multi_step.

Definition step_data_from_catalogue_witness
  (tm : TM)
  (W : StepInvariantBoundsCatalogueWitness tm)
  : StepInvariantBoundsData tm :=
  step_data_from_catalogue tm (catalogue_from_witness tm W).

Definition interpreter_obligations_from_catalogue_witness
  (tm : TM)
  (W : StepInvariantBoundsCatalogueWitness tm)
  (one_step : forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf)
  (multi_step : forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k)
  : InterpreterObligations tm :=
  interpreter_obligations_from_catalogue tm
    (catalogue_from_witness tm W) one_step multi_step.

Lemma utm_head_lt_shift_len :
  forall tm conf,
    config_ok tm conf -> (tm_config_head conf < EncodingMod.SHIFT_LEN)%nat.
Proof.
  intros tm [[q tape] head] Hok.
  simpl in *.
  destruct Hok as [_ [_ Hhead]].
  exact Hhead.
Qed.

Lemma utm_catalogue_witness :
  StepInvariantBoundsCatalogueWitness utm_tm.
Proof.
  refine
    {| sibcw_blank_lt_base := utm_blank_lt_base;
       sibcw_rule_bounds := _;
       sibcw_head_lt_shift_len := utm_head_lt_shift_len utm_tm;
       sibcw_rules_fit := rules_fit_utm |}.
  intros q sym q' write move Hin.
  split.
  - pose proof utm_rules_write_lt_base as Hwrite_all.
    simpl in Hin.
    pose proof (Forall_forall _ _ Hwrite_all (q, sym, q', write, move) Hin) as Hwrite.
    simpl in Hwrite. exact Hwrite.
  - pose proof utm_rules_move_abs_le_one as Hmove_all.
    simpl in Hin.
    pose proof (Forall_forall _ _ Hmove_all (q, sym, q', write, move) Hin) as Hmove.
    simpl in Hmove. exact Hmove.
Qed.

Definition utm_step_catalogue_prop :
  StepInvariantBoundsCatalogue utm_tm :=
  catalogue_from_witness utm_tm utm_catalogue_witness.

Definition utm_step_data :
  StepInvariantBoundsData utm_tm :=
  step_data_from_catalogue_witness utm_tm utm_catalogue_witness.

Definition utm_step_bounds :
  StepInvariantBoundsTM utm_tm :=
  step_bounds_from_data utm_tm utm_step_data.

Lemma utm_catalogue_static_check :
  catalogue_static_check utm_tm = true.
Proof.
  apply catalogue_static_check_of_witness.
  exact utm_catalogue_witness.
Qed.

Definition utm_step_catalogue_witness (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  (Hfit : rules_fit tm)
  : StepInvariantBoundsCatalogueWitness tm :=
  catalogue_static_check_witness tm Hcat (utm_head_lt_shift_len tm) Hfit.

Definition utm_step_catalogue (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  (Hfit : rules_fit tm)
  : StepInvariantBoundsCatalogue tm :=
  catalogue_from_witness tm (utm_step_catalogue_witness tm Hcat Hfit).

Lemma utm_interpreter_no_rule_found_halts :
  forall tm conf cpu_find,
    let '((q, tape), head) := conf in
    let sym := nth head tape tm.(tm_blank) in
    find_rule tm.(tm_rules) q sym = None ->
    ThieleUniversal.inv_core cpu_find tm conf ->
    ThieleUniversal.find_rule_start_inv tm conf cpu_find ->
    rules_fit tm ->
    decode_state tm (ThieleUniversal.run_n cpu_find 10) = conf.
Proof.
  intros tm conf cpu_find conf_def sym_def Hfind Hcore Hstart Hfit.
  (* The proof involves symbolic execution of the loop until it reaches
     the Jnz REG_TEMP1 0 instruction at PC=11, which halts.
     After a few steps, the PC is stable and no registers affecting
     the decoded state are changed. *)
  Admitted.

Lemma utm_simulate_one_step :
  forall tm conf,
    config_ok tm conf ->
    rules_fit tm ->
    decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
    = tm_step tm conf.
Proof.
  intros tm conf Hok Hfit.
  destruct conf as [[q tape] head].
  pose (cpu0 := utm_cpu_state tm ((q, tape), head)).
  pose proof (utm_cpu_state_inv_min tm ((q, tape), head)) as Hinv_min.
  pose proof (utm_cpu_state_fetch tm ((q, tape), head)) as Hfetch.
  pose proof (utm_cpu_state_inv_from_rules_fit tm ((q, tape), head) Hfit)
    as Hinv_full.
  pose proof (utm_decode_fetch_instruction tm q tape head Hfit) as Hdecode_fetch.
  pose proof (utm_decode_findrule_address_instruction tm q tape head Hfit)
    as Hdecode_addr.
  pose proof (utm_decode_findrule_symbol_instruction tm q tape head Hfit)
    as Hdecode_symbol.
  pose proof (utm_decode_findrule_load_rule_instruction tm q tape head Hfit)
    as Hdecode_load_rule.
  pose proof (utm_decode_findrule_copy_q_instruction tm q tape head Hfit)
    as Hdecode_copy_q.
  pose proof (utm_decode_findrule_subtract_instruction tm q tape head Hfit)
    as Hdecode_sub.
  pose proof (utm_decode_findrule_jump_zero_instruction tm q tape head Hfit)
    as Hdecode_jz.
  pose proof (utm_cpu_state_regs_length tm ((q, tape), head)) as Hregs_len.
  pose proof (utm_cpu_state_reg_bound tm ((q, tape), head)) as
    [Hq_bound [Hq'_bound [Hhead_bound [Haddr_bound [Htemp_bound [Hsym_bound Hpc_bound]]]]]].
  pose proof (utm_cpu_state_read_q tm q tape head) as Hq_init.
  pose proof (utm_cpu_state_read_head tm q tape head) as Hhead_init.
  (* These register bounds and the concrete fetch transition collectively set up
     the hypotheses required by the `transition_FindRule_to_ApplyRule` lemma. *)
  destruct (ThieleUniversal.transition_Fetch_to_FindRule tm ((q, tape), head) cpu0
              Hinv_full Hfetch) as [cpu_find [Hrun_fetch Hpc_find]].
  pose proof (utm_fetch_pc_after_three_steps tm q tape head Hfit) as Hpc_after_fetch.
  rewrite <- Hrun_fetch in Hpc_after_fetch.
  pose proof (utm_fetch_preserves_q tm q tape head Hfit) as Hq_after_fetch.
  rewrite <- Hrun_fetch in Hq_after_fetch.
  simpl in *.
  pose (sym := nth head tape tm.(tm_blank)).
  destruct (find_rule tm.(tm_rules) q sym) as [[[q' write] move]|] eqn:Hfind.
  - destruct (Nat.eqb q tm.(tm_accept) || Nat.eqb q tm.(tm_reject)) eqn:Hhalt.
    + (* TODO: establish that the interpreter halts immediately when the TM
         state is accepting or rejecting. *)
      pose proof (tm_step_halting_state tm q tape head Hhalt) as Htm_step_halt.
      rewrite Htm_step_halt.
    + (* Record the concrete post-fetch program counter so the find-rule
       invariant can be instantiated in a subsequent refinement step. *)
      pose proof Hhalt as Hcontinue.
      rewrite Bool.orb_false_iff in Hcontinue.
      destruct Hcontinue as [Hacc_false Hrej_false].
      apply Bool.not_true_iff_false in Hacc_false.
      apply Bool.not_true_iff_false in Hrej_false.
      pose proof (tm_step_rule_found_continue tm q tape head q' write move
                    Hhalt Hfind) as Htm_step_rule.
      pose proof Hpc_find as Hpc_find_rule.
      unfold ThieleUniversal.IS_FindRule_Start in Hpc_find_rule.
      pose proof (utm_fetch_addr_after_three_steps tm q tape head Hfit)
        as Haddr_after_fetch.
    rewrite <- Hrun_fetch in Haddr_after_fetch.
    destruct (Nat.lt_ge_cases head (length tape)) as [Hhead_lt | Hhead_ge].
    + pose proof (utm_fetch_state_in_bounds tm q tape head Hfit Hhead_lt)
        as [Hq_fetch [Hsym_fetch [Haddr_fetch Hpc_fetch]]].
      rewrite <- Hrun_fetch in Hq_fetch, Hsym_fetch, Haddr_fetch, Hpc_fetch.
      pose proof (utm_fetch_establishes_find_rule_start_inv_in_bounds
                    tm q tape head Hfit Hhead_lt) as Hstart_inv.
      rewrite <- Hrun_fetch in Hstart_inv.
      pose proof (utm_fetch_preserves_program_image tm q tape head Hfit)
        as Hprog_fetch.
      rewrite <- Hrun_fetch in Hprog_fetch.
      pose proof (utm_fetch_preserves_rule_table tm q tape head Hfit)
        as Hrules_fetch.
      rewrite <- Hrun_fetch in Hrules_fetch.
      pose proof (utm_fetch_preserves_tape_window tm q tape head Hfit)
        as Htape_fetch.
      rewrite <- Hrun_fetch in Htape_fetch.
      pose proof (utm_fetch_inv_core tm q tape head Hfit) as Hinv_core_fetch.
      rewrite <- Hrun_fetch in Hinv_core_fetch.
      pose proof (utm_find_rule_start_pc_prefix_step0 tm ((q, tape), head) cpu_find
                    Hinv_core_fetch Hstart_inv) as [Hpc_find_lt Hpc_loop_step0].
      pose proof (utm_run1_preserves_program_image_before_apply
                    cpu_find Hprog_fetch Hpc_find_lt)
        as Hprog_loop_step1.
      pose (cpu_reset := ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4).
      pose proof (utm_fetch_reset_state tm q tape head Hfit)
        as [Haddr_reset_raw [Hq_reset_raw [Hsym_reset_raw Hpc_reset_raw]]].
      change (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4)
        with cpu_reset in Haddr_reset_raw, Hpc_reset_raw.
      rewrite <- Hrun_fetch in Hq_reset_raw, Hsym_reset_raw.
      pose proof (utm_run_n_last_step (utm_cpu_state tm ((q, tape), head)) 3)
        as Hreset_step.
      change (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4)
        with cpu_reset in Hreset_step.
      rewrite <- Hrun_fetch in Hreset_step.
      simpl in Hreset_step.
      (* [Hreset_step] now records that the reset state is a one-step advance
         from [cpu_find], a fact needed when instantiating the rule-search
         bridge in subsequent refinements. *)
      pose proof (utm_fetch_reset_inv_core tm q tape head Hfit)
        as Hinv_core_reset.
      change (ThieleUniversal.run_n (utm_cpu_state tm ((q, tape), head)) 4)
        with cpu_reset in Hinv_core_reset.
      pose proof Haddr_reset_raw as Haddr_reset.
      pose proof Hq_reset_raw as Hq_reset.
      pose proof Hsym_reset_raw as Hsym_reset.
      pose proof Hpc_reset_raw as Hpc_reset.
      pose proof (utm_fetch_establishes_find_rule_loop_inv tm q tape head Hfit Hhead_lt)
        as Hloop0.
      rewrite <- Hrun_fetch in Hloop0.
      pose proof (ThieleUniversal.find_rule_loop_inv_pc_lt_29
                    tm ((q, tape), head) cpu_reset 0 Hloop0)
        as Hpc_loop_lt.
      destruct Hloop0 as [Hloop_q [Hloop_sym [Hloop_addr Hloop_pc]]].
      pose proof (utm_fetch_pc_prefix_lt_4 tm q tape head Hfit)
        as Hpc_prefix_fetch.
      pose proof (utm_find_rule_loop_pc_prefix_step1 tm q tape head Hfit)
        as Hpc_loop_step2.
      rewrite <- Hrun_fetch in Hpc_loop_step2.
      pose proof (utm_find_rule_loop_pc_prefix_step2 tm q tape head Hfit)
        as Hpc_loop_step3.
      rewrite <- Hrun_fetch in Hpc_loop_step3.
      pose proof (utm_find_rule_loop_pc_prefix_step3 tm q tape head Hfit)
        as Hpc_loop_step4.
      rewrite <- Hrun_fetch in Hpc_loop_step4.
      pose proof (utm_find_rule_loop_pc_prefix_step4 tm q tape head Hfit)
        as Hpc_loop_step5.
      rewrite <- Hrun_fetch in Hpc_loop_step5.
      pose proof (utm_find_rule_loop_pc_prefix_base tm q tape head Hfit Hhead_lt)
        as Hpc_loop_base_raw.
      assert (Hpc_loop_base :
                forall j,
                  j <= 2 ->
                  ThieleUniversal.CPU.read_reg ThieleUniversal.CPU.REG_PC
                    (ThieleUniversal.run_n cpu_find j) < 29).
      { intros j Hj.
        specialize (Hpc_loop_base_raw j Hj).
        rewrite <- Hrun_fetch in Hpc_loop_base_raw.
        exact Hpc_loop_base_raw.
      }
      pose proof (utm_pc_prefix_lt_of_le cpu_find 2 Hpc_loop_base)
        as Hpc_loop_prefix_base.
      pose proof (utm_pc_prefix_lt_succ cpu_find 3 Hpc_loop_prefix_base Hpc_loop_step2)
        as Hpc_loop_prefix_step3.
      pose proof (utm_pc_prefix_lt_succ cpu_find 4 Hpc_loop_prefix_step3 Hpc_loop_step4)
        as Hpc_loop_prefix_step4.
      pose proof (utm_pc_prefix_lt_succ cpu_find 5 Hpc_loop_prefix_step4 Hpc_loop_step5)
        as Hpc_loop_prefix_step5.
      pose proof (utm_find_rule_loop_pc_prefix_step5 tm q tape head Hfit Hhead_lt)
        as Hpc_loop_prefix_step6_raw.
      assert (Hpc_loop_prefix_step6 : utm_pc_prefix_lt cpu_find 6).
      { rewrite <- Hrun_fetch. exact Hpc_loop_prefix_step6_raw. }
      pose proof (utm_find_rule_loop_pc_prefix_step7 tm q tape head Hfit Hhead_lt)
        as Hpc_loop_prefix_step7_raw.
      assert (Hpc_loop_prefix_step7 : utm_pc_prefix_lt cpu_find 7).
      { rewrite <- Hrun_fetch. exact Hpc_loop_prefix_step7_raw. }
      (* Record the loop-invariant facts explicitly so later refinements can
         reuse the concrete register and program-counter equalities. *)
      pose proof Hdecode_jz as Hdecode_loop_jz.
      pose proof Hloop_q as Hq_loop.
      pose proof Hloop_sym as Hsym_loop.
      pose proof Hloop_addr as Haddr_loop.
      pose proof Hloop_pc as Hpc_loop.
      destruct (ThieleUniversal.transition_FindRule_to_ApplyRule
                  tm ((q, tape), head) cpu_find q' write move
                  Hinv_core_fetch Hstart_inv Hfind)
        as [k_apply [cpu_apply [Hrun_apply [Hk_apply
          [Hpc_apply [Hq'_apply [Hwrite_apply Hmove_apply]]]]]]].
      pose proof (ThieleUniversal.run_n_add cpu0 3 k_apply)
        as Hrun_apply_from_start.
      simpl in Hrun_apply_from_start.
      rewrite Hrun_fetch in Hrun_apply_from_start.
      rewrite Hrun_apply in Hrun_apply_from_start.
      pose proof Hk_apply as Hk_apply_eq.
      subst k_apply.
      (* The apply phase begins 18 steps after entering the loop, so the
         overall run from the setup state spans 21 instructions. *)
      pose (k_total := 21).
      assert (Hrun_apply_total :
                cpu_apply = ThieleUniversal.run_n cpu0 k_total).
      { subst k_total. exact (eq_sym Hrun_apply_from_start). }
      pose proof Hpc_apply as Hpc_apply_eq.
      unfold ThieleUniversal.IS_ApplyRule_Start in Hpc_apply_eq.
      pose (Happly_regs :=
              fun (Hpc_loop_prefix : utm_pc_prefix_lt cpu_find k_apply) =>
                let Hpc_prefix_total :=
                  utm_pc_prefix_total_from_loop cpu0 cpu_find k_apply
                    Hrun_fetch Hpc_prefix_fetch Hpc_loop_prefix in
                let Hrules_apply_final :=
                  utm_rule_table_preserved_until tm ((q, tape), head) k_total
                    Hfit Hpc_prefix_total in
                utm_apply_phase_registers_from_axioms tm q tape head
                  cpu0 cpu_apply k_total q' write move
                  Hinv_full Hrun_apply_total Hpc_prefix_total
                  Hpc_apply_eq Hrules_apply_final Hfind).
      (* TODO: Strengthen [Hpc_loop_prefix_base] into a full
         [utm_pc_prefix_lt cpu_find k_apply] witness so [Happly_regs]
         can instantiate the apply-phase axioms and extract the loaded
         rule components. *)
    + (* This is the out-of-bounds branch. *)
      pose proof (utm_fetch_state_out_of_bounds tm q tape head Hfit Hhead_ge)
        as [Hq_fetch [Hsym_fetch [Haddr_fetch Hpc_fetch]]].
      rewrite <- Hrun_fetch in Hq_fetch, Hsym_fetch, Haddr_fetch, Hpc_fetch.
      assert (Hsym_blank : sym = tm.(tm_blank)).
      { unfold sym. apply nth_ge_default. exact Hhead_ge. }
      pose proof (utm_fetch_establishes_find_rule_start_inv_out_of_bounds
                    tm q tape head Hfit Hhead_ge) as Hstart_inv.
      rewrite <- Hrun_fetch in Hstart_inv.
      pose proof (utm_fetch_inv_core tm q tape head Hfit) as Hinv_core_fetch.
      rewrite <- Hrun_fetch in Hinv_core_fetch.
    - destruct (Nat.eqb q tm.(tm_accept) || Nat.eqb q tm.(tm_reject)) eqn:Hhalt.
    + (* TODO: show that the interpreter mirrors the TM’s immediate halt when
         no rule applies and the state is accepting or rejecting. *)
      pose proof (tm_step_halting_state tm q tape head Hhalt) as Htm_step_halt.
      rewrite Htm_step_halt.
    + pose proof Hhalt as Hcontinue.
      rewrite Bool.orb_false_iff in Hcontinue.
      destruct Hcontinue as [Hacc_false Hrej_false].
      apply Bool.not_true_iff_false in Hacc_false.
      apply Bool.not_true_iff_false in Hrej_false.
      pose proof (tm_step_no_rule_continue tm q tape head Hhalt Hfind)
        as Htm_step_halt.
      rewrite Htm_step_halt.
      pose proof (utm_fetch_inv_core tm q tape head Hfit) as Hinv_core_fetch.
      rewrite <- Hrun_fetch in Hinv_core_fetch.
      destruct (Nat.lt_ge_cases head (length tape)) as [Hhead_lt | Hhead_ge].
      * pose proof (utm_fetch_establishes_find_rule_start_inv_in_bounds
                      tm q tape head Hfit Hhead_lt) as Hstart_inv.
        rewrite <- Hrun_fetch in Hstart_inv.
        apply (utm_interpreter_no_rule_found_halts tm ((q, tape), head)
                  cpu_find Hfind Hinv_core_fetch Hstart_inv Hfit).
      * pose proof (utm_fetch_establishes_find_rule_start_inv_out_of_bounds
                      tm q tape head Hfit Hhead_ge) as Hstart_inv.
        rewrite <- Hrun_fetch in Hstart_inv.
        apply (utm_interpreter_no_rule_found_halts tm ((q, tape), head)
                  cpu_find Hfind Hinv_core_fetch Hstart_inv Hfit).
Admitted.

Lemma utm_simulation_steps_axiom :
  forall tm conf k,
    config_ok tm conf ->
    rules_fit tm ->
    decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
    = tm_step_n tm conf k.
Proof.
  (* Multi-step simulation will follow from the one-step bridge once the
     strengthened invariant is available for each step. *)
Admitted.

Definition utm_obligations (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  (Hfit : rules_fit tm)
  : InterpreterObligations tm :=
  interpreter_obligations_from_catalogue_witness tm
    (utm_step_catalogue_witness tm Hcat Hfit)
    (fun conf Hok => utm_simulate_one_step tm conf Hok Hfit)
    (fun conf k Hok => utm_simulation_steps_axiom tm conf k Hok Hfit).

Definition tm_step_preserves_ok :
  forall tm,
    catalogue_static_check tm = true ->
    rules_fit tm ->
    forall conf,
      config_ok tm conf -> config_ok tm (tm_step tm conf) :=
  fun tm Hcat Hfit => interpreter_preserves_ok tm (utm_obligations tm Hcat Hfit).

Definition simulate_one_step :
  forall tm,
    catalogue_static_check tm = true ->
    rules_fit tm ->
    forall conf,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) 1)
      = tm_step tm conf :=
  fun tm Hcat Hfit => interpreter_simulate_one_step tm (utm_obligations tm Hcat Hfit).

Definition utm_simulation_steps :
  forall tm,
    catalogue_static_check tm = true ->
    rules_fit tm ->
    forall conf k,
      config_ok tm conf ->
      decode_state tm (thiele_step_n utm_program (encode_config tm conf) k)
      = tm_step_n tm conf k :=
  fun tm Hcat Hfit => interpreter_simulation_steps tm (utm_obligations tm Hcat Hfit).

(* ----------------------------------------------------------------- *)
(* Packaging containment as a reusable witness.                       *)
(* ----------------------------------------------------------------- *)

Record SimulationWitness := {
  witness_tm : TM;
  witness_catalogue_ok : catalogue_static_check witness_tm = true;
  witness_prog : Prog;
  witness_encode : TMConfig -> State;
  witness_decode : State -> TMConfig;
  witness_roundtrip : forall conf,
      config_ok witness_tm conf ->
      witness_decode (witness_encode conf) = conf;
  witness_correct : forall conf k,
      config_ok witness_tm conf ->
      witness_decode (thiele_step_n witness_prog (witness_encode conf) k)
      = tm_step_n witness_tm conf k
}.

Definition build_witness (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  (Hfit : rules_fit tm)
  : SimulationWitness :=
  {| witness_tm := tm;
     witness_catalogue_ok := Hcat;
     witness_prog := utm_program;
     witness_encode := encode_config tm;
     witness_decode := decode_state tm;
     witness_roundtrip := decode_encode_id tm;
     witness_correct := utm_simulation_steps tm Hcat Hfit |}.

Lemma build_witness_ok :
  forall tm (Hcat : catalogue_static_check tm = true) (Hfit : rules_fit tm),
    let wit := build_witness tm Hcat Hfit in
    (forall conf (Hok : config_ok tm conf),
        witness_roundtrip wit conf Hok = decode_encode_id tm conf Hok) /\
    (forall conf k (Hok : config_ok tm conf),
        witness_decode wit (thiele_step_n (witness_prog wit)
                                          (witness_encode wit conf) k)
        = tm_step_n tm conf k).
Proof.
  intros tm Hcat Hfit.
  unfold build_witness.
  split.
  - intros conf Hok. reflexivity.
  - intros conf k Hok. exact (utm_simulation_steps tm Hcat Hfit conf k Hok).
Qed.

Definition thiele_simulates_tm (tm : TM)
  (Hcat : catalogue_static_check tm = true)
  (Hfit : rules_fit tm) : Prop :=
  let wit := build_witness tm Hcat Hfit in
  (forall conf k,
      config_ok tm conf ->
      witness_decode wit (thiele_step_n (witness_prog wit)
                                        (witness_encode wit conf) k)
      = tm_step_n (witness_tm wit) conf k).

Theorem turing_contained_in_thiele :
  forall tm (Hcat : catalogue_static_check tm = true) (Hfit : rules_fit tm),
    thiele_simulates_tm tm Hcat Hfit.
Proof.
  intros tm Hcat Hfit.
  unfold thiele_simulates_tm.
  destruct (build_witness_ok tm Hcat Hfit) as [_ Hsim].
  intros conf k Hok.
  exact (Hsim conf k Hok).
Qed.

Corollary utm_simulation :
  thiele_simulates_tm utm_tm utm_catalogue_static_check rules_fit_utm.
Proof.
  apply turing_contained_in_thiele.
Qed.

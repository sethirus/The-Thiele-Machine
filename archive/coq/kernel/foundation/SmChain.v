(** SmChain.v: the replay program, run gadget by gadget.

    The program has thirteen pieces, laid one after the other. Its registers:

      1, 2                 the inputs x and c
      base_k .. (k = 0..4) five windows, one for each of five MMA blocks
                           (SmBlock.v); block k computes a number m_k from x
                           and c and leaves it in register base_k
      z, rs, rd            a jump register, a slot register that will hold 1,
                           and a register that is never written

    The pieces:

      g1   fan x into register base_k + 1 for every k   (SmLoops2.v)
      g2   fan c into register base_k + 2 for every k
      g3-g7   the five blocks
      g8   INC rs
      g9   CHECK PSlot rs, m_1 times
      g10  COMMIT PSlot rs, m_2 times
      g11  CERTIFY, m_3 times
      g12  move m_0 into register 0
      g13  if m_4 is positive, CHECK PSlot rd, which traps

    [sm2_setup] runs g1 .. g7. [sm2_setup_stuck]: if block 0 computes
    nothing, the program never stops during that part. [sm2_replay] runs
    g8 .. g13 and describes the final state: register 0 holds m_0, the
    ledger is m_1 + m_2 + m_3 + m_4, the fact table has m_1 entries, the
    channel is empty exactly when m_2 = 0, the flag is up exactly when
    m_3 >= 1, and the latch is up exactly when m_4 = 1.

    Everything here is stated for any program Q that holds the pieces at
    the stated lines. SmFixed.v builds the program and shows it does.

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v,
    SmHostBlocks.v, SmCodes.v, SmLoops.v, SmLoops2.v, SmLoops3.v,
    SmMMAOff.v, SmBlock.v, SmKleene.v. No axioms and no unfinished proofs. *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the host machine, here the fans, blocks and payments of the replay program, over the host machine of EarnedMulti.v.
   The host machine's link to the abstract record (a CertificationSystem
   with the trace floor, a Thiele-complete machine, and the halting problem
   of U) lives in UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Minimal.SmHostBlocks Minimal.SmCodes Minimal.SmLoops Minimal.SmLoops2 Minimal.SmLoops3 Kernel.SmMMAOff
  Kernel.SmBlock Kernel.SmKleene.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).
Local Notation hstep := (M.step UC.hprop_eqb UC.heval).

Lemma sm2_in2_big : forall x c q, 3 <= q -> sm_in2 x c q = 0.
Proof.
  intros x c q Hq. unfold sm_in2.
  replace (Nat.eqb q 1) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb q 2) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Section Chain.

Variables (R0 R1 R2 R3 R4 : nat -> nat -> nat -> Prop).
Variable b0 : sm2_bint R0.
Variable b1 : sm2_bint R1.
Variable b2 : sm2_bint R2.
Variable b3 : sm2_bint R3.
Variable b4 : sm2_bint R4.

Variables (base0 base1 base2 base3 base4 z rs rd : nat).
Hypothesis Hbase0 : base0 = 3.
Hypothesis Hbase1 : base1 = base0 + sm2_bi_N b0.
Hypothesis Hbase2 : base2 = base1 + sm2_bi_N b1.
Hypothesis Hbase3 : base3 = base2 + sm2_bi_N b2.
Hypothesis Hbase4 : base4 = base3 + sm2_bi_N b3.
Hypothesis Hz : z = base4 + sm2_bi_N b4.
Hypothesis Hrs : rs = z + 1.
Hypothesis Hrd : rd = z + 2.

Variables (o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 o13 : nat).
Hypothesis Ho2 : o2 = o1 + 10.
Hypothesis Ho3 : o3 = o2 + 10.
Hypothesis Ho4 : o4 = o3 + sm2_bi_len b0.
Hypothesis Ho5 : o5 = o4 + sm2_bi_len b1.
Hypothesis Ho6 : o6 = o5 + sm2_bi_len b2.
Hypothesis Ho7 : o7 = o6 + sm2_bi_len b3.
Hypothesis Ho8 : o8 = o7 + sm2_bi_len b4.
Hypothesis Ho9 : o9 = o8 + 1.
Hypothesis Ho10 : o10 = o9 + 6.
Hypothesis Ho11 : o11 = o10 + 6.
Hypothesis Ho12 : o12 = o11 + 6.
Hypothesis Ho13 : o13 = o12 + 6.

Variable Q : list hinstr.

Definition sm2_dsx : list nat := [base0 + 1; base1 + 1; base2 + 1; base3 + 1; base4 + 1].
Definition sm2_dsc : list nat := [base0 + 2; base1 + 2; base2 + 2; base3 + 2; base4 + 2].

Hypothesis Hq1 : sm2_inQ Q o1 (sm2_fan o1 1 z sm2_dsx).
Hypothesis Hq2 : sm2_inQ Q o2 (sm2_fan o2 2 z sm2_dsc).
Hypothesis Hqb0 : sm_embeds Q (sm2_bi_prog b0 base0) o3.
Hypothesis Hqb1 : sm_embeds Q (sm2_bi_prog b1 base1) o4.
Hypothesis Hqb2 : sm_embeds Q (sm2_bi_prog b2 base2) o5.
Hypothesis Hqb3 : sm_embeds Q (sm2_bi_prog b3 base3) o6.
Hypothesis Hqb4 : sm_embeds Q (sm2_bi_prog b4 base4) o7.
Hypothesis Hq8 : M.fetch Q (o8 + 1) = Some (M.INC rs).
Hypothesis Hq9 : sm2_inQ Q o9 (sm2_whilel o9 base1 z [M.CHECK UC.PSlot rs]).
Hypothesis Hq10 : sm2_inQ Q o10 (sm2_whilel o10 base2 z [M.COMMIT UC.PSlot rs]).
Hypothesis Hq11 : sm2_inQ Q o11 (sm2_whilel o11 base3 z [M.CERTIFY]).
Hypothesis Hq12 : sm2_inQ Q o12 (sm2_fan o12 base0 z [0]).
Hypothesis Hq13 : sm2_inQ Q o13 (sm2_trapg o13 base4 z rd).
Hypothesis HlenQ : length Q = o13 + 4.

Lemma sm2_N3 : 3 <= sm2_bi_N b0 /\ 3 <= sm2_bi_N b1 /\ 3 <= sm2_bi_N b2 /\ 3 <= sm2_bi_N b3 /\ 3 <= sm2_bi_N b4.
Proof.
  refine (conj (sm2_bi_N3 b0) (conj (sm2_bi_N3 b1) (conj (sm2_bi_N3 b2) (conj (sm2_bi_N3 b3) (sm2_bi_N3 b4))))).
Qed.

(* ================================================================= *)
(* The two fans put x and c into the windows.                         *)
(* ================================================================= *)

Lemma sm2_dsx_nodup : NoDup sm2_dsx.
Proof.
  destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  unfold sm2_dsx. repeat constructor; simpl; intuition lia.
Qed.

Lemma sm2_dsc_nodup : NoDup sm2_dsc.
Proof.
  destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  unfold sm2_dsc. repeat constructor; simpl; intuition lia.
Qed.

Lemma sm2_dsx_notin : forall q, (q < 3 \/ base4 + 3 <= q) -> ~ In q sm2_dsx.
Proof.
  intros q Hq. destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  unfold sm2_dsx. simpl. intros H. intuition lia.
Qed.

Lemma sm2_dsc_notin : forall q, (q < 3 \/ base4 + 3 <= q) -> ~ In q sm2_dsc.
Proof.
  intros q Hq. destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  unfold sm2_dsc. simpl. intros H. intuition lia.
Qed.

Lemma sm2_win_count : forall bk Nk j,
  ((bk = base0 /\ Nk = sm2_bi_N b0) \/ (bk = base1 /\ Nk = sm2_bi_N b1) \/ (bk = base2 /\ Nk = sm2_bi_N b2) \/
   (bk = base3 /\ Nk = sm2_bi_N b3) \/ (bk = base4 /\ Nk = sm2_bi_N b4)) -> j < Nk ->
  count_occ Nat.eq_dec sm2_dsx (bk + j) = (if Nat.eqb j 1 then 1 else 0) /\
  count_occ Nat.eq_dec sm2_dsc (bk + j) = (if Nat.eqb j 2 then 1 else 0).
Proof.
  intros bk Nk j Hbk Hj. destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  split.
  - destruct (Nat.eqb_spec j 1) as [-> | Hj1].
    + apply (proj1 (NoDup_count_occ' Nat.eq_dec sm2_dsx) sm2_dsx_nodup). unfold sm2_dsx. simpl. lia.
    + apply count_occ_not_In. unfold sm2_dsx. simpl. intros H. intuition lia.
  - destruct (Nat.eqb_spec j 2) as [-> | Hj2].
    + apply (proj1 (NoDup_count_occ' Nat.eq_dec sm2_dsc) sm2_dsc_nodup). unfold sm2_dsc. simpl. lia.
    + apply count_occ_not_In. unfold sm2_dsc. simpl. intros H. intuition lia.
Qed.

(* After the two fans every window holds the start vector of its block. *)
Lemma sm2_fans : forall x c (u : hstate),
  M.pc (M.core_of u) = o1 + 1 -> M.err (M.core_of u) = false ->
  (forall q, M.vals (M.core_of u) q = sm_in2 x c q) ->
  exists u', sm2_RR Q u u' /\ M.pc (M.core_of u') = o3 + 1 /\ M.err (M.core_of u') = false /\
    (forall q, 3 <= q ->
       M.vals (M.core_of u') q = x * count_occ Nat.eq_dec sm2_dsx q + c * count_occ Nat.eq_dec sm2_dsc q) /\
    M.vals (M.core_of u') 0 = 0 /\
    sm2_pfe u u'.
Proof.
  intros x c u Hp He Hv. destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  assert (Hzx : ~ In z sm2_dsx) by (apply sm2_dsx_notin; lia).
  assert (Hzc : ~ In z sm2_dsc) by (apply sm2_dsc_notin; lia).
  assert (H1x : ~ In 1 sm2_dsx) by (apply sm2_dsx_notin; lia).
  assert (H2x : ~ In 2 sm2_dsx) by (apply sm2_dsx_notin; lia).
  assert (H1c : ~ In 1 sm2_dsc) by (apply sm2_dsc_notin; lia).
  assert (H2c : ~ In 2 sm2_dsc) by (apply sm2_dsc_notin; lia).
  assert (Hv1 : M.vals (M.core_of u) 1 = x) by (rewrite Hv; unfold sm_in2; reflexivity).
  destruct (sm2_fan_spec Q o1 1 z sm2_dsx Hq1 ltac:(lia) H1x Hzx x u Hp He Hv1)
    as (uA & RA & PA & EA & VA1 & VAz & VA & WA & PFA).
  assert (Hlx : length sm2_dsx = 5) by reflexivity.
  assert (Hlc : length sm2_dsc = 5) by reflexivity.
  assert (Hv2 : M.vals (M.core_of uA) 2 = c).
  { rewrite (VA 2 ltac:(lia)), Hv, (sm2_count_nil _ _ H2x). unfold sm_in2. simpl. lia. }
  destruct (sm2_fan_spec Q o2 2 z sm2_dsc Hq2 ltac:(lia) H2c Hzc c uA ltac:(rewrite PA, Hlx; lia) EA Hv2)
    as (uB & RB & PB & EB & VB2 & VBz & VB & WB & PFB).
  exists uB. refine (conj _ (conj _ (conj EB (conj _ (conj _ _))))).
  - eapply sm2_RR_trans; [exact RA | exact RB].
  - rewrite PB, Hlc. lia.
  - intros q Hq. destruct (Nat.eq_dec q 2) as [-> | Hq2'].
    + lia.
    + rewrite (VB q Hq2'). destruct (Nat.eq_dec q 1) as [-> | Hq1'].
      * lia.
      * rewrite (VA q Hq1'). rewrite Hv, sm2_in2_big by exact Hq. lia.
  - rewrite (VB 0 ltac:(lia)), (VA 0 ltac:(lia)), Hv.
    rewrite (sm2_count_nil sm2_dsx 0 ltac:(apply sm2_dsx_notin; lia)).
    rewrite (sm2_count_nil sm2_dsc 0 ltac:(apply sm2_dsc_notin; lia)). unfold sm_in2. simpl. lia.
  - eapply sm2_pfe_trans; [exact PFA | exact PFB].
Qed.

Definition sm2_isbase (bk Nk : nat) : Prop :=
  (bk = base0 /\ Nk = sm2_bi_N b0) \/ (bk = base1 /\ Nk = sm2_bi_N b1) \/ (bk = base2 /\ Nk = sm2_bi_N b2) \/
  (bk = base3 /\ Nk = sm2_bi_N b3) \/ (bk = base4 /\ Nk = sm2_bi_N b4).

Lemma sm2_win_vals : forall x c (uB : hstate),
  (forall q, 3 <= q ->
     M.vals (M.core_of uB) q = x * count_occ Nat.eq_dec sm2_dsx q + c * count_occ Nat.eq_dec sm2_dsc q) ->
  forall bk Nk j, sm2_isbase bk Nk -> j < Nk -> M.vals (M.core_of uB) (bk + j) = sm_in2 x c j.
Proof.
  intros x c uB HB bk Nk j Hbk Hj. destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  assert (Hge : 3 <= bk + j) by (unfold sm2_isbase in Hbk; lia).
  rewrite (HB _ Hge). destruct (sm2_win_count bk Nk j Hbk Hj) as [Cx Cc]. rewrite Cx, Cc.
  unfold sm_in2. destruct (Nat.eqb_spec j 1), (Nat.eqb_spec j 2); simpl; lia.
Qed.

Lemma sm2_setup : forall x c m0 m1 m2 m3 m4 (u : hstate),
  R0 x c m0 -> R1 x c m1 -> R2 x c m2 -> R3 x c m3 -> R4 x c m4 ->
  M.pc (M.core_of u) = o1 + 1 -> M.err (M.core_of u) = false ->
  (forall q, M.vals (M.core_of u) q = sm_in2 x c q) ->
  exists u', sm2_RR Q u u' /\ M.pc (M.core_of u') = o8 + 1 /\ M.err (M.core_of u') = false /\
    M.vals (M.core_of u') base0 = m0 /\ M.vals (M.core_of u') base1 = m1 /\
    M.vals (M.core_of u') base2 = m2 /\ M.vals (M.core_of u') base3 = m3 /\
    M.vals (M.core_of u') base4 = m4 /\
    M.vals (M.core_of u') rs = 0 /\ M.vals (M.core_of u') rd = 0 /\ M.vals (M.core_of u') 0 = 0 /\
    sm2_pfe u u'.
Proof.
  intros x c m0 m1 m2 m3 m4 u HR0 HR1 HR2 HR3 HR4 Hp He Hv.
  destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  destruct (sm2_fans x c u Hp He Hv) as (uB & RB & PB & EB & VB & V0B & PFB).
  assert (W : forall bk Nk j, sm2_isbase bk Nk -> j < Nk -> M.vals (M.core_of uB) (bk + j) = sm_in2 x c j)
    by (apply sm2_win_vals; exact VB).
  assert (Wb0 : forall j, j < sm2_bi_N b0 -> M.vals (M.core_of uB) (base0 + j) = sm_in2 x c j)
    by (intros j Hj; apply (W base0 (sm2_bi_N b0) j); [unfold sm2_isbase; lia | exact Hj]).
  destruct (sm2_bi_ctx b0 base0 o3 Q uB x c m0 Hqb0 ltac:(lia) EB Wb0 HR0)
    as (u1 & RR0 & P0 & E0 & Vb0 & F0 & PF0).
  assert (Wc1 : forall j, j < sm2_bi_N b1 -> M.vals (M.core_of u1) (base1 + j) = sm_in2 x c j).
  { intros j Hj. rewrite (proj1 (F0 (base1 + j) ltac:(lia))). apply (W base1 (sm2_bi_N b1) j); [unfold sm2_isbase; lia | exact Hj]. }
  destruct (sm2_bi_ctx b1 base1 o4 Q u1 x c m1 Hqb1 ltac:(lia) E0 Wc1 HR1)
    as (u2 & RR1 & P1 & E1 & Vb1 & F1 & PF1).
  assert (Wc2 : forall j, j < sm2_bi_N b2 -> M.vals (M.core_of u2) (base2 + j) = sm_in2 x c j).
  { intros j Hj. rewrite (proj1 (F1 (base2 + j) ltac:(lia))), (proj1 (F0 (base2 + j) ltac:(lia))). apply (W base2 (sm2_bi_N b2) j); [unfold sm2_isbase; lia | exact Hj]. }
  destruct (sm2_bi_ctx b2 base2 o5 Q u2 x c m2 Hqb2 ltac:(lia) E1 Wc2 HR2)
    as (u3 & RR2 & P2 & E2 & Vb2 & F2 & PF2).
  assert (Wc3 : forall j, j < sm2_bi_N b3 -> M.vals (M.core_of u3) (base3 + j) = sm_in2 x c j).
  { intros j Hj. rewrite (proj1 (F2 (base3 + j) ltac:(lia))), (proj1 (F1 (base3 + j) ltac:(lia))), (proj1 (F0 (base3 + j) ltac:(lia))). apply (W base3 (sm2_bi_N b3) j); [unfold sm2_isbase; lia | exact Hj]. }
  destruct (sm2_bi_ctx b3 base3 o6 Q u3 x c m3 Hqb3 ltac:(lia) E2 Wc3 HR3)
    as (u4 & RR3 & P3 & E3 & Vb3 & F3 & PF3).
  assert (Wc4 : forall j, j < sm2_bi_N b4 -> M.vals (M.core_of u4) (base4 + j) = sm_in2 x c j).
  { intros j Hj. rewrite (proj1 (F3 (base4 + j) ltac:(lia))), (proj1 (F2 (base4 + j) ltac:(lia))), (proj1 (F1 (base4 + j) ltac:(lia))), (proj1 (F0 (base4 + j) ltac:(lia))). apply (W base4 (sm2_bi_N b4) j); [unfold sm2_isbase; lia | exact Hj]. }
  destruct (sm2_bi_ctx b4 base4 o7 Q u4 x c m4 Hqb4 ltac:(lia) E3 Wc4 HR4)
    as (u5 & RR4 & P4 & E4 & Vb4 & F4 & PF4).
  exists u5. refine (conj _ (conj _ (conj E4 _))).
  - eapply sm2_RR_trans; [exact RB |]. eapply sm2_RR_trans; [exact RR0 |]. eapply sm2_RR_trans; [exact RR1 |].
    eapply sm2_RR_trans; [exact RR2 |]. eapply sm2_RR_trans; [exact RR3 |]. exact RR4.
  - rewrite P4. lia.
  - assert (Vrs : M.vals (M.core_of u5) rs = 0 /\ M.vals (M.core_of u5) rd = 0 /\ M.vals (M.core_of u5) 0 = 0).
    { rewrite (proj1 (F4 rs ltac:(lia))), (proj1 (F3 rs ltac:(lia))), (proj1 (F2 rs ltac:(lia))),
        (proj1 (F1 rs ltac:(lia))), (proj1 (F0 rs ltac:(lia))).
      rewrite (proj1 (F4 rd ltac:(lia))), (proj1 (F3 rd ltac:(lia))), (proj1 (F2 rd ltac:(lia))),
        (proj1 (F1 rd ltac:(lia))), (proj1 (F0 rd ltac:(lia))).
      rewrite (proj1 (F4 0 ltac:(lia))), (proj1 (F3 0 ltac:(lia))), (proj1 (F2 0 ltac:(lia))),
        (proj1 (F1 0 ltac:(lia))), (proj1 (F0 0 ltac:(lia))).
      rewrite (VB rs ltac:(lia)), (VB rd ltac:(lia)), V0B.
      rewrite (sm2_count_nil sm2_dsx rs ltac:(apply sm2_dsx_notin; lia)),
              (sm2_count_nil sm2_dsc rs ltac:(apply sm2_dsc_notin; lia)),
              (sm2_count_nil sm2_dsx rd ltac:(apply sm2_dsx_notin; lia)),
              (sm2_count_nil sm2_dsc rd ltac:(apply sm2_dsc_notin; lia)).
      repeat split; lia. }
  destruct Vrs as (Vrs & Vrd & Vr0).
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj Vrs (conj Vrd (conj Vr0 _)))))))).
  + rewrite (proj1 (F4 base0 ltac:(lia))), (proj1 (F3 base0 ltac:(lia))), (proj1 (F2 base0 ltac:(lia))),
      (proj1 (F1 base0 ltac:(lia))). exact Vb0.
  + rewrite (proj1 (F4 base1 ltac:(lia))), (proj1 (F3 base1 ltac:(lia))), (proj1 (F2 base1 ltac:(lia))). exact Vb1.
  + rewrite (proj1 (F4 base2 ltac:(lia))), (proj1 (F3 base2 ltac:(lia))). exact Vb2.
  + rewrite (proj1 (F4 base3 ltac:(lia))). exact Vb3.
  + exact Vb4.
  + eapply sm2_pfe_trans; [exact PFB |]. eapply sm2_pfe_trans; [exact PF0 |].
    eapply sm2_pfe_trans; [exact PF1 |]. eapply sm2_pfe_trans; [exact PF2 |].
    eapply sm2_pfe_trans; [exact PF3 | exact PF4].
Qed.

Lemma sm2_setup_halt : forall x c (u : hstate),
  M.pc (M.core_of u) = o1 + 1 -> M.err (M.core_of u) = false ->
  (forall q, M.vals (M.core_of u) q = sm_in2 x c q) ->
  forall n, M.next_instr Q (M.core_of (hrun_prog n Q u)) = None -> exists m, R0 x c m.
Proof.
  intros x c u Hp He Hv n Hn.
  destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  destruct (sm2_fans x c u Hp He Hv) as (uB & RB & PB & EB & VB & V0B & PFB).
  assert (W : forall bk Nk j, sm2_isbase bk Nk -> j < Nk -> M.vals (M.core_of uB) (bk + j) = sm_in2 x c j)
    by (apply sm2_win_vals; exact VB).
  assert (Wb0 : forall j, j < sm2_bi_N b0 -> M.vals (M.core_of uB) (base0 + j) = sm_in2 x c j)
    by (intros j Hj; apply (W base0 (sm2_bi_N b0) j); [unfold sm2_isbase; lia | exact Hj]).
  destruct (sm2_RR_steps Q u uB RB) as (N & Hrun & Hall).
  destruct (le_lt_dec N n) as [Hle | Hlt].
  - replace n with (N + (n - N)) in Hn by lia.
    rewrite (sm_run_add UC.hprop_eqb UC.heval N (n - N) Q u), Hrun in Hn.
    exact (sm2_bi_halt b0 base0 o3 Q uB x c Hqb0 ltac:(lia) EB Wb0 (n - N) Hn).
  - exfalso. exact (Hall n Hlt Hn).
Qed.

Lemma sm2_heval1 : UC.heval UC.PSlot 1 = true.
Proof. reflexivity. Qed.

Lemma sm2_repeat_in : forall (A : Type) (a : A) n (l : list A), 1 <= n -> In a (repeat a n ++ l).
Proof. intros A a n l Hn. destruct n as [| n]; [lia |]. simpl. left. reflexivity. Qed.

Lemma sm2_fetch_end : forall (Q' : list hinstr) (n : nat), length Q' < n -> M.fetch Q' n = None.
Proof.
  intros Q' n H. destruct n as [| n]; [lia |]. simpl. apply nth_error_None. lia.
Qed.

Lemma sm2_replay : forall (u : hstate) out nf bc cc fe,
  M.pc (M.core_of u) = o8 + 1 -> M.err (M.core_of u) = false ->
  M.vals (M.core_of u) base0 = out -> M.vals (M.core_of u) base1 = nf ->
  M.vals (M.core_of u) base2 = bc -> M.vals (M.core_of u) base3 = cc ->
  M.vals (M.core_of u) base4 = fe ->
  M.vals (M.core_of u) rs = 0 -> M.vals (M.core_of u) rd = 0 -> M.vals (M.core_of u) 0 = 0 ->
  M.facts (M.core_of u) = [] -> M.chan (M.core_of u) = None ->
  M.mu u = 0 -> M.cert u = false ->
  nf <= 16 -> fe <= 1 -> (1 <= bc -> 1 <= nf) -> (1 <= cc -> 1 <= bc) ->
  exists u', sm2_RR Q u u' /\ M.halted Q (M.core_of u') /\
    M.vals (M.core_of u') 0 = out /\ (M.err (M.core_of u') = true <-> fe = 1) /\
    M.mu u' = nf + bc + cc + fe /\ (M.cert u' = true <-> 1 <= cc) /\
    length (M.facts (M.core_of u')) = nf /\ (M.chan (M.core_of u') = None <-> bc = 0).
Proof.
  intros u out nf bc cc fe Hp He Hv0 Hv1 Hv2 Hv3 Hv4 Hrs0 Hrd0 Hr00 Hf0 Hc0 Hmu0 Hce0 Hnf Hfe Hbn Hcb.
  destruct sm2_N3 as (N0 & N1 & N2 & N3 & N4).
  (* the slot register gets 1 *)
  assert (F8 : M.fetch Q (M.pc (M.core_of u)) = Some (M.INC rs)) by (rewrite Hp; exact Hq8).
  destruct (sm2_step_inc Q u rs He F8) as (N8 & P8 & V8 & W8 & E8).
  set (u1 := hstep Q u) in *.
  assert (He1 : M.err (M.core_of u1) = false) by (destruct E8 as (_ & _ & C & _); rewrite <- C; exact He).
  assert (Hrs1 : M.vals (M.core_of u1) rs = 1) by (rewrite V8, Nat.eqb_refl, Hrs0; reflexivity).
  assert (Hv1' : forall q, q <> rs -> M.vals (M.core_of u1) q = M.vals (M.core_of u) q)
    by (intros q Hq; rewrite V8; destruct (Nat.eqb_spec q rs); [congruence | reflexivity]).
  (* the check loop *)
  destruct (sm2_check_loop Q o9 base1 z rs Hq9 ltac:(lia) ltac:(lia) ltac:(lia) nf u1
              ltac:(rewrite P8, Hp; lia) He1 ltac:(rewrite Hv1' by lia; exact Hv1)
              ltac:(rewrite Hrs1; exact sm2_heval1)
              ltac:(destruct E8 as (Ef & _); rewrite <- Ef, Hf0; simpl; lia))
    as (u2 & RC2 & P2 & E2 & Vb1 & Vz2 & V2 & W2 & Fa2 & C2 & Mu2 & Ce2).
  assert (Hf2 : M.facts (M.core_of u2) = repeat (M.mkfact UC.PSlot rs (M.vers (M.core_of u1) rs)) nf).
  { rewrite Fa2. destruct E8 as (Ef & _). rewrite <- Ef, Hf0. rewrite app_nil_r. reflexivity. }
  assert (Hw2rs : M.vers (M.core_of u2) rs = M.vers (M.core_of u1) rs) by (apply W2; lia).
  (* the commit loop *)
  destruct (sm2_commit_loop Q o10 base2 z rs Hq10 ltac:(lia) ltac:(lia) ltac:(lia) bc u2
              ltac:(rewrite P2; lia) E2 ltac:(rewrite V2 by lia; rewrite Hv1' by lia; exact Hv2)
              ltac:(intro Hb; rewrite Hf2, Hw2rs; rewrite <- (app_nil_r (repeat _ nf));
                    apply sm2_repeat_in; exact (Hbn Hb)))
    as (u3 & RC3 & P3 & E3 & Vb2 & Vz3 & V3 & W3 & Fa3 & Cn3 & Cs3 & Mu3 & Ce3).
  assert (Hf3 : M.facts (M.core_of u3) = repeat (M.mkfact UC.PSlot rs (M.vers (M.core_of u1) rs)) nf)
    by (rewrite Fa3; exact Hf2).
  assert (Hchan1 : M.chan (M.core_of u2) = None).
  { rewrite C2. destruct E8 as (_ & Ec & _). rewrite <- Ec. exact Hc0. }
  (* the certify loop *)
  destruct (sm2_certify_loop Q o11 base3 z Hq11 ltac:(lia) cc u3
              ltac:(rewrite P3; lia) E3 ltac:(rewrite V3 by lia; rewrite V2 by lia; rewrite Hv1' by lia; exact Hv3)
              ltac:(intro Hc1; rewrite (Cs3 (Hcb Hc1)); intro Hx; discriminate Hx))
    as (u4 & RC4 & P4 & E4 & Vb3 & Vz4 & V4 & W4 & Fa4 & Cn4 & Mu4 & Ce40 & Ce41).
  (* the result goes to register 0 *)
  assert (Hv0_4 : M.vals (M.core_of u4) base0 = out).
  { rewrite V4 by lia. rewrite V3 by lia. rewrite V2 by lia. rewrite Hv1' by lia. exact Hv0. }
  assert (Hr0_4 : M.vals (M.core_of u4) 0 = 0).
  { rewrite V4 by lia. rewrite V3 by lia. rewrite V2 by lia. rewrite Hv1' by lia. exact Hr00. }
  destruct (sm2_fan_spec Q o12 base0 z [0] Hq12 ltac:(lia) ltac:(simpl; lia) ltac:(simpl; lia) out u4
              ltac:(rewrite P4; lia) E4 Hv0_4)
    as (u5 & RC5 & P5 & E5 & Vb0 & Vz5 & V5 & W5 & PF5).
  assert (Hc4 : count_occ Nat.eq_dec [0] base4 = 0) by (apply sm2_count_nil; simpl; intros [H | H]; lia).
  assert (Hcd : count_occ Nat.eq_dec [0] rd = 0) by (apply sm2_count_nil; simpl; intros [H | H]; lia).
  assert (Hc00 : count_occ Nat.eq_dec [0] 0 = 1) by reflexivity.
  assert (Hv4_5 : M.vals (M.core_of u5) base4 = fe).
  { rewrite (V5 base4 ltac:(lia)), Hc4. rewrite Nat.mul_0_r, Nat.add_0_r.
    rewrite V4 by lia. rewrite V3 by lia. rewrite V2 by lia. rewrite Hv1' by lia. exact Hv4. }
  assert (Hrd_5 : M.vals (M.core_of u5) rd = 0).
  { rewrite (V5 rd ltac:(lia)), Hcd. rewrite Nat.mul_0_r, Nat.add_0_r.
    rewrite V4 by lia. rewrite V3 by lia. rewrite V2 by lia. rewrite Hv1' by lia. exact Hrd0. }
  assert (Hv05 : M.vals (M.core_of u5) 0 = out).
  { rewrite (V5 0 ltac:(lia)), Hc00, Hr0_4. lia. }
  destruct PF5 as (Pf5 & Pc5 & Pe5 & Pm5 & Pk5).
  assert (Hf5 : M.facts (M.core_of u5) = repeat (M.mkfact UC.PSlot rs (M.vers (M.core_of u1) rs)) nf)
    by (rewrite <- Pf5, Fa4; exact Hf3).
  assert (Hlenf : length (M.facts (M.core_of u5)) = nf) by (rewrite Hf5, repeat_length; reflexivity).
  assert (HchanT : (M.chan (M.core_of u5) = None <-> bc = 0)).
  { rewrite <- Pc5, Cn4. destruct (Nat.eq_dec bc 0) as [Hb0 | Hb0].
    - rewrite (Cn3 Hb0). split; [intros _; exact Hb0 | intros _; exact Hchan1].
    - rewrite (Cs3 ltac:(lia)). split; [intro Hx; discriminate Hx | intro; lia]. }
  assert (HmuT : M.mu u5 = nf + bc + cc).
  { rewrite <- Pm5, Mu4, Mu3, Mu2. destruct E8 as (_ & _ & _ & Em & _). rewrite <- Em. lia. }
  assert (HcertT : (M.cert u5 = true <-> 1 <= cc)).
  { rewrite <- Pk5. destruct (Nat.eq_dec cc 0) as [Hc0' | Hc0'].
    - rewrite (Ce40 Hc0'). destruct E8 as (_ & _ & _ & _ & Ek8). rewrite Ce3, Ce2, <- Ek8, Hce0.
      split; [intro Hx; discriminate Hx | intro; lia].
    - rewrite (Ce41 ltac:(lia)). split; [intros _; lia | intros _; reflexivity]. }
  (* the closing check *)
  assert (Hpc5 : M.pc (M.core_of u5) = o13 + 1) by (rewrite P5; simpl; lia).
  destruct (Nat.eq_dec fe 0) as [Hfe0 | Hfe0].
  - assert (Hv4_5' : M.vals (M.core_of u5) base4 = 0) by (rewrite Hv4_5; exact Hfe0).
    destruct (sm2_trap_zero Q o13 base4 z rd Hq13 ltac:(lia) u5 Hpc5 E5 Hv4_5')
      as (u6 & RC6 & P6 & E6 & V6 & PF6).
    destruct PF6 as (Pf6 & Pc6 & Pe6 & Pm6 & Pk6).
    exists u6. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + eapply sm2_RR_step; [exact N8 |]. eapply sm2_RR_trans; [exact RC2 |].
      eapply sm2_RR_trans; [exact RC3 |]. eapply sm2_RR_trans; [exact RC4 |].
      eapply sm2_RR_trans; [exact RC5 |]. exact RC6.
    + unfold M.halted, M.next_instr. rewrite E6, P6, (sm2_fetch_end Q); [reflexivity | lia].
    + rewrite (V6 0). exact Hv05.
    + rewrite <- Pe6, E5. split; [intro Hx; discriminate Hx | intro Hx; lia].
    + rewrite <- Pm6, HmuT. lia.
    + rewrite <- Pk6. exact HcertT.
    + rewrite <- Pf6. exact Hlenf.
    + rewrite <- Pc6. exact HchanT.
  - assert (Hfe1 : fe = 1) by lia.
    assert (Hv4_5' : M.vals (M.core_of u5) base4 = S 0) by (rewrite Hv4_5, Hfe1; reflexivity).
    destruct (sm2_trap_pos Q o13 base4 z rd Hq13 u5 0 Hpc5 E5 Hv4_5' Hrd_5 ltac:(lia))
      as (u6 & RC6 & E6 & V6 & Fa6 & C6 & Mu6 & Ce6).
    exists u6. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + eapply sm2_RR_step; [exact N8 |]. eapply sm2_RR_trans; [exact RC2 |].
      eapply sm2_RR_trans; [exact RC3 |]. eapply sm2_RR_trans; [exact RC4 |].
      eapply sm2_RR_trans; [exact RC5 |]. exact RC6.
    + unfold M.halted, M.next_instr. rewrite E6. reflexivity.
    + rewrite (V6 0 ltac:(lia)). exact Hv05.
    + rewrite E6. split; [intros _; exact Hfe1 | intros _; reflexivity].
    + rewrite Mu6, HmuT. lia.
    + rewrite Ce6. exact HcertT.
    + rewrite Fa6. exact Hlenf.
    + rewrite C6. exact HchanT.
Qed.

End Chain.

Print Assumptions sm2_setup.
Print Assumptions sm2_setup_halt.
Print Assumptions sm2_replay.

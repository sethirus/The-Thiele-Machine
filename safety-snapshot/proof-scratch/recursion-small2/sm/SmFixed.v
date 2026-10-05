(** SmFixed.v: the replay program sm2_VG as one list of host instructions.

    SmChain.v runs thirteen pieces one after another and says what each does.
    This file builds the list: the two fans, the five Minsky blocks relocated
    at their offsets, INC rs, the three effect loops, the move into register
    0 and the closing check, each placed at the line where the previous piece
    ends. The registers of the five windows follow one another from register
    3; the jump register, the slot register and the register that is never
    written come next.

    What is proved:
      1. Every piece sits in sm2_VG at its offset, and the offsets add up
         [sm2_VGq1 .. sm2_VGq13, sm2_VG_length, sm2_VG_fetch8].
      2. [sm2_VG_forward]: started from the state after the specialising
         prefix (pc 1, registers 0, x, c, 0, 0, ..., empty record), if the five
         relations hold of five numbers m_0 .. m_4 that are the numbers of a
         record that could be (at most 16 facts, m_4 at most 1, a commit needs
         a fact, a certify needs a commit), the program stops with m_0 in
         register 0, ledger m_1 + m_2 + m_3 + m_4, m_1 facts, an empty
         channel exactly when m_2 = 0, the flag up exactly when m_3 >= 1 and
         the trap latch up exactly when m_4 = 1.
      3. [sm2_VG_halt]: if the program stops, the first relation holds of
         some number.

    Dependencies: Coq standard library, EarnedMulti.v, UniversalCodes.v and
    the Sm files up to SmChain.v. No axioms, no Admitted.                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedMulti Minimal.UniversalCodes.
Require Import Sm.SmHostBlocks Sm.SmCodes Sm.SmLoops Sm.SmLoops2 Sm.SmLoops3 Sm.SmMMAOff
  Sm.SmBlock Sm.SmKleene Sm.SmChain.
Module M := Minimal.EarnedMulti.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

Local Notation hinstr := (@M.instr UC.hprop).
Local Notation hstate := (@M.state UC.hprop).
Local Notation hrun_prog := (M.run_prog UC.hprop_eqb UC.heval).

Section Assemble.

Variables (R0 R1 R2 R3 R4 : nat -> nat -> nat -> Prop).
Variable b0 : sm2_bint R0.
Variable b1 : sm2_bint R1.
Variable b2 : sm2_bint R2.
Variable b3 : sm2_bint R3.
Variable b4 : sm2_bint R4.

Definition sm2_lb0 : nat := 3.
Definition sm2_lb1 : nat := sm2_lb0 + sm2_bi_N b0.
Definition sm2_lb2 : nat := sm2_lb1 + sm2_bi_N b1.
Definition sm2_lb3 : nat := sm2_lb2 + sm2_bi_N b2.
Definition sm2_lb4 : nat := sm2_lb3 + sm2_bi_N b3.
Definition sm2_lz : nat := sm2_lb4 + sm2_bi_N b4.
Definition sm2_lrs : nat := sm2_lz + 1.
Definition sm2_lrd : nat := sm2_lz + 2.

Definition sm2_lo1 : nat := 0.
Definition sm2_lo2 : nat := sm2_lo1 + 10.
Definition sm2_lo3 : nat := sm2_lo2 + 10.
Definition sm2_lo4 : nat := sm2_lo3 + sm2_bi_len b0.
Definition sm2_lo5 : nat := sm2_lo4 + sm2_bi_len b1.
Definition sm2_lo6 : nat := sm2_lo5 + sm2_bi_len b2.
Definition sm2_lo7 : nat := sm2_lo6 + sm2_bi_len b3.
Definition sm2_lo8 : nat := sm2_lo7 + sm2_bi_len b4.
Definition sm2_lo9 : nat := sm2_lo8 + 1.
Definition sm2_lo10 : nat := sm2_lo9 + 6.
Definition sm2_lo11 : nat := sm2_lo10 + 6.
Definition sm2_lo12 : nat := sm2_lo11 + 6.
Definition sm2_lo13 : nat := sm2_lo12 + 6.

Definition sm2_gdx (o : nat) : list hinstr := sm2_fan o 1 sm2_lz (sm2_dsx sm2_lb0 sm2_lb1 sm2_lb2 sm2_lb3 sm2_lb4).
Definition sm2_gdc (o : nat) : list hinstr := sm2_fan o 2 sm2_lz (sm2_dsc sm2_lb0 sm2_lb1 sm2_lb2 sm2_lb3 sm2_lb4).
Definition sm2_gb0 (o : nat) : list hinstr := sm_reloc o (sm2_bi_prog b0 sm2_lb0).
Definition sm2_gb1 (o : nat) : list hinstr := sm_reloc o (sm2_bi_prog b1 sm2_lb1).
Definition sm2_gb2 (o : nat) : list hinstr := sm_reloc o (sm2_bi_prog b2 sm2_lb2).
Definition sm2_gb3 (o : nat) : list hinstr := sm_reloc o (sm2_bi_prog b3 sm2_lb3).
Definition sm2_gb4 (o : nat) : list hinstr := sm_reloc o (sm2_bi_prog b4 sm2_lb4).
Definition sm2_ginc (o : nat) : list hinstr := [M.INC sm2_lrs].
Definition sm2_gchk (o : nat) : list hinstr := sm2_whilel o sm2_lb1 sm2_lz [M.CHECK UC.PSlot sm2_lrs].
Definition sm2_gcmt (o : nat) : list hinstr := sm2_whilel o sm2_lb2 sm2_lz [M.COMMIT UC.PSlot sm2_lrs].
Definition sm2_gcer (o : nat) : list hinstr := sm2_whilel o sm2_lb3 sm2_lz [M.CERTIFY].
Definition sm2_gout (o : nat) : list hinstr := sm2_fan o sm2_lb0 sm2_lz [0].
Definition sm2_gtrap (o : nat) : list hinstr := sm2_trapg o sm2_lb4 sm2_lz sm2_lrd.

Definition sm2_VG : list hinstr :=
  sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++
  sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13.

Lemma sm2_len_gdx : forall o, length (sm2_gdx o) = 10.
Proof. intro o. unfold sm2_gdx, sm2_fan. rewrite sm2_whilel_length, map_length. reflexivity. Qed.
Lemma sm2_len_gdc : forall o, length (sm2_gdc o) = 10.
Proof. intro o. unfold sm2_gdc, sm2_fan. rewrite sm2_whilel_length, map_length. reflexivity. Qed.
Lemma sm2_len_gb0 : forall o, length (sm2_gb0 o) = sm2_bi_len b0.
Proof. intro o. unfold sm2_gb0. rewrite sm_reloc_length. apply sm2_bi_len_eq. Qed.
Lemma sm2_len_gb1 : forall o, length (sm2_gb1 o) = sm2_bi_len b1.
Proof. intro o. unfold sm2_gb1. rewrite sm_reloc_length. apply sm2_bi_len_eq. Qed.
Lemma sm2_len_gb2 : forall o, length (sm2_gb2 o) = sm2_bi_len b2.
Proof. intro o. unfold sm2_gb2. rewrite sm_reloc_length. apply sm2_bi_len_eq. Qed.
Lemma sm2_len_gb3 : forall o, length (sm2_gb3 o) = sm2_bi_len b3.
Proof. intro o. unfold sm2_gb3. rewrite sm_reloc_length. apply sm2_bi_len_eq. Qed.
Lemma sm2_len_gb4 : forall o, length (sm2_gb4 o) = sm2_bi_len b4.
Proof. intro o. unfold sm2_gb4. rewrite sm_reloc_length. apply sm2_bi_len_eq. Qed.
Lemma sm2_len_ginc : forall o, length (sm2_ginc o) = 1.
Proof. intro o. reflexivity. Qed.
Lemma sm2_len_gchk : forall o, length (sm2_gchk o) = 6.
Proof. intro o. unfold sm2_gchk. rewrite sm2_whilel_length. reflexivity. Qed.
Lemma sm2_len_gcmt : forall o, length (sm2_gcmt o) = 6.
Proof. intro o. unfold sm2_gcmt. rewrite sm2_whilel_length. reflexivity. Qed.
Lemma sm2_len_gcer : forall o, length (sm2_gcer o) = 6.
Proof. intro o. unfold sm2_gcer. rewrite sm2_whilel_length. reflexivity. Qed.
Lemma sm2_len_gout : forall o, length (sm2_gout o) = 6.
Proof. intro o. unfold sm2_gout, sm2_fan. rewrite sm2_whilel_length. reflexivity. Qed.
Lemma sm2_len_gtrap : forall o, length (sm2_gtrap o) = 4.
Proof. intro o. reflexivity. Qed.

Ltac sm2_lens :=
  repeat rewrite app_length;
  repeat first [rewrite sm2_len_gdx | rewrite sm2_len_gdc | rewrite sm2_len_gb0 | rewrite sm2_len_gb1 | rewrite sm2_len_gb2
               | rewrite sm2_len_gb3 | rewrite sm2_len_gb4 | rewrite sm2_len_ginc | rewrite sm2_len_gchk
               | rewrite sm2_len_gcmt | rewrite sm2_len_gcer | rewrite sm2_len_gout | rewrite sm2_len_gtrap];
  unfold sm2_lo13, sm2_lo12, sm2_lo11, sm2_lo10, sm2_lo9, sm2_lo8, sm2_lo7, sm2_lo6, sm2_lo5, sm2_lo4, sm2_lo3, sm2_lo2, sm2_lo1; cbn [length]; lia.

Lemma sm2_VGq1 : sm2_inQ sm2_VG sm2_lo1 (sm2_gdx sm2_lo1).
Proof.
  assert (HV : sm2_VG = (@nil hinstr) ++ sm2_gdx sm2_lo1 ++ (sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (@nil hinstr) = sm2_lo1) by sm2_lens.
  pose proof (sm2_inQ_app (@nil hinstr) (sm2_gdx sm2_lo1) (sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq2 : sm2_inQ sm2_VG sm2_lo2 (sm2_gdc sm2_lo2).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1) ++ sm2_gdc sm2_lo2 ++ (sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1) = sm2_lo2) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1) (sm2_gdc sm2_lo2) (sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq3 : sm_embeds sm2_VG (sm2_bi_prog b0 sm2_lb0) sm2_lo3.
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2) ++ sm2_gb0 sm2_lo3 ++ (sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2) = sm2_lo3) by sm2_lens.
  pose proof (sm_embeds_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2) (sm2_bi_prog b0 sm2_lb0) (sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. unfold sm2_gb0 in HV. rewrite HV. exact H.
Qed.

Lemma sm2_VGq4 : sm_embeds sm2_VG (sm2_bi_prog b1 sm2_lb1) sm2_lo4.
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3) ++ sm2_gb1 sm2_lo4 ++ (sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3) = sm2_lo4) by sm2_lens.
  pose proof (sm_embeds_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3) (sm2_bi_prog b1 sm2_lb1) (sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. unfold sm2_gb1 in HV. rewrite HV. exact H.
Qed.

Lemma sm2_VGq5 : sm_embeds sm2_VG (sm2_bi_prog b2 sm2_lb2) sm2_lo5.
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4) ++ sm2_gb2 sm2_lo5 ++ (sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4) = sm2_lo5) by sm2_lens.
  pose proof (sm_embeds_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4) (sm2_bi_prog b2 sm2_lb2) (sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. unfold sm2_gb2 in HV. rewrite HV. exact H.
Qed.

Lemma sm2_VGq6 : sm_embeds sm2_VG (sm2_bi_prog b3 sm2_lb3) sm2_lo6.
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5) ++ sm2_gb3 sm2_lo6 ++ (sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5) = sm2_lo6) by sm2_lens.
  pose proof (sm_embeds_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5) (sm2_bi_prog b3 sm2_lb3) (sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. unfold sm2_gb3 in HV. rewrite HV. exact H.
Qed.

Lemma sm2_VGq7 : sm_embeds sm2_VG (sm2_bi_prog b4 sm2_lb4) sm2_lo7.
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6) ++ sm2_gb4 sm2_lo7 ++ (sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6) = sm2_lo7) by sm2_lens.
  pose proof (sm_embeds_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6) (sm2_bi_prog b4 sm2_lb4) (sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. unfold sm2_gb4 in HV. rewrite HV. exact H.
Qed.

Lemma sm2_VGq8 : sm2_inQ sm2_VG sm2_lo8 (sm2_ginc sm2_lo8).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7) ++ sm2_ginc sm2_lo8 ++ (sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7) = sm2_lo8) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7) (sm2_ginc sm2_lo8) (sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq9 : sm2_inQ sm2_VG sm2_lo9 (sm2_gchk sm2_lo9).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8) ++ sm2_gchk sm2_lo9 ++ (sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8) = sm2_lo9) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8) (sm2_gchk sm2_lo9) (sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq10 : sm2_inQ sm2_VG sm2_lo10 (sm2_gcmt sm2_lo10).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9) ++ sm2_gcmt sm2_lo10 ++ (sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9) = sm2_lo10) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9) (sm2_gcmt sm2_lo10) (sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq11 : sm2_inQ sm2_VG sm2_lo11 (sm2_gcer sm2_lo11).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10) ++ sm2_gcer sm2_lo11 ++ (sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10) = sm2_lo11) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10) (sm2_gcer sm2_lo11) (sm2_gout sm2_lo12 ++ sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq12 : sm2_inQ sm2_VG sm2_lo12 (sm2_gout sm2_lo12).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11) ++ sm2_gout sm2_lo12 ++ (sm2_gtrap sm2_lo13)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11) = sm2_lo12) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11) (sm2_gout sm2_lo12) (sm2_gtrap sm2_lo13)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VGq13 : sm2_inQ sm2_VG sm2_lo13 (sm2_gtrap sm2_lo13).
Proof.
  assert (HV : sm2_VG = (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12) ++ sm2_gtrap sm2_lo13 ++ (@nil hinstr)) by (unfold sm2_VG; repeat rewrite <- app_assoc; reflexivity).
  assert (Hl : length (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12) = sm2_lo13) by sm2_lens.
  pose proof (sm2_inQ_app (sm2_gdx sm2_lo1 ++ sm2_gdc sm2_lo2 ++ sm2_gb0 sm2_lo3 ++ sm2_gb1 sm2_lo4 ++ sm2_gb2 sm2_lo5 ++ sm2_gb3 sm2_lo6 ++ sm2_gb4 sm2_lo7 ++ sm2_ginc sm2_lo8 ++ sm2_gchk sm2_lo9 ++ sm2_gcmt sm2_lo10 ++ sm2_gcer sm2_lo11 ++ sm2_gout sm2_lo12) (sm2_gtrap sm2_lo13) (@nil hinstr)) as H.
  rewrite Hl in H. rewrite HV. exact H.
Qed.

Lemma sm2_VG_length : length sm2_VG = sm2_lo13 + 4.
Proof. unfold sm2_VG. sm2_lens. Qed.

Lemma sm2_VG_fetch8 : M.fetch sm2_VG (sm2_lo8 + 1) = Some (M.INC sm2_lrs).
Proof.
  pose proof (sm2_VGq8 1 ltac:(simpl; lia)) as H. rewrite H. reflexivity.
Qed.

(* The chain lemmas of SmChain.v, for the program sm2_VG. *)

Definition sm2_vgstart (x c : nat) (u : hstate) : Prop :=
  M.pc (M.core_of u) = 1 /\ M.err (M.core_of u) = false /\
  (forall q, M.vals (M.core_of u) q = sm_in2 x c q) /\
  M.facts (M.core_of u) = [] /\ M.chan (M.core_of u) = None /\ M.mu u = 0 /\ M.cert u = false.

Theorem sm2_VG_forward : forall x c m0 m1 m2 m3 m4 (u : hstate),
  sm2_vgstart x c u ->
  R0 x c m0 -> R1 x c m1 -> R2 x c m2 -> R3 x c m3 -> R4 x c m4 ->
  m1 <= 16 -> m4 <= 1 -> (1 <= m2 -> 1 <= m1) -> (1 <= m3 -> 1 <= m2) ->
  exists u', sm2_RR sm2_VG u u' /\ M.halted sm2_VG (M.core_of u') /\
    M.vals (M.core_of u') 0 = m0 /\ (M.err (M.core_of u') = true <-> m4 = 1) /\
    M.mu u' = m1 + m2 + m3 + m4 /\ (M.cert u' = true <-> 1 <= m3) /\
    length (M.facts (M.core_of u')) = m1 /\ (M.chan (M.core_of u') = None <-> m2 = 0).
Proof.
  intros x c m0 m1 m2 m3 m4 u (Hp & He & Hv & Hf & Hc & Hm & Hk) H0 H1 H2 H3 H4 Hn1 Hn4 Hb Hc3.
  destruct (@sm2_setup R0 R1 R2 R3 R4 b0 b1 b2 b3 b4 sm2_lb0 sm2_lb1 sm2_lb2 sm2_lb3 sm2_lb4 sm2_lz sm2_lrs sm2_lrd
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              sm2_lo1 sm2_lo2 sm2_lo3 sm2_lo4 sm2_lo5 sm2_lo6 sm2_lo7 sm2_lo8 sm2_lo9 sm2_lo10 sm2_lo11 sm2_lo12 sm2_lo13
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              sm2_VG sm2_VGq1 sm2_VGq2 sm2_VGq3 sm2_VGq4 sm2_VGq5 sm2_VGq6 sm2_VGq7 sm2_VG_length
              x c m0 m1 m2 m3 m4 u H0 H1 H2 H3 H4 ltac:(rewrite Hp; reflexivity) He Hv)
    as (u1 & R1' & P1 & E1 & V0 & V1 & V2 & V3 & V4 & Vrs & Vrd & Vr0 & PF1).
  destruct PF1 as (Pf & Pc & Pe & Pm & Pk).
  destruct (@sm2_replay R0 R1 R2 R3 R4 b0 b1 b2 b3 b4 sm2_lb0 sm2_lb1 sm2_lb2 sm2_lb3 sm2_lb4 sm2_lz sm2_lrs sm2_lrd
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              sm2_lo1 sm2_lo2 sm2_lo3 sm2_lo4 sm2_lo5 sm2_lo6 sm2_lo7 sm2_lo8 sm2_lo9 sm2_lo10 sm2_lo11 sm2_lo12 sm2_lo13
              eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
              sm2_VG sm2_VG_fetch8 sm2_VGq9 sm2_VGq10 sm2_VGq11 sm2_VGq12 sm2_VGq13 sm2_VG_length
              u1 m0 m1 m2 m3 m4 P1 E1 V0 V1 V2 V3 V4 Vrs Vrd Vr0
              ltac:(rewrite <- Pf; exact Hf) ltac:(rewrite <- Pc; exact Hc)
              ltac:(rewrite <- Pm; exact Hm) ltac:(rewrite <- Pk; exact Hk) Hn1 Hn4 Hb Hc3)
    as (u' & R2' & Hh & Vo & Ee & Mu & Ce & Fl & Ch).
  exists u'. refine (conj _ (conj Hh (conj Vo (conj Ee (conj Mu (conj Ce (conj Fl Ch))))))).
  eapply sm2_RR_trans; [exact R1' | exact R2'].
Qed.

Theorem sm2_VG_halt : forall x c (u : hstate),
  sm2_vgstart x c u ->
  forall n, M.next_instr sm2_VG (M.core_of (hrun_prog n sm2_VG u)) = None -> exists m, R0 x c m.
Proof.
  intros x c u (Hp & He & Hv & _) n Hn.
  exact (@sm2_setup_halt R0 R1 R2 R3 R4 b0 b1 b2 b3 b4 sm2_lb0 sm2_lb1 sm2_lb2 sm2_lb3 sm2_lb4 sm2_lz sm2_lrs sm2_lrd
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           sm2_lo1 sm2_lo2 sm2_lo3 sm2_lo4 sm2_lo5 sm2_lo6 sm2_lo7 sm2_lo8 sm2_lo9 sm2_lo10 sm2_lo11 sm2_lo12 sm2_lo13
           eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
           sm2_VG sm2_VGq1 sm2_VGq2 sm2_VGq3 sm2_VG_length x c u ltac:(rewrite Hp; reflexivity) He Hv n Hn).
Qed.

End Assemble.

Print Assumptions sm2_VG_forward.
Print Assumptions sm2_VG_halt.

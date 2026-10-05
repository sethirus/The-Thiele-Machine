(** UniversalPLayout.v: the fixed host program U_P of the universal
    interpreter, as one concrete list of host instructions.

    This file is the priced counterpart of UniversalLayout.v: the host is the
    machine of EarnedMultiPriced.v (with PAY), the guest is the priced
    machine of EarnedPriced.v over the universal property language
    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and
    the host program is U_P.

    U_P is built from the blocks of UniversalPBlocks.v. It starts at host
    address 1. Its registers:

      pu_RA = 0, pu_RB = 1          the guest counters (greg CA = pu_RA, greg CB = pu_RB)
      pu_PROG = 2                the code of the guest program
      pu_GPC = 3                 the guest pc
      pu_T0 .. pu_T9 = 4 .. 13      scratch
      pu_NC c = 14 + ccode c     how many CHECK moves on counter c passed
      pu_MP c k = 16 + 16 ccode c + k    mirror of slot k of bank c
                              (claim code + 1 when the slot is live, else 0)
      pu_SLOT c k = 48 + 16 ccode c + k  slot k of bank c, the fact holders
      pu_DEAD = 80               never written; a record move on it fails

    Sections of U_P, each at a named address:

      pu_L_HEAD  (address 1)  fetch the current guest instruction, split its
                           code into opcode and operand, jump to the
                           opcode's handler; guest pc 0 or past the end
                           goes to pu_L_HALT
      pu_L_HALT               clear the scratch registers, then HALT
      pu_L_INC                choose the bank; pu_L_INCH c: INC (greg c), bump
                           every slot of bank c, INC pu_GPC, back to pu_L_HEAD
      pu_L_DEC                split the operand into bank and target;
                           pu_L_DECH c: DEC (greg c); on 0, INC pu_GPC; else bump
                           every slot of bank c and set pu_GPC to the target
      pu_L_CHECK              split the operand into bank and property code;
                           pu_L_CKH c: a 17-way branch on pu_NC c; for k < 16 the
                           block pu_hCKS c k packs (property code, value of
                           greg c) into pu_SLOT c k, runs CHECK PSlot (pu_SLOT c k),
                           sets pu_MP c k := code + 1, INC pu_NC c, INC pu_GPC; for
                           pu_NC c >= 16 it runs CHECK PSlot pu_DEAD
      pu_L_COMMIT             split the operand; pu_L_CMH c: compare pu_MP c k with
                           code + 1 for k = 0 .. 15 (EQR); the first match
                           runs COMMIT PSlot (pu_SLOT c k); no match runs
                           COMMIT PSlot pu_DEAD
      pu_L_CERT               CERTIFY, INC pu_GPC, back to pu_L_HEAD
      pu_L_PAY                PAY, INC pu_GPC, back to pu_L_HEAD

    The opcode dispatch of pu_L_HEAD is 7-way: INC, DEC, HALT, CHECK,
    COMMIT, CERTIFY and PAY.

    Proved here: the length of every block, the value of every label, the
    placement (subcode) of every section and of every per-(c, k) block in
    U_P, proved once per family; the exact list of instructions of U_P that
    mention pu_SLOT c k (two bumps, the move into the slot, its CHECK and its
    COMMIT), that every DEC on a slot jumps to the next address whatever
    the slot holds, the exact list of instructions that mention pu_DEAD, the
    exact list of instructions that cost anything (CHECK, COMMIT and
    CERTIFY sites and the one PAY site, 70 of them), the single HALT, and that U_P mentions no
    register above pu_DEAD.

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedGeneric.v, EarnedPriced.v, EarnedMultiPriced.v, CompilerChecker.v,
    UniversalPCodes.v, UniversalPBridge.v and UniversalPBlocks.v. No axioms,
    no Admitted.                                                          *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Minimal.UniversalPCodes Minimal.UniversalPBridge Minimal.UniversalPBlocks.

Local Notation hinstr := (@M.pu_instr pu_hprop).

(* ================================================================= *)
(* Registers.                                                         *)
(* ================================================================= *)

(* SAFE: register number 0 is where the guest's counter A lives, as
   register 0 of the host machine; it is an address, not a placeholder. *)
Definition pu_RA : nat := 0.
Definition pu_RB : nat := 1.
Definition pu_PROG : nat := 2.
Definition pu_GPC : nat := 3.
Definition pu_T0 : nat := 4.
Definition pu_T1 : nat := 5.
Definition pu_T2 : nat := 6.
Definition pu_T3 : nat := 7.
Definition pu_T4 : nat := 8.
Definition pu_T5 : nat := 9.
Definition pu_T6 : nat := 10.
Definition pu_T7 : nat := 11.
Definition pu_T8 : nat := 12.
Definition pu_T9 : nat := 13.
Definition pu_greg (c : E.ctr) : nat := pu_ccode c.
Definition pu_NC (c : E.ctr) : nat := 14 + pu_ccode c.
Definition pu_MP (c : E.ctr) (k : nat) : nat := 16 + 16 * pu_ccode c + k.
Definition pu_SLOT (c : E.ctr) (k : nat) : nat := 48 + 16 * pu_ccode c + k.
Definition pu_DEAD : nat := 80.

Definition pu_scratch (r : nat) : Prop := 4 <= r < 14.
Definition pu_in_mp (c : E.ctr) (r : nat) : Prop := 16 + 16 * pu_ccode c <= r < 32 + 16 * pu_ccode c.
Definition pu_in_slots (c : E.ctr) (r : nat) : Prop := 48 + 16 * pu_ccode c <= r < 64 + 16 * pu_ccode c.

Lemma pu_greg_CA : pu_greg E.CA = pu_RA. Proof. reflexivity. Qed.
Lemma pu_greg_CB : pu_greg E.CB = pu_RB. Proof. reflexivity. Qed.

Lemma pu_scratch_cases : forall r, pu_scratch r ->
  r = pu_T0 \/ r = pu_T1 \/ r = pu_T2 \/ r = pu_T3 \/ r = pu_T4 \/
  r = pu_T5 \/ r = pu_T6 \/ r = pu_T7 \/ r = pu_T8 \/ r = pu_T9.
Proof.
  intros r H. unfold pu_scratch in H.
  unfold pu_T0, pu_T1, pu_T2, pu_T3, pu_T4, pu_T5, pu_T6, pu_T7, pu_T8, pu_T9. lia.
Qed.

Lemma pu_in_mp_MP : forall c k, k < 16 -> pu_in_mp c (pu_MP c k).
Proof. intros c k Hk. unfold pu_in_mp, pu_MP. lia. Qed.

Lemma pu_in_slots_SLOT : forall c k, k < 16 -> pu_in_slots c (pu_SLOT c k).
Proof. intros c k Hk. unfold pu_in_slots, pu_SLOT. lia. Qed.

Lemma pu_in_mp_inv : forall c r, pu_in_mp c r -> exists k, k < 16 /\ r = pu_MP c k.
Proof. intros c r H. unfold pu_in_mp in H. exists (r - (16 + 16 * pu_ccode c)). unfold pu_MP. lia. Qed.

Lemma pu_in_slots_inv : forall c r, pu_in_slots c r -> exists k, k < 16 /\ r = pu_SLOT c k.
Proof.
  intros c r H. unfold pu_in_slots in H. exists (r - (48 + 16 * pu_ccode c)). unfold pu_SLOT. lia.
Qed.

(* ================================================================= *)
(* Families of blocks placed one after another.                       *)
(* ================================================================= *)

(* fam f len k n o: the blocks f k, f (k+1), ..., f (k+n-1), each of
   length len, the first at address o. *)
Fixpoint pu_fam (f : nat -> nat -> list hinstr) (len k n o : nat) : list hinstr :=
  match n with
  | 0 => []
  | S n' => f k o ++ pu_fam f len (S k) n' (len + o)
  end.

Lemma pu_fam_length : forall f len, (forall k o, length (f k o) = len) ->
  forall n k o, length (pu_fam f len k n o) = n * len.
Proof.
  intros f len Hl n. induction n as [| n IH]; intros k o; [reflexivity |].
  simpl. rewrite app_length, Hl, IH. reflexivity.
Qed.

Lemma pu_fam_sub : forall f len, (forall k o, length (f k o) = len) ->
  forall n k0 o k, k0 <= k -> k < k0 + n ->
  subcode (o + (k - k0) * len, f k (o + (k - k0) * len)) (o, pu_fam f len k0 n o).
Proof.
  intros f len Hl n. induction n as [| n IH]; intros k0 o k H1 H2; [lia |].
  cbn [pu_fam]. destruct (Nat.eq_dec k k0) as [-> | Hne].
  - rewrite Nat.sub_diag, Nat.mul_0_l, Nat.add_0_r. apply subcode_left. reflexivity.
  - apply subcode_trans with (Q := (len + o, pu_fam f len (S k0) n (len + o))).
    + replace (o + (k - k0) * len) with (len + o + (k - S k0) * len).
      * apply IH; lia.
      * replace (k - k0) with (S (k - S k0)) by lia. simpl. lia.
    + apply subcode_right. rewrite Hl. lia.
Qed.

Corollary pu_fam_sub0 : forall f len, (forall k o, length (f k o) = len) ->
  forall n o k, k < n -> subcode (o + k * len, f k (o + k * len)) (o, pu_fam f len 0 n o).
Proof.
  intros f len Hl n o k Hk. pose proof (pu_fam_sub f len Hl n 0 o k (Nat.le_0_l k) Hk) as H.
  rewrite Nat.sub_0_r in H. exact H.
Qed.

(* ================================================================= *)
(* Lengths, offsets and labels.                                       *)
(* ================================================================= *)

Definition pu_HEAD_len : nat := pu_FETCH_len + 1 + UNPACK_len + 3 * 7 + JMP_len.
Definition pu_HALTB_len : nat := 11.
Definition pu_CD_len : nat := 3 * 2 + JMP_len.
Definition pu_UCD_len : nat := UNPACK_len + 3 * 2 + JMP_len.
Definition pu_BUMPS_len : nat := 16 * pu_BUMP_len.
Definition pu_INCH_len : nat := 2 + pu_BUMPS_len + JMP_len.
Definition pu_DECH_len : nat := 5 + pu_BUMPS_len + 1 + MOVE_len + JMP_len.
Definition pu_CKS_len : nat := 2 * pu_COPY_len + PACK_len + MOVE_len + 2 + MOVE_len + 3 + JMP_len.
Definition pu_CKH_len : nat := pu_COPY_len + 3 * 16 + 1 + JMP_len + 16 * pu_CKS_len.
Definition pu_CMS_len : nat := 3 + JMP_len.
Definition pu_CMH_len : nat := 1 + 16 * pu_EQR_len + 1 + JMP_len + 16 * pu_CMS_len.
Definition pu_CERTH_len : nat := 2 + JMP_len.
Definition pu_PAYH_len : nat := 2 + JMP_len.

(* Offsets inside the per-bank handlers. *)
Definition pu_DECH_taken (o : nat) : nat := 5 + o.
Definition pu_CKS_chk (o : nat) : nat := 2 * pu_COPY_len + PACK_len + MOVE_len + o.
Definition pu_CKH_dead (o : nat) : nat := pu_COPY_len + 3 * 16 + o.
Definition pu_CKH_slots (o : nat) : nat := pu_COPY_len + 3 * 16 + 1 + JMP_len + o.
Definition pu_CKS_at (o k : nat) : nat := pu_CKH_slots o + k * pu_CKS_len.
Definition pu_CMH_dead (o : nat) : nat := 1 + 16 * pu_EQR_len + o.
Definition pu_CMH_slots (o : nat) : nat := 1 + 16 * pu_EQR_len + 1 + JMP_len + o.
Definition pu_CMS_at (o k : nat) : nat := pu_CMH_slots o + k * pu_CMS_len.

(* Labels. *)
Definition pu_L_HEAD : nat := 1.
Definition pu_L_HALT : nat := pu_L_HEAD + pu_HEAD_len.
Definition pu_L_INC : nat := pu_L_HALT + pu_HALTB_len.
Definition pu_L_INCH (c : E.ctr) : nat := pu_L_INC + pu_CD_len + pu_ccode c * pu_INCH_len.
Definition pu_L_DEC : nat := pu_L_INC + pu_CD_len + 2 * pu_INCH_len.
Definition pu_L_DECH (c : E.ctr) : nat := pu_L_DEC + pu_UCD_len + pu_ccode c * pu_DECH_len.
Definition pu_L_CHECK : nat := pu_L_DEC + pu_UCD_len + 2 * pu_DECH_len.
Definition pu_L_CKH (c : E.ctr) : nat := pu_L_CHECK + pu_UCD_len + pu_ccode c * pu_CKH_len.
Definition pu_L_COMMIT : nat := pu_L_CHECK + pu_UCD_len + 2 * pu_CKH_len.
Definition pu_L_CMH (c : E.ctr) : nat := pu_L_COMMIT + pu_UCD_len + pu_ccode c * pu_CMH_len.
Definition pu_L_CERT : nat := pu_L_COMMIT + pu_UCD_len + 2 * pu_CMH_len.
Definition pu_L_STOP : nat := pu_L_HALT + 10.
Definition pu_L_PAY : nat := pu_L_CERT + pu_CERTH_len.
Definition pu_U_len : nat := pu_L_PAY + pu_PAYH_len - 1.

(* The handler address of each guest opcode. *)
Definition pu_op_of (i : E.instr) : nat :=
  match i with
  | E.INC _ => 0 | E.DEC _ _ => 1 | E.HALT => 2
  | E.CHECK _ _ => 3 | E.COMMIT _ _ => 4 | E.CERTIFY => 5 | E.PAY => 6
  end.
Definition pu_arg_of (i : E.instr) : nat :=
  match i with
  | E.INC c => pu_ccode c
  | E.DEC c j => pu_pair (pu_ccode c) j
  | E.HALT => 0
  | E.CHECK p c => pu_pair (pu_ccode c) (pu_pcode p)
  | E.COMMIT p c => pu_pair (pu_ccode c) (pu_pcode p)
  | E.CERTIFY => 0
  | E.PAY => 0
  end.
Definition pu_handlers : list nat :=
  [pu_L_INC; pu_L_DEC; pu_L_HALT; pu_L_CHECK; pu_L_COMMIT; pu_L_CERT; pu_L_PAY].
Definition pu_handler (i : E.instr) : nat := nth (pu_op_of i) pu_handlers 0.

Lemma pu_icode_op_arg : forall i, pu_icode i = pu_pair (pu_op_of i) (pu_arg_of i).
Proof. intros []; reflexivity. Qed.

Lemma pu_op_of_lt : forall i, pu_op_of i < length pu_handlers.
Proof. intros []; simpl; lia. Qed.

(* ================================================================= *)
(* The blocks of U_P.                                                   *)
(* ================================================================= *)

(* HEAD: fetch, split the code, dispatch on the opcode. *)
Definition pu_hHEAD (o : nat) : list hinstr :=
  pu_hFETCH pu_PROG pu_GPC pu_T0 pu_T1 pu_T2 pu_T3 pu_T4 pu_L_HALT pu_L_HALT o ++
  pu_hZERO pu_T0 (pu_FETCH_len + o) ++
  pu_hUNPACK pu_T3 pu_T2 pu_T5 (1 + pu_FETCH_len + o) ++
  pu_hDISP pu_T5 pu_T4 pu_handlers (1 + pu_FETCH_len + UNPACK_len + o) ++
  pu_hJMP pu_T4 pu_L_HALT (3 * 7 + 1 + pu_FETCH_len + UNPACK_len + o).

(* HALT: clear the scratch registers, then stop. *)
Definition pu_hHALTB (o : nat) : list hinstr :=
  pu_hZERO pu_T0 o ++ pu_hZERO pu_T1 (1 + o) ++ pu_hZERO pu_T2 (2 + o) ++ pu_hZERO pu_T3 (3 + o) ++
  pu_hZERO pu_T4 (4 + o) ++ pu_hZERO pu_T5 (5 + o) ++ pu_hZERO pu_T6 (6 + o) ++ pu_hZERO pu_T7 (7 + o) ++
  pu_hZERO pu_T8 (8 + o) ++ pu_hZERO pu_T9 (9 + o) ++ [M.HALT].

(* Bank choice on pu_T2 = ccode c. *)
Definition pu_hCD (ta tb o : nat) : list hinstr :=
  pu_hDISP pu_T2 pu_T4 [ta; tb] o ++ pu_hJMP pu_T4 pu_L_HALT (3 * 2 + o).

(* Split pu_T2 = pair (ccode c) x into pu_T2 := x, pu_T6 := ccode c; bank choice
   on pu_T6. *)
Definition pu_hUCD (ta tb o : nat) : list hinstr :=
  pu_hUNPACK pu_T3 pu_T2 pu_T6 o ++ pu_hDISP pu_T6 pu_T4 [ta; tb] (UNPACK_len + o) ++
  pu_hJMP pu_T4 pu_L_HALT (3 * 2 + UNPACK_len + o).

(* BUMP every slot of bank c. *)
Definition pu_hBUMPS (c : E.ctr) (o : nat) : list hinstr :=
  pu_fam (fun k o' => pu_hBUMP (pu_SLOT c k) (pu_MP c k) o') pu_BUMP_len 0 16 o.

Definition pu_hINCH (c : E.ctr) (o : nat) : list hinstr :=
  pu_hINC (pu_greg c) o ++ pu_hBUMPS c (1 + o) ++ pu_hINC pu_GPC (1 + pu_BUMPS_len + o) ++
  pu_hJMP pu_T4 pu_L_HEAD (2 + pu_BUMPS_len + o).

Definition pu_hDECH (c : E.ctr) (o : nat) : list hinstr :=
  pu_hDEC (pu_greg c) (pu_DECH_taken o) o ++ pu_hINC pu_GPC (1 + o) ++ pu_hZERO pu_T2 (2 + o) ++
  pu_hJMP pu_T4 pu_L_HEAD (3 + o) ++
  pu_hBUMPS c (pu_DECH_taken o) ++ pu_hZERO pu_GPC (pu_BUMPS_len + pu_DECH_taken o) ++
  pu_hMOVE pu_T2 pu_GPC (1 + pu_BUMPS_len + pu_DECH_taken o) ++
  pu_hJMP pu_T4 pu_L_HEAD (1 + MOVE_len + pu_BUMPS_len + pu_DECH_taken o).

(* Slot k of bank c: load the claim into the slot and check it. *)
Definition pu_hCKS (c : E.ctr) (k o : nat) : list hinstr :=
  pu_hCOPY (pu_greg c) pu_T8 pu_T4 o ++
  pu_hCOPY pu_T2 pu_T9 pu_T4 (pu_COPY_len + o) ++
  pu_hPACK pu_T3 pu_T8 pu_T9 (2 * pu_COPY_len + o) ++
  pu_hMOVE pu_T8 (pu_SLOT c k) (2 * pu_COPY_len + PACK_len + o) ++
  pu_hCHECK (pu_SLOT c k) (pu_CKS_chk o) ++
  pu_hZERO (pu_MP c k) (1 + pu_CKS_chk o) ++
  pu_hMOVE pu_T2 (pu_MP c k) (2 + pu_CKS_chk o) ++
  pu_hINC (pu_MP c k) (2 + MOVE_len + pu_CKS_chk o) ++
  pu_hINC (pu_NC c) (3 + MOVE_len + pu_CKS_chk o) ++
  pu_hINC pu_GPC (4 + MOVE_len + pu_CKS_chk o) ++
  pu_hJMP pu_T4 pu_L_HEAD (5 + MOVE_len + pu_CKS_chk o).

Definition pu_hCKH (c : E.ctr) (o : nat) : list hinstr :=
  pu_hCOPY (pu_NC c) pu_T7 pu_T4 o ++
  pu_hDISP pu_T7 pu_T4 (map (pu_CKS_at o) (seq 0 16)) (pu_COPY_len + o) ++
  pu_hCHECK pu_DEAD (pu_CKH_dead o) ++
  pu_hJMP pu_T4 pu_L_HALT (1 + pu_CKH_dead o) ++
  pu_fam (pu_hCKS c) pu_CKS_len 0 16 (pu_CKH_slots o).

(* Commit from slot sl. *)
Definition pu_hCMS (sl o : nat) : list hinstr :=
  pu_hCOMMIT sl o ++ pu_hZERO pu_T2 (1 + o) ++ pu_hINC pu_GPC (2 + o) ++ pu_hJMP pu_T4 pu_L_HEAD (3 + o).

Definition pu_hEQRS (c : E.ctr) (tgt : nat -> nat) (o : nat) : list hinstr :=
  pu_fam (fun k o' => pu_hEQR (pu_MP c k) pu_T2 pu_T7 pu_T8 pu_T4 (tgt k) o') pu_EQR_len 0 16 o.

Definition pu_hCMH (c : E.ctr) (o : nat) : list hinstr :=
  pu_hINC pu_T2 o ++
  pu_hEQRS c (pu_CMS_at o) (1 + o) ++
  pu_hCOMMIT pu_DEAD (pu_CMH_dead o) ++
  pu_hJMP pu_T4 pu_L_HALT (1 + pu_CMH_dead o) ++
  pu_fam (fun k o' => pu_hCMS (pu_SLOT c k) o') pu_CMS_len 0 16 (pu_CMH_slots o).

Definition pu_hCERTH (o : nat) : list hinstr :=
  pu_hCERTIFY o ++ pu_hINC pu_GPC (1 + o) ++ pu_hJMP pu_T4 pu_L_HEAD (2 + o).

(* PAY: pay 1, INC GPC, back to HEAD. *)
Definition pu_hPAYH (o : nat) : list hinstr :=
  pu_hPAY o ++ pu_hINC pu_GPC (1 + o) ++ pu_hJMP pu_T4 pu_L_HEAD (2 + o).

(* ================================================================= *)
(* Block lengths.                                                     *)
(* ================================================================= *)

Lemma pu_hHEAD_length : forall o, length (pu_hHEAD o) = pu_HEAD_len.
Proof. reflexivity. Qed.
Lemma pu_hHALTB_length : forall o, length (pu_hHALTB o) = pu_HALTB_len.
Proof. reflexivity. Qed.
Lemma pu_hCD_length : forall ta tb o, length (pu_hCD ta tb o) = pu_CD_len.
Proof. reflexivity. Qed.
Lemma pu_hUCD_length : forall ta tb o, length (pu_hUCD ta tb o) = pu_UCD_len.
Proof. reflexivity. Qed.
Lemma pu_hBUMPS_length : forall c o, length (pu_hBUMPS c o) = pu_BUMPS_len.
Proof. reflexivity. Qed.
Lemma pu_hINCH_length : forall c o, length (pu_hINCH c o) = pu_INCH_len.
Proof. reflexivity. Qed.
Lemma pu_hDECH_length : forall c o, length (pu_hDECH c o) = pu_DECH_len.
Proof. reflexivity. Qed.
Lemma pu_hCKS_length : forall c k o, length (pu_hCKS c k o) = pu_CKS_len.
Proof. reflexivity. Qed.
Lemma pu_hCKH_length : forall c o, length (pu_hCKH c o) = pu_CKH_len.
Proof. reflexivity. Qed.
Lemma pu_hCMS_length : forall sl o, length (pu_hCMS sl o) = pu_CMS_len.
Proof. reflexivity. Qed.
Lemma pu_hEQRS_length : forall c tgt o, length (pu_hEQRS c tgt o) = 16 * pu_EQR_len.
Proof. reflexivity. Qed.
Lemma pu_hCMH_length : forall c o, length (pu_hCMH c o) = pu_CMH_len.
Proof. reflexivity. Qed.
Lemma pu_hCERTH_length : forall o, length (pu_hCERTH o) = pu_CERTH_len.
Proof. reflexivity. Qed.
Lemma pu_hPAYH_length : forall o, length (pu_hPAYH o) = pu_PAYH_len.
Proof. reflexivity. Qed.

(* The label constants, as numbers. *)
Lemma pu_label_values :
  pu_L_HEAD = 1 /\ pu_L_HALT = 101 /\ pu_L_INC = 112 /\ pu_L_INCH E.CA = 120 /\ pu_L_INCH E.CB = 172 /\
  pu_L_DEC = 224 /\ pu_L_DECH E.CA = 252 /\ pu_L_DECH E.CB = 312 /\ pu_L_CHECK = 372 /\
  pu_L_CKH E.CA = 400 /\ pu_L_CKH E.CB = 1422 /\ pu_L_COMMIT = 2444 /\ pu_L_CMH E.CA = 2472 /\
  pu_L_CMH E.CB = 3100 /\ pu_L_CERT = 3728 /\ pu_L_PAY = 3732 /\ pu_L_STOP = 111 /\
  pu_U_len = 3735.
Proof. repeat split; reflexivity. Qed.

Lemma pu_block_len_values :
  pu_HEAD_len = 100 /\ pu_HALTB_len = 11 /\ pu_CD_len = 8 /\ pu_UCD_len = 28 /\ pu_BUMPS_len = 48 /\
  pu_INCH_len = 52 /\ pu_DECH_len = 60 /\ pu_CKS_len = 60 /\ pu_CKH_len = 1022 /\ pu_CMS_len = 5 /\
  pu_CMH_len = 628 /\ pu_CERTH_len = 4 /\ pu_PAYH_len = 4 /\ pu_EQR_len = 34 /\ pu_FETCH_len = 56 /\ pu_COPY_len = 11.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* U_P.                                                                 *)
(* ================================================================= *)

Definition pu_Usecs : list (list hinstr) :=
  [ pu_hHEAD pu_L_HEAD;
    pu_hHALTB pu_L_HALT;
    pu_hCD (pu_L_INCH E.CA) (pu_L_INCH E.CB) pu_L_INC;
    pu_hINCH E.CA (pu_L_INCH E.CA);
    pu_hINCH E.CB (pu_L_INCH E.CB);
    pu_hUCD (pu_L_DECH E.CA) (pu_L_DECH E.CB) pu_L_DEC;
    pu_hDECH E.CA (pu_L_DECH E.CA);
    pu_hDECH E.CB (pu_L_DECH E.CB);
    pu_hUCD (pu_L_CKH E.CA) (pu_L_CKH E.CB) pu_L_CHECK;
    pu_hCKH E.CA (pu_L_CKH E.CA);
    pu_hCKH E.CB (pu_L_CKH E.CB);
    pu_hUCD (pu_L_CMH E.CA) (pu_L_CMH E.CB) pu_L_COMMIT;
    pu_hCMH E.CA (pu_L_CMH E.CA);
    pu_hCMH E.CB (pu_L_CMH E.CB);
    pu_hCERTH pu_L_CERT;
    pu_hPAYH pu_L_PAY ].

Definition U_P : list hinstr := concat pu_Usecs.

Lemma pu_U_length : length U_P = pu_U_len.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Placement of the sections.                                         *)
(* ================================================================= *)

Lemma pu_concat_split : forall (secs : list (list hinstr)) i,
  concat secs = concat (firstn i secs) ++ nth i secs [] ++ concat (skipn (S i) secs).
Proof.
  induction secs as [| l secs IH]; intros [| i]; simpl; try reflexivity.
  rewrite (IH i), app_assoc. reflexivity.
Qed.

Lemma pu_sc_concat : forall (secs : list (list hinstr)) i,
  subcode (1 + length (concat (firstn i secs)), nth i secs []) (1, concat secs).
Proof.
  intros secs i. exists (concat (firstn i secs)), (concat (skipn (S i) secs)).
  split; [apply pu_concat_split | reflexivity].
Qed.

(* Place section number i at address a, after checking a by computation. *)
Ltac pu_place i :=
  let H := fresh in
  pose proof (pu_sc_concat pu_Usecs i) as H; cbn [nth pu_Usecs] in H;
  refine (pu_sc_pos _ _ _ _ _ H); vm_compute; reflexivity.

Lemma pu_U_HEAD : subcode (pu_L_HEAD, pu_hHEAD pu_L_HEAD) (1, U_P).
Proof. pu_place 0. Qed.
Lemma pu_U_HALTB : subcode (pu_L_HALT, pu_hHALTB pu_L_HALT) (1, U_P).
Proof. pu_place 1. Qed.
Lemma pu_U_INCD : subcode (pu_L_INC, pu_hCD (pu_L_INCH E.CA) (pu_L_INCH E.CB) pu_L_INC) (1, U_P).
Proof. pu_place 2. Qed.
Lemma pu_U_INCH : forall c, subcode (pu_L_INCH c, pu_hINCH c (pu_L_INCH c)) (1, U_P).
Proof. intros []; [pu_place 3 | pu_place 4]. Qed.
Lemma pu_U_DECD : subcode (pu_L_DEC, pu_hUCD (pu_L_DECH E.CA) (pu_L_DECH E.CB) pu_L_DEC) (1, U_P).
Proof. pu_place 5. Qed.
Lemma pu_U_DECH : forall c, subcode (pu_L_DECH c, pu_hDECH c (pu_L_DECH c)) (1, U_P).
Proof. intros []; [pu_place 6 | pu_place 7]. Qed.
Lemma pu_U_CKD : subcode (pu_L_CHECK, pu_hUCD (pu_L_CKH E.CA) (pu_L_CKH E.CB) pu_L_CHECK) (1, U_P).
Proof. pu_place 8. Qed.
Lemma pu_U_CKH : forall c, subcode (pu_L_CKH c, pu_hCKH c (pu_L_CKH c)) (1, U_P).
Proof. intros []; [pu_place 9 | pu_place 10]. Qed.
Lemma pu_U_CMD : subcode (pu_L_COMMIT, pu_hUCD (pu_L_CMH E.CA) (pu_L_CMH E.CB) pu_L_COMMIT) (1, U_P).
Proof. pu_place 11. Qed.
Lemma pu_U_CMH : forall c, subcode (pu_L_CMH c, pu_hCMH c (pu_L_CMH c)) (1, U_P).
Proof. intros []; [pu_place 12 | pu_place 13]. Qed.
Lemma pu_U_CERTH : subcode (pu_L_CERT, pu_hCERTH pu_L_CERT) (1, U_P).
Proof. pu_place 14. Qed.
Lemma pu_U_PAYH : subcode (pu_L_PAY, pu_hPAYH pu_L_PAY) (1, U_P).
Proof. pu_place 15. Qed.

(* Placement inside the per-bank handlers, once per family. *)
Lemma pu_U_BUMPS_inc : forall c, subcode (1 + pu_L_INCH c, pu_hBUMPS c (1 + pu_L_INCH c)) (1, U_P).
Proof.
  intro c. pose proof (pu_U_INCH c) as H. unfold pu_hINCH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. exact H3.
Qed.

Lemma pu_U_BUMPS_dec : forall c,
  subcode (pu_DECH_taken (pu_L_DECH c), pu_hBUMPS c (pu_DECH_taken (pu_L_DECH c))) (1, U_P).
Proof.
  intro c. pose proof (pu_U_DECH c) as H. unfold pu_hDECH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. pu_sc_split H6 H7 H8.
  pu_sc_split H8 H9 H10. exact H9.
Qed.

Lemma pu_U_CKH_slots : forall c,
  subcode (pu_CKH_slots (pu_L_CKH c), pu_fam (pu_hCKS c) pu_CKS_len 0 16 (pu_CKH_slots (pu_L_CKH c))) (1, U_P).
Proof.
  intro c. pose proof (pu_U_CKH c) as H. unfold pu_hCKH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. pu_sc_split H6 H7 H8. exact H8.
Qed.

Lemma pu_U_CKS : forall c k, k < 16 ->
  subcode (pu_CKS_at (pu_L_CKH c) k, pu_hCKS c k (pu_CKS_at (pu_L_CKH c) k)) (1, U_P).
Proof.
  intros c k Hk. eapply subcode_trans; [| apply pu_U_CKH_slots].
  apply (pu_fam_sub0 (pu_hCKS c) pu_CKS_len (pu_hCKS_length c) 16 (pu_CKH_slots (pu_L_CKH c)) k Hk).
Qed.

Lemma pu_U_CKH_dead : forall c, subcode (pu_CKH_dead (pu_L_CKH c), pu_hCHECK pu_DEAD (pu_CKH_dead (pu_L_CKH c))) (1, U_P).
Proof.
  intro c. pose proof (pu_U_CKH c) as H. unfold pu_hCKH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. exact H5.
Qed.

Lemma pu_U_EQRS : forall c, subcode (1 + pu_L_CMH c, pu_hEQRS c (pu_CMS_at (pu_L_CMH c)) (1 + pu_L_CMH c)) (1, U_P).
Proof.
  intro c. pose proof (pu_U_CMH c) as H. unfold pu_hCMH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. exact H3.
Qed.

Lemma pu_U_CMH_dead : forall c, subcode (pu_CMH_dead (pu_L_CMH c), pu_hCOMMIT pu_DEAD (pu_CMH_dead (pu_L_CMH c))) (1, U_P).
Proof.
  intro c. pose proof (pu_U_CMH c) as H. unfold pu_hCMH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. exact H5.
Qed.

Lemma pu_U_CMH_slots : forall c,
  subcode (pu_CMH_slots (pu_L_CMH c),
           pu_fam (fun k o' => pu_hCMS (pu_SLOT c k) o') pu_CMS_len 0 16 (pu_CMH_slots (pu_L_CMH c))) (1, U_P).
Proof.
  intro c. pose proof (pu_U_CMH c) as H. unfold pu_hCMH in H.
  pu_sc_split H H1 H2. pu_sc_split H2 H3 H4. pu_sc_split H4 H5 H6. pu_sc_split H6 H7 H8. exact H8.
Qed.

Lemma pu_U_CMS : forall c k, k < 16 ->
  subcode (pu_CMS_at (pu_L_CMH c) k, pu_hCMS (pu_SLOT c k) (pu_CMS_at (pu_L_CMH c) k)) (1, U_P).
Proof.
  intros c k Hk. eapply subcode_trans; [| apply pu_U_CMH_slots].
  apply (pu_fam_sub0 (fun k o' => pu_hCMS (pu_SLOT c k) o') pu_CMS_len
           (fun k o => pu_hCMS_length (pu_SLOT c k) o) 16 (pu_CMH_slots (pu_L_CMH c)) k Hk).
Qed.

(* The single HALT of U_P. *)
Lemma pu_U_fetch_stop : M.pu_fetch U_P pu_L_STOP = Some M.HALT.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Which instructions of U_P mention a register, and which cost.        *)
(* ================================================================= *)

(* The (address, instruction) pairs of a program, from address a on,
   whose instruction satisfies f. *)
Fixpoint pu_sites (f : hinstr -> bool) (l : list hinstr) (a : nat) : list (nat * hinstr) :=
  match l with
  | [] => []
  | i :: l' => if f i then (a, i) :: pu_sites f l' (S a) else pu_sites f l' (S a)
  end.

Lemma pu_sites_In : forall f l a pc i,
  In (pc, i) (pu_sites f l a) <->
  (exists q, nth_error l q = Some i /\ pc = a + q) /\ f i = true.
Proof.
  intros f l. induction l as [| x l IH]; intros a pc i; simpl.
  - split; [intros [] |]. intros [[q [Hq _]] _]. destruct q; discriminate.
  - destruct (f x) eqn:Ef; simpl; rewrite IH; split.
    + intros [Heq | [[q [Hq Hp]] Hf]].
      * inversion Heq; subst. split; [exists 0; split; [reflexivity | lia] | exact Ef].
      * split; [exists (S q); split; [exact Hq | lia] | exact Hf].
    + intros [[q [Hq Hp]] Hf]. destruct q as [| q].
      * left. simpl in Hq. inversion Hq. subst. f_equal. lia.
      * right. split; [exists q; split; [exact Hq | lia] | exact Hf].
    + intros [[q [Hq Hp]] Hf]. split; [exists (S q); split; [exact Hq | lia] | exact Hf].
    + intros [[q [Hq Hp]] Hf]. destruct q as [| q].
      * simpl in Hq. inversion Hq. subst. congruence.
      * split; [exists q; split; [exact Hq | lia] | exact Hf].
Qed.

Theorem pu_sites_fetch : forall f (Ph : list hinstr) pc i,
  In (pc, i) (pu_sites f Ph 1) <-> M.pu_fetch Ph pc = Some i /\ f i = true.
Proof.
  intros f Ph pc i. rewrite pu_sites_In. split.
  - intros [[q [Hq ->]] Hf]. simpl. auto.
  - intros [Hf Hi]. destruct pc as [| q]; [discriminate |].
    split; [exists q; split; [exact Hf | lia] | exact Hi].
Qed.

(* A BUMP at address a: INC r, then DEC r back to the next address. *)
Definition pu_bump_sites (a r : nat) : list (nat * hinstr) :=
  [(a, M.INC r); (S a, M.DEC r (S (S a)))].

(* The address of the INC into the slot inside pu_hCKS (the third
   instruction of its MOVE). *)
Definition pu_CKS_move (o : nat) : nat := 2 + 2 * pu_COPY_len + PACK_len + o.

(* Every instruction of U_P that mentions pu_SLOT c k, in address order. *)
Definition pu_slot_sites (c : E.ctr) (k : nat) : list (nat * hinstr) :=
  pu_bump_sites (1 + pu_L_INCH c + k * pu_BUMP_len) (pu_SLOT c k) ++
  pu_bump_sites (pu_DECH_taken (pu_L_DECH c) + k * pu_BUMP_len) (pu_SLOT c k) ++
  [(pu_CKS_move (pu_CKS_at (pu_L_CKH c) k), M.INC (pu_SLOT c k));
   (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) k), M.CHECK PSlot (pu_SLOT c k));
   (pu_CMS_at (pu_L_CMH c) k, M.COMMIT PSlot (pu_SLOT c k))].

Theorem pu_U_slot_sites : forall c k, k < 16 ->
  pu_sites (fun i => M.pu_mentions i (pu_SLOT c k)) U_P 1 = pu_slot_sites c k.
Proof.
  intros c k Hk.
  destruct c; do 16 (destruct k as [| k]; [vm_compute; reflexivity |]); lia.
Qed.

(* Every instruction of U_P that mentions pu_DEAD. *)
Definition pu_dead_sites : list (nat * hinstr) :=
  [(pu_CKH_dead (pu_L_CKH E.CA), M.CHECK PSlot pu_DEAD); (pu_CKH_dead (pu_L_CKH E.CB), M.CHECK PSlot pu_DEAD);
   (pu_CMH_dead (pu_L_CMH E.CA), M.COMMIT PSlot pu_DEAD); (pu_CMH_dead (pu_L_CMH E.CB), M.COMMIT PSlot pu_DEAD)].

Theorem pu_U_dead_sites : pu_sites (fun i => M.pu_mentions i pu_DEAD) U_P 1 = pu_dead_sites.
Proof. vm_compute. reflexivity. Qed.

Corollary pu_U_slot_mentions : forall c k pc i, k < 16 ->
  M.pu_fetch U_P pc = Some i -> M.pu_mentions i (pu_SLOT c k) = true -> In (pc, i) (pu_slot_sites c k).
Proof.
  intros c k pc i Hk Hf Hm. rewrite <- (pu_U_slot_sites c k Hk). apply pu_sites_fetch. auto.
Qed.

Corollary pu_U_slot_sites_fetch : forall c k pc i, k < 16 ->
  In (pc, i) (pu_slot_sites c k) -> M.pu_fetch U_P pc = Some i.
Proof.
  intros c k pc i Hk Hin. rewrite <- (pu_U_slot_sites c k Hk) in Hin.
  apply pu_sites_fetch in Hin. tauto.
Qed.

(* No instruction of U_P reads a slot: an INC writes it, CHECK and COMMIT
   leave it alone, and every DEC on a slot goes to the next address
   whether the slot holds 0 or not, right after an INC of the same slot. *)
Theorem pu_U_slot_dec_next : forall c k pc j, k < 16 ->
  M.pu_fetch U_P pc = Some (M.DEC (pu_SLOT c k) j) ->
  j = S pc /\ M.pu_fetch U_P (pc - 1) = Some (M.INC (pu_SLOT c k)) /\ 1 < pc.
Proof.
  intros c k pc j Hk Hf.
  assert (Hin : In (pc, M.DEC (pu_SLOT c k) j) (pu_slot_sites c k)).
  { apply pu_U_slot_mentions; [exact Hk | exact Hf | apply Nat.eqb_refl]. }
  unfold pu_slot_sites, pu_bump_sites in Hin. simpl in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | [E | []]]]]]]]; try discriminate E;
    inversion E; subst; (split; [reflexivity | split; [| lia]]);
    apply (pu_U_slot_sites_fetch c k _ _ Hk); unfold pu_slot_sites, pu_bump_sites; simpl;
    solve [ repeat (first [ left; f_equal; lia | right ]) ].
Qed.

Theorem pu_U_slot_kinds : forall c k pc i, k < 16 ->
  M.pu_fetch U_P pc = Some i -> M.pu_mentions i (pu_SLOT c k) = true ->
  i = M.INC (pu_SLOT c k) \/ i = M.DEC (pu_SLOT c k) (S pc) \/
  i = M.CHECK PSlot (pu_SLOT c k) \/ i = M.COMMIT PSlot (pu_SLOT c k).
Proof.
  intros c k pc i Hk Hf Hm. pose proof (pu_U_slot_mentions c k pc i Hk Hf Hm) as Hin.
  unfold pu_slot_sites, pu_bump_sites in Hin. simpl in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | [E | []]]]]]]]; inversion E; subst;
    first [ left; reflexivity | right; left; reflexivity
          | right; right; left; reflexivity | right; right; right; reflexivity ].
Qed.

(* The paid instructions of U_P: one CHECK per slot and one on pu_DEAD per
   bank, one COMMIT per slot and one on pu_DEAD per bank, one CERTIFY. *)
Definition pu_ck_paid (c : E.ctr) : list (nat * hinstr) :=
  (pu_CKH_dead (pu_L_CKH c), M.CHECK PSlot pu_DEAD) ::
  map (fun k => (pu_CKS_chk (pu_CKS_at (pu_L_CKH c) k), M.CHECK PSlot (pu_SLOT c k))) (seq 0 16).
Definition pu_cm_paid (c : E.ctr) : list (nat * hinstr) :=
  (pu_CMH_dead (pu_L_CMH c), M.COMMIT PSlot pu_DEAD) ::
  map (fun k => (pu_CMS_at (pu_L_CMH c) k, M.COMMIT PSlot (pu_SLOT c k))) (seq 0 16).
Definition pu_paid_sites : list (nat * hinstr) :=
  pu_ck_paid E.CA ++ pu_ck_paid E.CB ++ pu_cm_paid E.CA ++ pu_cm_paid E.CB ++
  [(pu_L_CERT, M.CERTIFY); (pu_L_PAY, M.PAY)].

Lemma pu_paid_sites_length : length pu_paid_sites = 70.
Proof. reflexivity. Qed.

Theorem pu_U_paid_sites : pu_sites (fun i => Nat.eqb (M.pu_cost i) 1) U_P 1 = pu_paid_sites.
Proof. vm_compute. reflexivity. Qed.

Lemma pu_cost_le_1 : forall i : hinstr, M.pu_cost i <= 1.
Proof. intros []; simpl; lia. Qed.

Corollary pu_U_paid : forall pc i, M.pu_fetch U_P pc = Some i ->
  M.pu_cost i = 1 <-> In (pc, i) pu_paid_sites.
Proof.
  intros pc i Hf. rewrite <- pu_U_paid_sites, pu_sites_fetch. split.
  - intro H. split; [exact Hf | apply Nat.eqb_eq, H].
  - intros [_ H]. apply Nat.eqb_eq, H.
Qed.

Corollary pu_U_free : forall pc i, M.pu_fetch U_P pc = Some i ->
  ~ In (pc, i) pu_paid_sites -> M.pu_cost i = 0.
Proof.
  intros pc i Hf Hn. pose proof (pu_cost_le_1 i) as H.
  destruct (M.pu_cost i) as [| [| m]] eqn:Ec; [reflexivity | | lia].
  exfalso. apply Hn. apply (pu_U_paid pc i Hf). exact Ec.
Qed.

(* The only HALT of U_P is at pu_L_STOP. *)
Definition pu_is_halt (i : hinstr) : bool := match i with M.HALT => true | _ => false end.

Theorem pu_U_halt_sites : pu_sites pu_is_halt U_P 1 = [(pu_L_STOP, M.HALT)].
Proof. vm_compute. reflexivity. Qed.

(* U_P mentions no register above pu_DEAD. *)
Definition pu_ireg (i : hinstr) : option nat :=
  match i with
  | M.INC r | M.DEC r _ | M.CHECK _ r | M.COMMIT _ r => Some r
  | M.HALT | M.CERTIFY | M.PAY => None
  end.

Lemma pu_mentions_ireg : forall (i : hinstr) r, M.pu_mentions i r = true <-> pu_ireg i = Some r.
Proof.
  intros [d | d j | | p d | p d | |] r; simpl;
    try (split; intro H; discriminate);
    (rewrite Nat.eqb_eq; split; intro H; [subst; reflexivity | inversion H; reflexivity]).
Qed.

Theorem pu_U_regs_bound : forall pc i r, M.pu_fetch U_P pc = Some i -> M.pu_mentions i r = true -> r <= pu_DEAD.
Proof.
  intros pc i r Hf Hm. apply pu_mentions_ireg in Hm.
  assert (Hall : forallb (fun i => match pu_ireg i with Some r => r <=? pu_DEAD | None => true end) U_P
                 = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. destruct pc as [| q]; [discriminate |].
  simpl in Hf. specialize (Hall i (nth_error_In U_P q Hf)). rewrite Hm in Hall.
  apply Nat.leb_le, Hall.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_fam_sub0.
Print Assumptions pu_label_values.
Print Assumptions pu_U_length.
Print Assumptions pu_U_HEAD.
Print Assumptions pu_U_HALTB.
Print Assumptions pu_U_INCH.
Print Assumptions pu_U_DECH.
Print Assumptions pu_U_CKH.
Print Assumptions pu_U_CMH.
Print Assumptions pu_U_CERTH.
Print Assumptions pu_U_PAYH.
Print Assumptions pu_U_BUMPS_inc.
Print Assumptions pu_U_BUMPS_dec.
Print Assumptions pu_U_CKS.
Print Assumptions pu_U_CKH_dead.
Print Assumptions pu_U_EQRS.
Print Assumptions pu_U_CMH_dead.
Print Assumptions pu_U_CMS.
Print Assumptions pu_U_fetch_stop.
Print Assumptions pu_sites_fetch.
Print Assumptions pu_U_slot_sites.
Print Assumptions pu_U_dead_sites.
Print Assumptions pu_U_slot_dec_next.
Print Assumptions pu_U_slot_kinds.
Print Assumptions pu_U_paid_sites.
Print Assumptions pu_U_paid.
Print Assumptions pu_U_free.
Print Assumptions pu_U_halt_sites.
Print Assumptions pu_U_regs_bound.

(** UniversalLayout.v: the fixed host program U of the universal
    interpreter, as one concrete list of host instructions.

    U is built from the blocks of UniversalBlocks.v. It starts at host
    address 1. Its registers:

      RA = 0, RB = 1          the guest counters (greg CA = RA, greg CB = RB)
      PROG = 2                the code of the guest program
      GPC = 3                 the guest pc
      T0 .. T9 = 4 .. 13      scratch
      NC c = 14 + ccode c     how many CHECK moves on counter c passed
      MP c k = 16 + 16 ccode c + k    mirror of slot k of bank c
                              (claim code + 1 when the slot is live, else 0)
      SLOT c k = 48 + 16 ccode c + k  slot k of bank c, the fact holders
      DEAD = 80               never written; a record move on it fails

    Sections of U, each at a named address:

      L_HEAD  (address 1)  fetch the current guest instruction, split its
                           code into opcode and operand, jump to the
                           opcode's handler; guest pc 0 or past the end
                           goes to L_HALT
      L_HALT               clear the scratch registers, then HALT
      L_INC                choose the bank; L_INCH c: INC (greg c), bump
                           every slot of bank c, INC GPC, back to L_HEAD
      L_DEC                split the operand into bank and target;
                           L_DECH c: DEC (greg c); on 0, INC GPC; else bump
                           every slot of bank c and set GPC to the target
      L_CHECK              split the operand into bank and property code;
                           L_CKH c: a 17-way branch on NC c; for k < 16 the
                           block hCKS c k packs (property code, value of
                           greg c) into SLOT c k, runs CHECK PSlot (SLOT c k),
                           sets MP c k := code + 1, INC NC c, INC GPC; for
                           NC c >= 16 it runs CHECK PSlot DEAD
      L_COMMIT             split the operand; L_CMH c: compare MP c k with
                           code + 1 for k = 0 .. 15 (EQR); the first match
                           runs COMMIT PSlot (SLOT c k); no match runs
                           COMMIT PSlot DEAD
      L_CERT               CERTIFY, INC GPC, back to L_HEAD

    Proved here: the length of every block, the value of every label, the
    placement (subcode) of every section and of every per-(c, k) block in
    U, proved once per family; the exact list of instructions of U that
    mention SLOT c k (two bumps, the move into the slot, its CHECK and its
    COMMIT), that every DEC on a slot jumps to the next address whatever
    the slot holds, the exact list of instructions that mention DEAD, the
    exact list of instructions that cost anything (CHECK, COMMIT and
    CERTIFY sites, 69 of them), the single HALT, and that U mentions no
    register above DEAD.

    Dependencies: the Coq standard library, the vendored coq-undecidability
    library, EarnedCore.v, EarnedGeneric.v, EarnedMulti.v,
    UniversalCodes.v, UniversalBridge.v and UniversalBlocks.v. No axioms,
    no Admitted.                                                          *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter of UniversalRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and the standard-library files under minimal/. Its link to the
   abstract record (the host as a CertificationSystem, the undecidability
   of U's halting problem, and the agreement with complete_cs) lives in
   UniversalInterpreterLinks.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Undecidability.Shared.Libs.DLW Require Import Vec.pos Vec.vec Code.subcode Code.sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.Util Require Import MMA_pairing.
Require Import Minimal.UniversalCodes Kernel.UniversalBridge Kernel.UniversalBlocks.

Local Notation hinstr := (@M.instr hprop).

(* ================================================================= *)
(* Registers.                                                         *)
(* ================================================================= *)

(* SAFE: register number 0 is where the guest's counter A lives, as
   register 0 of the host machine; it is an address, not a placeholder. *)
Definition RA : nat := 0.
Definition RB : nat := 1.
Definition PROG : nat := 2.
Definition GPC : nat := 3.
Definition T0 : nat := 4.
Definition T1 : nat := 5.
Definition T2 : nat := 6.
Definition T3 : nat := 7.
Definition T4 : nat := 8.
Definition T5 : nat := 9.
Definition T6 : nat := 10.
Definition T7 : nat := 11.
Definition T8 : nat := 12.
Definition T9 : nat := 13.
Definition greg (c : E.ctr) : nat := ccode c.
Definition NC (c : E.ctr) : nat := 14 + ccode c.
Definition MP (c : E.ctr) (k : nat) : nat := 16 + 16 * ccode c + k.
Definition SLOT (c : E.ctr) (k : nat) : nat := 48 + 16 * ccode c + k.
Definition DEAD : nat := 80.

Definition scratch (r : nat) : Prop := 4 <= r < 14.
Definition in_mp (c : E.ctr) (r : nat) : Prop := 16 + 16 * ccode c <= r < 32 + 16 * ccode c.
Definition in_slots (c : E.ctr) (r : nat) : Prop := 48 + 16 * ccode c <= r < 64 + 16 * ccode c.

Lemma greg_CA : greg E.CA = RA. Proof. reflexivity. Qed.
Lemma greg_CB : greg E.CB = RB. Proof. reflexivity. Qed.

Lemma scratch_cases : forall r, scratch r ->
  r = T0 \/ r = T1 \/ r = T2 \/ r = T3 \/ r = T4 \/
  r = T5 \/ r = T6 \/ r = T7 \/ r = T8 \/ r = T9.
Proof.
  intros r H. unfold scratch in H.
  unfold T0, T1, T2, T3, T4, T5, T6, T7, T8, T9. lia.
Qed.

Lemma in_mp_MP : forall c k, k < 16 -> in_mp c (MP c k).
Proof. intros c k Hk. unfold in_mp, MP. lia. Qed.

Lemma in_slots_SLOT : forall c k, k < 16 -> in_slots c (SLOT c k).
Proof. intros c k Hk. unfold in_slots, SLOT. lia. Qed.

Lemma in_mp_inv : forall c r, in_mp c r -> exists k, k < 16 /\ r = MP c k.
Proof. intros c r H. unfold in_mp in H. exists (r - (16 + 16 * ccode c)). unfold MP. lia. Qed.

Lemma in_slots_inv : forall c r, in_slots c r -> exists k, k < 16 /\ r = SLOT c k.
Proof.
  intros c r H. unfold in_slots in H. exists (r - (48 + 16 * ccode c)). unfold SLOT. lia.
Qed.

(* ================================================================= *)
(* Families of blocks placed one after another.                       *)
(* ================================================================= *)

(* fam f len k n o: the blocks f k, f (k+1), ..., f (k+n-1), each of
   length len, the first at address o. *)
Fixpoint fam (f : nat -> nat -> list hinstr) (len k n o : nat) : list hinstr :=
  match n with
  | 0 => []
  | S n' => f k o ++ fam f len (S k) n' (len + o)
  end.

Lemma fam_length : forall f len, (forall k o, length (f k o) = len) ->
  forall n k o, length (fam f len k n o) = n * len.
Proof.
  intros f len Hl n. induction n as [| n IH]; intros k o; [reflexivity |].
  simpl. rewrite app_length, Hl, IH. reflexivity.
Qed.

Lemma fam_sub : forall f len, (forall k o, length (f k o) = len) ->
  forall n k0 o k, k0 <= k -> k < k0 + n ->
  subcode (o + (k - k0) * len, f k (o + (k - k0) * len)) (o, fam f len k0 n o).
Proof.
  intros f len Hl n. induction n as [| n IH]; intros k0 o k H1 H2; [lia |].
  cbn [fam]. destruct (Nat.eq_dec k k0) as [-> | Hne].
  - rewrite Nat.sub_diag, Nat.mul_0_l, Nat.add_0_r. apply subcode_left. reflexivity.
  - apply subcode_trans with (Q := (len + o, fam f len (S k0) n (len + o))).
    + replace (o + (k - k0) * len) with (len + o + (k - S k0) * len).
      * apply IH; lia.
      * replace (k - k0) with (S (k - S k0)) by lia. simpl. lia.
    + apply subcode_right. rewrite Hl. lia.
Qed.

Corollary fam_sub0 : forall f len, (forall k o, length (f k o) = len) ->
  forall n o k, k < n -> subcode (o + k * len, f k (o + k * len)) (o, fam f len 0 n o).
Proof.
  intros f len Hl n o k Hk. pose proof (fam_sub f len Hl n 0 o k (Nat.le_0_l k) Hk) as H.
  rewrite Nat.sub_0_r in H. exact H.
Qed.

(* ================================================================= *)
(* Lengths, offsets and labels.                                       *)
(* ================================================================= *)

Definition HEAD_len : nat := FETCH_len + 1 + UNPACK_len + 3 * 6 + JMP_len.
Definition HALTB_len : nat := 11.
Definition CD_len : nat := 3 * 2 + JMP_len.
Definition UCD_len : nat := UNPACK_len + 3 * 2 + JMP_len.
Definition BUMPS_len : nat := 16 * BUMP_len.
Definition INCH_len : nat := 2 + BUMPS_len + JMP_len.
Definition DECH_len : nat := 5 + BUMPS_len + 1 + MOVE_len + JMP_len.
Definition CKS_len : nat := 2 * COPY_len + PACK_len + MOVE_len + 2 + MOVE_len + 3 + JMP_len.
Definition CKH_len : nat := COPY_len + 3 * 16 + 1 + JMP_len + 16 * CKS_len.
Definition CMS_len : nat := 3 + JMP_len.
Definition CMH_len : nat := 1 + 16 * EQR_len + 1 + JMP_len + 16 * CMS_len.
Definition CERTH_len : nat := 2 + JMP_len.

(* Offsets inside the per-bank handlers. *)
Definition DECH_taken (o : nat) : nat := 5 + o.
Definition CKS_chk (o : nat) : nat := 2 * COPY_len + PACK_len + MOVE_len + o.
Definition CKH_dead (o : nat) : nat := COPY_len + 3 * 16 + o.
Definition CKH_slots (o : nat) : nat := COPY_len + 3 * 16 + 1 + JMP_len + o.
Definition CKS_at (o k : nat) : nat := CKH_slots o + k * CKS_len.
Definition CMH_dead (o : nat) : nat := 1 + 16 * EQR_len + o.
Definition CMH_slots (o : nat) : nat := 1 + 16 * EQR_len + 1 + JMP_len + o.
Definition CMS_at (o k : nat) : nat := CMH_slots o + k * CMS_len.

(* Labels. *)
Definition L_HEAD : nat := 1.
Definition L_HALT : nat := L_HEAD + HEAD_len.
Definition L_INC : nat := L_HALT + HALTB_len.
Definition L_INCH (c : E.ctr) : nat := L_INC + CD_len + ccode c * INCH_len.
Definition L_DEC : nat := L_INC + CD_len + 2 * INCH_len.
Definition L_DECH (c : E.ctr) : nat := L_DEC + UCD_len + ccode c * DECH_len.
Definition L_CHECK : nat := L_DEC + UCD_len + 2 * DECH_len.
Definition L_CKH (c : E.ctr) : nat := L_CHECK + UCD_len + ccode c * CKH_len.
Definition L_COMMIT : nat := L_CHECK + UCD_len + 2 * CKH_len.
Definition L_CMH (c : E.ctr) : nat := L_COMMIT + UCD_len + ccode c * CMH_len.
Definition L_CERT : nat := L_COMMIT + UCD_len + 2 * CMH_len.
Definition L_STOP : nat := L_HALT + 10.
Definition U_len : nat := L_CERT + CERTH_len - 1.

(* The handler address of each guest opcode. *)
Definition op_of (i : E.instr) : nat :=
  match i with
  | E.INC _ => 0 | E.DEC _ _ => 1 | E.HALT => 2
  | E.CHECK _ _ => 3 | E.COMMIT _ _ => 4 | E.CERTIFY => 5
  end.
Definition arg_of (i : E.instr) : nat :=
  match i with
  | E.INC c => ccode c
  | E.DEC c j => pair (ccode c) j
  | E.HALT => 0
  | E.CHECK p c => pair (ccode c) (pcode p)
  | E.COMMIT p c => pair (ccode c) (pcode p)
  | E.CERTIFY => 0
  end.
Definition handlers : list nat := [L_INC; L_DEC; L_HALT; L_CHECK; L_COMMIT; L_CERT].
Definition handler (i : E.instr) : nat := nth (op_of i) handlers 0.

Lemma icode_op_arg : forall i, icode i = pair (op_of i) (arg_of i).
Proof. intros []; reflexivity. Qed.

Lemma op_of_lt : forall i, op_of i < length handlers.
Proof. intros []; simpl; lia. Qed.

(* ================================================================= *)
(* The blocks of U.                                                   *)
(* ================================================================= *)

(* HEAD: fetch, split the code, dispatch on the opcode. *)
Definition hHEAD (o : nat) : list hinstr :=
  hFETCH PROG GPC T0 T1 T2 T3 T4 L_HALT L_HALT o ++
  hZERO T0 (FETCH_len + o) ++
  hUNPACK T3 T2 T5 (1 + FETCH_len + o) ++
  hDISP T5 T4 handlers (1 + FETCH_len + UNPACK_len + o) ++
  hJMP T4 L_HALT (3 * 6 + 1 + FETCH_len + UNPACK_len + o).

(* HALT: clear the scratch registers, then stop. *)
Definition hHALTB (o : nat) : list hinstr :=
  hZERO T0 o ++ hZERO T1 (1 + o) ++ hZERO T2 (2 + o) ++ hZERO T3 (3 + o) ++
  hZERO T4 (4 + o) ++ hZERO T5 (5 + o) ++ hZERO T6 (6 + o) ++ hZERO T7 (7 + o) ++
  hZERO T8 (8 + o) ++ hZERO T9 (9 + o) ++ [M.HALT].

(* Bank choice on T2 = ccode c. *)
Definition hCD (ta tb o : nat) : list hinstr :=
  hDISP T2 T4 [ta; tb] o ++ hJMP T4 L_HALT (3 * 2 + o).

(* Split T2 = pair (ccode c) x into T2 := x, T6 := ccode c; bank choice
   on T6. *)
Definition hUCD (ta tb o : nat) : list hinstr :=
  hUNPACK T3 T2 T6 o ++ hDISP T6 T4 [ta; tb] (UNPACK_len + o) ++
  hJMP T4 L_HALT (3 * 2 + UNPACK_len + o).

(* BUMP every slot of bank c. *)
Definition hBUMPS (c : E.ctr) (o : nat) : list hinstr :=
  fam (fun k o' => hBUMP (SLOT c k) (MP c k) o') BUMP_len 0 16 o.

Definition hINCH (c : E.ctr) (o : nat) : list hinstr :=
  hINC (greg c) o ++ hBUMPS c (1 + o) ++ hINC GPC (1 + BUMPS_len + o) ++
  hJMP T4 L_HEAD (2 + BUMPS_len + o).

Definition hDECH (c : E.ctr) (o : nat) : list hinstr :=
  hDEC (greg c) (DECH_taken o) o ++ hINC GPC (1 + o) ++ hZERO T2 (2 + o) ++
  hJMP T4 L_HEAD (3 + o) ++
  hBUMPS c (DECH_taken o) ++ hZERO GPC (BUMPS_len + DECH_taken o) ++
  hMOVE T2 GPC (1 + BUMPS_len + DECH_taken o) ++
  hJMP T4 L_HEAD (1 + MOVE_len + BUMPS_len + DECH_taken o).

(* Slot k of bank c: load the claim into the slot and check it. *)
Definition hCKS (c : E.ctr) (k o : nat) : list hinstr :=
  hCOPY (greg c) T8 T4 o ++
  hCOPY T2 T9 T4 (COPY_len + o) ++
  hPACK T3 T8 T9 (2 * COPY_len + o) ++
  hMOVE T8 (SLOT c k) (2 * COPY_len + PACK_len + o) ++
  hCHECK (SLOT c k) (CKS_chk o) ++
  hZERO (MP c k) (1 + CKS_chk o) ++
  hMOVE T2 (MP c k) (2 + CKS_chk o) ++
  hINC (MP c k) (2 + MOVE_len + CKS_chk o) ++
  hINC (NC c) (3 + MOVE_len + CKS_chk o) ++
  hINC GPC (4 + MOVE_len + CKS_chk o) ++
  hJMP T4 L_HEAD (5 + MOVE_len + CKS_chk o).

Definition hCKH (c : E.ctr) (o : nat) : list hinstr :=
  hCOPY (NC c) T7 T4 o ++
  hDISP T7 T4 (map (CKS_at o) (seq 0 16)) (COPY_len + o) ++
  hCHECK DEAD (CKH_dead o) ++
  hJMP T4 L_HALT (1 + CKH_dead o) ++
  fam (hCKS c) CKS_len 0 16 (CKH_slots o).

(* Commit from slot sl. *)
Definition hCMS (sl o : nat) : list hinstr :=
  hCOMMIT sl o ++ hZERO T2 (1 + o) ++ hINC GPC (2 + o) ++ hJMP T4 L_HEAD (3 + o).

Definition hEQRS (c : E.ctr) (tgt : nat -> nat) (o : nat) : list hinstr :=
  fam (fun k o' => hEQR (MP c k) T2 T7 T8 T4 (tgt k) o') EQR_len 0 16 o.

Definition hCMH (c : E.ctr) (o : nat) : list hinstr :=
  hINC T2 o ++
  hEQRS c (CMS_at o) (1 + o) ++
  hCOMMIT DEAD (CMH_dead o) ++
  hJMP T4 L_HALT (1 + CMH_dead o) ++
  fam (fun k o' => hCMS (SLOT c k) o') CMS_len 0 16 (CMH_slots o).

Definition hCERTH (o : nat) : list hinstr :=
  hCERTIFY o ++ hINC GPC (1 + o) ++ hJMP T4 L_HEAD (2 + o).

(* ================================================================= *)
(* Block lengths.                                                     *)
(* ================================================================= *)

Lemma hHEAD_length : forall o, length (hHEAD o) = HEAD_len.
Proof. reflexivity. Qed.
Lemma hHALTB_length : forall o, length (hHALTB o) = HALTB_len.
Proof. reflexivity. Qed.
Lemma hCD_length : forall ta tb o, length (hCD ta tb o) = CD_len.
Proof. reflexivity. Qed.
Lemma hUCD_length : forall ta tb o, length (hUCD ta tb o) = UCD_len.
Proof. reflexivity. Qed.
Lemma hBUMPS_length : forall c o, length (hBUMPS c o) = BUMPS_len.
Proof. reflexivity. Qed.
Lemma hINCH_length : forall c o, length (hINCH c o) = INCH_len.
Proof. reflexivity. Qed.
Lemma hDECH_length : forall c o, length (hDECH c o) = DECH_len.
Proof. reflexivity. Qed.
Lemma hCKS_length : forall c k o, length (hCKS c k o) = CKS_len.
Proof. reflexivity. Qed.
Lemma hCKH_length : forall c o, length (hCKH c o) = CKH_len.
Proof. reflexivity. Qed.
Lemma hCMS_length : forall sl o, length (hCMS sl o) = CMS_len.
Proof. reflexivity. Qed.
Lemma hEQRS_length : forall c tgt o, length (hEQRS c tgt o) = 16 * EQR_len.
Proof. reflexivity. Qed.
Lemma hCMH_length : forall c o, length (hCMH c o) = CMH_len.
Proof. reflexivity. Qed.
Lemma hCERTH_length : forall o, length (hCERTH o) = CERTH_len.
Proof. reflexivity. Qed.

(* The label constants, as numbers. *)
Lemma label_values :
  L_HEAD = 1 /\ L_HALT = 98 /\ L_INC = 109 /\ L_INCH E.CA = 117 /\ L_INCH E.CB = 169 /\
  L_DEC = 221 /\ L_DECH E.CA = 249 /\ L_DECH E.CB = 309 /\ L_CHECK = 369 /\
  L_CKH E.CA = 397 /\ L_CKH E.CB = 1419 /\ L_COMMIT = 2441 /\ L_CMH E.CA = 2469 /\
  L_CMH E.CB = 3097 /\ L_CERT = 3725 /\ L_STOP = 108 /\ U_len = 3728.
Proof. repeat split; reflexivity. Qed.

Lemma block_len_values :
  HEAD_len = 97 /\ HALTB_len = 11 /\ CD_len = 8 /\ UCD_len = 28 /\ BUMPS_len = 48 /\
  INCH_len = 52 /\ DECH_len = 60 /\ CKS_len = 60 /\ CKH_len = 1022 /\ CMS_len = 5 /\
  CMH_len = 628 /\ CERTH_len = 4 /\ EQR_len = 34 /\ FETCH_len = 56 /\ COPY_len = 11.
Proof. repeat split; reflexivity. Qed.

(* ================================================================= *)
(* U.                                                                 *)
(* ================================================================= *)

Definition Usecs : list (list hinstr) :=
  [ hHEAD L_HEAD;
    hHALTB L_HALT;
    hCD (L_INCH E.CA) (L_INCH E.CB) L_INC;
    hINCH E.CA (L_INCH E.CA);
    hINCH E.CB (L_INCH E.CB);
    hUCD (L_DECH E.CA) (L_DECH E.CB) L_DEC;
    hDECH E.CA (L_DECH E.CA);
    hDECH E.CB (L_DECH E.CB);
    hUCD (L_CKH E.CA) (L_CKH E.CB) L_CHECK;
    hCKH E.CA (L_CKH E.CA);
    hCKH E.CB (L_CKH E.CB);
    hUCD (L_CMH E.CA) (L_CMH E.CB) L_COMMIT;
    hCMH E.CA (L_CMH E.CA);
    hCMH E.CB (L_CMH E.CB);
    hCERTH L_CERT ].

Definition U : list hinstr := concat Usecs.

Lemma U_length : length U = U_len.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Placement of the sections.                                         *)
(* ================================================================= *)

Lemma concat_split : forall (secs : list (list hinstr)) i,
  concat secs = concat (firstn i secs) ++ nth i secs [] ++ concat (skipn (S i) secs).
Proof.
  induction secs as [| l secs IH]; intros [| i]; simpl; try reflexivity.
  rewrite (IH i), app_assoc. reflexivity.
Qed.

Lemma sc_concat : forall (secs : list (list hinstr)) i,
  subcode (1 + length (concat (firstn i secs)), nth i secs []) (1, concat secs).
Proof.
  intros secs i. exists (concat (firstn i secs)), (concat (skipn (S i) secs)).
  split; [apply concat_split | reflexivity].
Qed.

(* Place section number i at address a, after checking a by computation. *)
Ltac place i :=
  let H := fresh in
  pose proof (sc_concat Usecs i) as H; cbn [nth Usecs] in H;
  refine (sc_pos _ _ _ _ _ H); vm_compute; reflexivity.

Lemma U_HEAD : subcode (L_HEAD, hHEAD L_HEAD) (1, U).
Proof. place 0. Qed.
Lemma U_HALTB : subcode (L_HALT, hHALTB L_HALT) (1, U).
Proof. place 1. Qed.
Lemma U_INCD : subcode (L_INC, hCD (L_INCH E.CA) (L_INCH E.CB) L_INC) (1, U).
Proof. place 2. Qed.
Lemma U_INCH : forall c, subcode (L_INCH c, hINCH c (L_INCH c)) (1, U).
Proof. intros []; [place 3 | place 4]. Qed.
Lemma U_DECD : subcode (L_DEC, hUCD (L_DECH E.CA) (L_DECH E.CB) L_DEC) (1, U).
Proof. place 5. Qed.
Lemma U_DECH : forall c, subcode (L_DECH c, hDECH c (L_DECH c)) (1, U).
Proof. intros []; [place 6 | place 7]. Qed.
Lemma U_CKD : subcode (L_CHECK, hUCD (L_CKH E.CA) (L_CKH E.CB) L_CHECK) (1, U).
Proof. place 8. Qed.
Lemma U_CKH : forall c, subcode (L_CKH c, hCKH c (L_CKH c)) (1, U).
Proof. intros []; [place 9 | place 10]. Qed.
Lemma U_CMD : subcode (L_COMMIT, hUCD (L_CMH E.CA) (L_CMH E.CB) L_COMMIT) (1, U).
Proof. place 11. Qed.
Lemma U_CMH : forall c, subcode (L_CMH c, hCMH c (L_CMH c)) (1, U).
Proof. intros []; [place 12 | place 13]. Qed.
Lemma U_CERTH : subcode (L_CERT, hCERTH L_CERT) (1, U).
Proof. place 14. Qed.

(* Placement inside the per-bank handlers, once per family. *)
Lemma U_BUMPS_inc : forall c, subcode (1 + L_INCH c, hBUMPS c (1 + L_INCH c)) (1, U).
Proof.
  intro c. pose proof (U_INCH c) as H. unfold hINCH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. exact H3.
Qed.

Lemma U_BUMPS_dec : forall c,
  subcode (DECH_taken (L_DECH c), hBUMPS c (DECH_taken (L_DECH c))) (1, U).
Proof.
  intro c. pose proof (U_DECH c) as H. unfold hDECH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. sc_split H6 H7 H8.
  sc_split H8 H9 H10. exact H9.
Qed.

Lemma U_CKH_slots : forall c,
  subcode (CKH_slots (L_CKH c), fam (hCKS c) CKS_len 0 16 (CKH_slots (L_CKH c))) (1, U).
Proof.
  intro c. pose proof (U_CKH c) as H. unfold hCKH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. sc_split H6 H7 H8. exact H8.
Qed.

Lemma U_CKS : forall c k, k < 16 ->
  subcode (CKS_at (L_CKH c) k, hCKS c k (CKS_at (L_CKH c) k)) (1, U).
Proof.
  intros c k Hk. eapply subcode_trans; [| apply U_CKH_slots].
  apply (fam_sub0 (hCKS c) CKS_len (hCKS_length c) 16 (CKH_slots (L_CKH c)) k Hk).
Qed.

Lemma U_CKH_dead : forall c, subcode (CKH_dead (L_CKH c), hCHECK DEAD (CKH_dead (L_CKH c))) (1, U).
Proof.
  intro c. pose proof (U_CKH c) as H. unfold hCKH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. exact H5.
Qed.

Lemma U_EQRS : forall c, subcode (1 + L_CMH c, hEQRS c (CMS_at (L_CMH c)) (1 + L_CMH c)) (1, U).
Proof.
  intro c. pose proof (U_CMH c) as H. unfold hCMH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. exact H3.
Qed.

Lemma U_CMH_dead : forall c, subcode (CMH_dead (L_CMH c), hCOMMIT DEAD (CMH_dead (L_CMH c))) (1, U).
Proof.
  intro c. pose proof (U_CMH c) as H. unfold hCMH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. exact H5.
Qed.

Lemma U_CMH_slots : forall c,
  subcode (CMH_slots (L_CMH c),
           fam (fun k o' => hCMS (SLOT c k) o') CMS_len 0 16 (CMH_slots (L_CMH c))) (1, U).
Proof.
  intro c. pose proof (U_CMH c) as H. unfold hCMH in H.
  sc_split H H1 H2. sc_split H2 H3 H4. sc_split H4 H5 H6. sc_split H6 H7 H8. exact H8.
Qed.

Lemma U_CMS : forall c k, k < 16 ->
  subcode (CMS_at (L_CMH c) k, hCMS (SLOT c k) (CMS_at (L_CMH c) k)) (1, U).
Proof.
  intros c k Hk. eapply subcode_trans; [| apply U_CMH_slots].
  apply (fam_sub0 (fun k o' => hCMS (SLOT c k) o') CMS_len
           (fun k o => hCMS_length (SLOT c k) o) 16 (CMH_slots (L_CMH c)) k Hk).
Qed.

(* The single HALT of U. *)
Lemma U_fetch_stop : M.fetch U L_STOP = Some M.HALT.
Proof. vm_compute. reflexivity. Qed.

(* ================================================================= *)
(* Which instructions of U mention a register, and which cost.        *)
(* ================================================================= *)

(* The (address, instruction) pairs of a program, from address a on,
   whose instruction satisfies f. *)
Fixpoint sites (f : hinstr -> bool) (l : list hinstr) (a : nat) : list (nat * hinstr) :=
  match l with
  | [] => []
  | i :: l' => if f i then (a, i) :: sites f l' (S a) else sites f l' (S a)
  end.

Lemma sites_In : forall f l a pc i,
  In (pc, i) (sites f l a) <->
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

Theorem sites_fetch : forall f (Ph : list hinstr) pc i,
  In (pc, i) (sites f Ph 1) <-> M.fetch Ph pc = Some i /\ f i = true.
Proof.
  intros f Ph pc i. rewrite sites_In. split.
  - intros [[q [Hq ->]] Hf]. simpl. auto.
  - intros [Hf Hi]. destruct pc as [| q]; [discriminate |].
    split; [exists q; split; [exact Hf | lia] | exact Hi].
Qed.

(* A BUMP at address a: INC r, then DEC r back to the next address. *)
Definition bump_sites (a r : nat) : list (nat * hinstr) :=
  [(a, M.INC r); (S a, M.DEC r (S (S a)))].

(* The address of the INC into the slot inside hCKS (the third
   instruction of its MOVE). *)
Definition CKS_move (o : nat) : nat := 2 + 2 * COPY_len + PACK_len + o.

(* Every instruction of U that mentions SLOT c k, in address order. *)
Definition slot_sites (c : E.ctr) (k : nat) : list (nat * hinstr) :=
  bump_sites (1 + L_INCH c + k * BUMP_len) (SLOT c k) ++
  bump_sites (DECH_taken (L_DECH c) + k * BUMP_len) (SLOT c k) ++
  [(CKS_move (CKS_at (L_CKH c) k), M.INC (SLOT c k));
   (CKS_chk (CKS_at (L_CKH c) k), M.CHECK PSlot (SLOT c k));
   (CMS_at (L_CMH c) k, M.COMMIT PSlot (SLOT c k))].

Theorem U_slot_sites : forall c k, k < 16 ->
  sites (fun i => M.mentions i (SLOT c k)) U 1 = slot_sites c k.
Proof.
  intros c k Hk.
  destruct c; do 16 (destruct k as [| k]; [vm_compute; reflexivity |]); lia.
Qed.

(* Every instruction of U that mentions DEAD. *)
Definition dead_sites : list (nat * hinstr) :=
  [(CKH_dead (L_CKH E.CA), M.CHECK PSlot DEAD); (CKH_dead (L_CKH E.CB), M.CHECK PSlot DEAD);
   (CMH_dead (L_CMH E.CA), M.COMMIT PSlot DEAD); (CMH_dead (L_CMH E.CB), M.COMMIT PSlot DEAD)].

Theorem U_dead_sites : sites (fun i => M.mentions i DEAD) U 1 = dead_sites.
Proof. vm_compute. reflexivity. Qed.

Corollary U_slot_mentions : forall c k pc i, k < 16 ->
  M.fetch U pc = Some i -> M.mentions i (SLOT c k) = true -> In (pc, i) (slot_sites c k).
Proof.
  intros c k pc i Hk Hf Hm. rewrite <- (U_slot_sites c k Hk). apply sites_fetch. auto.
Qed.

Corollary U_slot_sites_fetch : forall c k pc i, k < 16 ->
  In (pc, i) (slot_sites c k) -> M.fetch U pc = Some i.
Proof.
  intros c k pc i Hk Hin. rewrite <- (U_slot_sites c k Hk) in Hin.
  apply sites_fetch in Hin. tauto.
Qed.

(* No instruction of U reads a slot: an INC writes it, CHECK and COMMIT
   leave it alone, and every DEC on a slot goes to the next address
   whether the slot holds 0 or not, right after an INC of the same slot. *)
Theorem U_slot_dec_next : forall c k pc j, k < 16 ->
  M.fetch U pc = Some (M.DEC (SLOT c k) j) ->
  j = S pc /\ M.fetch U (pc - 1) = Some (M.INC (SLOT c k)) /\ 1 < pc.
Proof.
  intros c k pc j Hk Hf.
  assert (Hin : In (pc, M.DEC (SLOT c k) j) (slot_sites c k)).
  { apply U_slot_mentions; [exact Hk | exact Hf | apply Nat.eqb_refl]. }
  unfold slot_sites, bump_sites in Hin. simpl in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | [E | []]]]]]]]; try discriminate E;
    inversion E; subst; (split; [reflexivity | split; [| lia]]);
    apply (U_slot_sites_fetch c k _ _ Hk); unfold slot_sites, bump_sites; simpl;
    solve [ repeat (first [ left; f_equal; lia | right ]) ].
Qed.

Theorem U_slot_kinds : forall c k pc i, k < 16 ->
  M.fetch U pc = Some i -> M.mentions i (SLOT c k) = true ->
  i = M.INC (SLOT c k) \/ i = M.DEC (SLOT c k) (S pc) \/
  i = M.CHECK PSlot (SLOT c k) \/ i = M.COMMIT PSlot (SLOT c k).
Proof.
  intros c k pc i Hk Hf Hm. pose proof (U_slot_mentions c k pc i Hk Hf Hm) as Hin.
  unfold slot_sites, bump_sites in Hin. simpl in Hin.
  destruct Hin as [E | [E | [E | [E | [E | [E | [E | []]]]]]]]; inversion E; subst;
    first [ left; reflexivity | right; left; reflexivity
          | right; right; left; reflexivity | right; right; right; reflexivity ].
Qed.

(* The paid instructions of U: one CHECK per slot and one on DEAD per
   bank, one COMMIT per slot and one on DEAD per bank, one CERTIFY. *)
Definition ck_paid (c : E.ctr) : list (nat * hinstr) :=
  (CKH_dead (L_CKH c), M.CHECK PSlot DEAD) ::
  map (fun k => (CKS_chk (CKS_at (L_CKH c) k), M.CHECK PSlot (SLOT c k))) (seq 0 16).
Definition cm_paid (c : E.ctr) : list (nat * hinstr) :=
  (CMH_dead (L_CMH c), M.COMMIT PSlot DEAD) ::
  map (fun k => (CMS_at (L_CMH c) k, M.COMMIT PSlot (SLOT c k))) (seq 0 16).
Definition paid_sites : list (nat * hinstr) :=
  ck_paid E.CA ++ ck_paid E.CB ++ cm_paid E.CA ++ cm_paid E.CB ++ [(L_CERT, M.CERTIFY)].

Lemma paid_sites_length : length paid_sites = 69.
Proof. reflexivity. Qed.

Theorem U_paid_sites : sites (fun i => Nat.eqb (M.cost i) 1) U 1 = paid_sites.
Proof. vm_compute. reflexivity. Qed.

Lemma cost_le_1 : forall i : hinstr, M.cost i <= 1.
Proof. intros []; simpl; lia. Qed.

Corollary U_paid : forall pc i, M.fetch U pc = Some i ->
  M.cost i = 1 <-> In (pc, i) paid_sites.
Proof.
  intros pc i Hf. rewrite <- U_paid_sites, sites_fetch. split.
  - intro H. split; [exact Hf | apply Nat.eqb_eq, H].
  - intros [_ H]. apply Nat.eqb_eq, H.
Qed.

Corollary U_free : forall pc i, M.fetch U pc = Some i ->
  ~ In (pc, i) paid_sites -> M.cost i = 0.
Proof.
  intros pc i Hf Hn. pose proof (cost_le_1 i) as H.
  destruct (M.cost i) as [| [| m]] eqn:Ec; [reflexivity | | lia].
  exfalso. apply Hn. apply (U_paid pc i Hf). exact Ec.
Qed.

(* The only HALT of U is at L_STOP. *)
Definition is_halt (i : hinstr) : bool := match i with M.HALT => true | _ => false end.

Theorem U_halt_sites : sites is_halt U 1 = [(L_STOP, M.HALT)].
Proof. vm_compute. reflexivity. Qed.

(* U mentions no register above DEAD. *)
Definition ireg (i : hinstr) : option nat :=
  match i with
  | M.INC r | M.DEC r _ | M.CHECK _ r | M.COMMIT _ r => Some r
  | M.HALT | M.CERTIFY => None
  end.

Lemma mentions_ireg : forall (i : hinstr) r, M.mentions i r = true <-> ireg i = Some r.
Proof.
  intros [d | d j | | p d | p d |] r; simpl;
    try (split; intro H; discriminate);
    (rewrite Nat.eqb_eq; split; intro H; [subst; reflexivity | inversion H; reflexivity]).
Qed.

Theorem U_regs_bound : forall pc i r, M.fetch U pc = Some i -> M.mentions i r = true -> r <= DEAD.
Proof.
  intros pc i r Hf Hm. apply mentions_ireg in Hm.
  assert (Hall : forallb (fun i => match ireg i with Some r => r <=? DEAD | None => true end) U
                 = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hall. destruct pc as [| q]; [discriminate |].
  simpl in Hf. specialize (Hall i (nth_error_In U q Hf)). rewrite Hm in Hall.
  apply Nat.leb_le, Hall.
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions fam_sub0.
Print Assumptions label_values.
Print Assumptions U_length.
Print Assumptions U_HEAD.
Print Assumptions U_HALTB.
Print Assumptions U_INCH.
Print Assumptions U_DECH.
Print Assumptions U_CKH.
Print Assumptions U_CMH.
Print Assumptions U_CERTH.
Print Assumptions U_BUMPS_inc.
Print Assumptions U_BUMPS_dec.
Print Assumptions U_CKS.
Print Assumptions U_CKH_dead.
Print Assumptions U_EQRS.
Print Assumptions U_CMH_dead.
Print Assumptions U_CMS.
Print Assumptions U_fetch_stop.
Print Assumptions sites_fetch.
Print Assumptions U_slot_sites.
Print Assumptions U_dead_sites.
Print Assumptions U_slot_dec_next.
Print Assumptions U_slot_kinds.
Print Assumptions U_paid_sites.
Print Assumptions U_paid.
Print Assumptions U_free.
Print Assumptions U_halt_sites.
Print Assumptions U_regs_bound.

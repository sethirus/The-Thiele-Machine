(** TcCodes.v: numbers for the programs of the small machine, and the
    specialisation program.

    The instructions of EarnedCore.v are written here as a plain inductive
    type [tc_ki] (no records, no property type), with translations
    [tc_ofki] to the machine's own instructions and [tc_toki] back. A
    program is the list of its instruction codes, the list coded as in
    UniversalCodes.v (pair m n is (2n + 1) * 2^m, [] is 0).

      tc_kcode i     the number of an instruction: it is UC.icode of the
                     machine's instruction [tc_kcode_icode]
      tc_pcode P     the number of a program of the machine; it is
                     UC.prog_code P [tc_pcode_prog_code]
      tc_pdec n      reads any number back as a program, and
                     tc_pdec (tc_pcode P) = P   [tc_pdec_pcode]

    The specialisation program [tc_spec c V] is c copies of "multiply
    counter A by 3" followed by V moved down by 11 c lines. Started on
    2^x it leaves 2^x * 3^c in counter A and then runs V, so V sees the pair
    (x, c) as 2^x * 3^c. [tc_kspec c] is the number of
    [tc_spec c (tc_pdec c)]; it is built from numbers, lists and pairs only,
    so that it can be turned into a term of the lambda calculus (TcEvalL.v).

    Dependencies: Coq standard library, EarnedCore.v, EarnedGeneric.v,
    UniversalCodes.v, TcBlocks.v, TcBridge.v, TcGadget.v. No axioms and no unfinished proofs.                                                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is recursion theory on the two-counter machine of EarnedCore.v (its
   programs, runs and the numbering of programs). The machine's link to the
   abstract record (a CertificationSystem with the trace cost floor, and a
   Thiele-complete machine) lives in EarnedCoreLinks.v and ThieleComplete.v. *)


From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedCore Minimal.EarnedGeneric Minimal.UniversalCodes.
From Undecidability.Shared.Libs.DLW Require Import utils gcd pos vec subcode sss.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs mma_utils.
Require Import Kernel.TcBridge Kernel.TcGadget Minimal.TcBlocks.
Module E := Minimal.EarnedCore.
Module G := Minimal.EarnedGeneric.
Module UC := Minimal.UniversalCodes.
Unset Implicit Arguments.

(* ================================================================= *)
(* Halving, and pairs read back.                                      *)
(* ================================================================= *)

Fixpoint tc_hb (n : nat) : nat * bool :=
  match n with
  | 0 => (0, false)
  | S k => let (h, b) := tc_hb k in if b then (S h, false) else (h, true)
  end.

Definition tc_bit (b : bool) : nat := if b then 1 else 0.

Lemma tc_hb_correct : forall n, n = 2 * fst (tc_hb n) + tc_bit (snd (tc_hb n)).
Proof.
  induction n as [| k IH]; [reflexivity |].
  simpl. destruct (tc_hb k) as [h b]. simpl in *.
  destruct b; simpl in *; lia.
Qed.

Lemma tc_hb_unique : forall h b, tc_hb (tc_bit b + 2 * h) = (h, b).
Proof.
  intros h b. pose proof (tc_hb_correct (tc_bit b + 2 * h)) as E1.
  destruct (tc_hb (tc_bit b + 2 * h)) as [h' b'] eqn:Ehb. simpl in E1.
  destruct b, b'; unfold tc_bit in E1; simpl in E1; f_equal; lia.
Qed.

Lemma tc_hb_spec : forall n, tc_hb n = (Nat.div2 n, Nat.odd n).
Proof.
  intro n. pose proof (Nat.div2_odd n) as E1.
  rewrite E1 at 1. replace (Nat.b2n (Nat.odd n)) with (tc_bit (Nat.odd n))
    by (destruct (Nat.odd n); reflexivity).
  rewrite Nat.add_comm. apply tc_hb_unique.
Qed.

Fixpoint tc_unp (fuel x m : nat) : option (nat * nat) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | 0 => None
      | S _ =>
          match tc_hb x with
          | (h, true) => Some (m, h)
          | (h, false) => tc_unp f h (S m)
          end
      end
  end.

Lemma tc_unp_eq : forall f x m, tc_unp f x m = UC.unp f x m.
Proof.
  induction f as [| f IH]; intros x m; [reflexivity |].
  destruct x as [| x']; [reflexivity |].
  change (UC.unp (S f) (S x') m) with
    (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
     else UC.unp f (Nat.div2 (S x')) (S m)).
  change (tc_unp (S f) (S x') m) with
    (match tc_hb (S x') with (h, true) => Some (m, h) | (h, false) => tc_unp f h (S m) end).
  rewrite tc_hb_spec.
  destruct (Nat.odd (S x')); [reflexivity | apply IH].
Qed.

Definition tc_unpair (x : nat) : option (nat * nat) := tc_unp x x 0.

Lemma tc_unpair_eq : forall x, tc_unpair x = UC.unpair x.
Proof. intro x. apply tc_unp_eq. Qed.

Lemma tc_unpair_pair : forall m n, tc_unpair (UC.pair m n) = Some (m, n).
Proof. intros. rewrite tc_unpair_eq. apply UC.unpair_pair. Qed.

Lemma tc_pair_ge : forall m n, S n <= UC.pair m n.
Proof.
  intros m n. unfold UC.pair. pose proof (UC.pow2_pos m). nia.
Qed.

(* ================================================================= *)
(* Lists of numbers as one number.                                    *)
(* ================================================================= *)

Fixpoint tc_lencode (l : list nat) : nat :=
  match l with [] => 0 | x :: t => UC.pair x (tc_lencode t) end.

Fixpoint tc_ldec (fuel v : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f => match tc_unpair v with None => [] | Some (x, t) => x :: tc_ldec f t end
  end.

Definition tc_ldecode (v : nat) : list nat := tc_ldec v v.

Lemma tc_lencode_ge : forall l, length l <= tc_lencode l.
Proof.
  induction l as [| x t IH]; simpl; [lia |]. pose proof (tc_pair_ge x (tc_lencode t)). lia.
Qed.

Lemma tc_ldec_encode : forall l f, length l <= f -> tc_ldec f (tc_lencode l) = l.
Proof.
  induction l as [| x t IH]; intros f Hf.
  - destruct f; reflexivity.
  - destruct f as [| f]; [simpl in Hf; lia |]. simpl.
    rewrite tc_unpair_pair. rewrite IH by (simpl in Hf; lia). reflexivity.
Qed.

Theorem tc_ldecode_encode : forall l, tc_ldecode (tc_lencode l) = l.
Proof. intro l. apply tc_ldec_encode, tc_lencode_ge. Qed.

Lemma tc_lencode_G : forall l, tc_lencode l = G.encode l.
Proof.
  induction l as [| x t IH]; [reflexivity |].
  simpl. rewrite IH. unfold UC.pair. simpl. lia.
Qed.

(* ================================================================= *)
(* Instructions.                                                      *)
(* ================================================================= *)

Inductive tc_ki : Type :=
| tc_KInc (c : nat)
| tc_KDec (c j : nat)
| tc_KHalt
| tc_KCheck (c q : nat)
| tc_KCommit (c q : nat)
| tc_KCertify.

Definition tc_kcode (i : tc_ki) : nat :=
  match i with
  | tc_KInc c => UC.pair 0 c
  | tc_KDec c j => UC.pair 1 (UC.pair c j)
  | tc_KHalt => UC.pair 2 0
  | tc_KCheck c q => UC.pair 3 (UC.pair c q)
  | tc_KCommit c q => UC.pair 4 (UC.pair c q)
  | tc_KCertify => UC.pair 5 0
  end.

Definition tc_kdecD (a : nat) : tc_ki :=
  match tc_unpair a with Some (c, q) => tc_KDec c q | None => tc_KHalt end.
Definition tc_kdecK (a : nat) : tc_ki :=
  match tc_unpair a with Some (c, q) => tc_KCheck c q | None => tc_KHalt end.
Definition tc_kdecM (a : nat) : tc_ki :=
  match tc_unpair a with Some (c, q) => tc_KCommit c q | None => tc_KHalt end.

Definition tc_kdec_op (o a : nat) : tc_ki :=
  match o with
  | 0 => tc_KInc a
  | S o1 =>
      match o1 with
      | 0 => tc_kdecD a
      | S o2 =>
          match o2 with
          | 0 => tc_KHalt
          | S o3 =>
              match o3 with
              | 0 => tc_kdecK a
              | S o4 =>
                  match o4 with
                  | 0 => tc_kdecM a
                  | S o5 => match o5 with 0 => tc_KCertify | S _ => tc_KHalt end
                  end
              end
          end
      end
  end.

Definition tc_kdec (x : nat) : tc_ki :=
  match tc_unpair x with Some (o, a) => tc_kdec_op o a | None => tc_KHalt end.

Theorem tc_kdec_kcode : forall i, tc_kdec (tc_kcode i) = i.
Proof.
  intros []; unfold tc_kdec, tc_kcode; rewrite tc_unpair_pair; try reflexivity;
    simpl; unfold tc_kdecD, tc_kdecK, tc_kdecM; rewrite tc_unpair_pair; reflexivity.
Qed.

Definition tc_kpcode (P : list tc_ki) : nat := tc_lencode (map tc_kcode P).

Definition tc_kpdec (n : nat) : list tc_ki := map tc_kdec (tc_ldecode n).

Theorem tc_kpdec_kpcode : forall P, tc_kpdec (tc_kpcode P) = P.
Proof.
  intro P. unfold tc_kpdec, tc_kpcode. rewrite tc_ldecode_encode, map_map.
  rewrite (map_ext _ (fun i => i)) by apply tc_kdec_kcode. apply map_id.
Qed.

(* ================================================================= *)
(* The machine's own instructions.                                    *)
(* ================================================================= *)

Definition tc_cdec (c : nat) : E.ctr := if Nat.eqb c 0 then E.CA else E.CB.

Lemma tc_cdec_ccode : forall c, tc_cdec (UC.ccode c) = c.
Proof. intros []; reflexivity. Qed.

Definition tc_ofki (i : tc_ki) : E.instr :=
  match i with
  | tc_KInc c => E.INC (tc_cdec c)
  | tc_KDec c j => E.DEC (tc_cdec c) j
  | tc_KHalt => E.HALT
  | tc_KCheck c q => E.CHECK (UC.pdec q) (tc_cdec c)
  | tc_KCommit c q => E.COMMIT (UC.pdec q) (tc_cdec c)
  | tc_KCertify => E.CERTIFY
  end.

Definition tc_toki (i : E.instr) : tc_ki :=
  match i with
  | E.INC c => tc_KInc (UC.ccode c)
  | E.DEC c j => tc_KDec (UC.ccode c) j
  | E.HALT => tc_KHalt
  | E.CHECK p c => tc_KCheck (UC.ccode c) (UC.pcode p)
  | E.COMMIT p c => tc_KCommit (UC.ccode c) (UC.pcode p)
  | E.CERTIFY => tc_KCertify
  end.

Lemma tc_of_to_ki : forall i, tc_ofki (tc_toki i) = i.
Proof.
  intros [c | c j | | p c | p c |]; simpl; rewrite ?tc_cdec_ccode, ?UC.pdec_pcode; reflexivity.
Qed.

Lemma tc_kcode_icode : forall i, tc_kcode (tc_toki i) = UC.icode i.
Proof. intros [c | c j | | p c | p c |]; reflexivity. Qed.

Lemma tc_map_of_to : forall P, map tc_ofki (map tc_toki P) = P.
Proof.
  intro P. rewrite map_map. rewrite (map_ext _ (fun i => i)) by apply tc_of_to_ki. apply map_id.
Qed.

Definition tc_pcode (P : list E.instr) : nat := tc_kpcode (map tc_toki P).

Definition tc_pdec (n : nat) : list E.instr := map tc_ofki (tc_kpdec n).

Theorem tc_pdec_pcode : forall P, tc_pdec (tc_pcode P) = P.
Proof. intro P. unfold tc_pdec, tc_pcode. rewrite tc_kpdec_kpcode. apply tc_map_of_to. Qed.

Theorem tc_pcode_prog_code : forall P, tc_pcode P = UC.prog_code P.
Proof.
  intro P. unfold tc_pcode, tc_kpcode, UC.prog_code. rewrite tc_lencode_G.
  f_equal. rewrite map_map. apply map_ext. intro i. apply tc_kcode_icode.
Qed.

Theorem tc_pcode_inj : forall P Q, tc_pcode P = tc_pcode Q -> P = Q.
Proof.
  intros P Q H. rewrite <- (tc_pdec_pcode P), <- (tc_pdec_pcode Q), H. reflexivity.
Qed.

Lemma tc_pcode_of : forall P, tc_pcode (map tc_ofki P) = tc_kpcode (map tc_toki (map tc_ofki P)).
Proof. reflexivity. Qed.

(* ================================================================= *)
(* Relocation, on tc_ki programs.                                     *)
(* ================================================================= *)

Definition tc_kri (off len : nat) (i : tc_ki) : tc_ki :=
  match i with tc_KDec c j => tc_KDec c (tc_rj off len j) | _ => i end.

Definition tc_kreloc (off : nat) (B : list tc_ki) : list tc_ki := map (tc_kri off (length B)) B.

Lemma tc_kreloc_of : forall off B,
  map tc_ofki (tc_kreloc off B) = tc_greloc off (map tc_ofki B).
Proof.
  intros off B. unfold tc_kreloc, tc_greloc. rewrite !map_map, map_length.
  apply map_ext. intros [c | c j | | c q | c q |]; reflexivity.
Qed.

(* ================================================================= *)
(* The multiplication block and the specialisation                    *)
(* ================================================================= *)

(* the vendored block: A := k * A with B as the spare, at address i *)
Fixpoint tc_vchain (k c i : nat) : list (mm_instr (pos 2)) :=
  match c with
  | 0 => []
  | S c' => mma_mult_cst_with_zero tcA tcB k i ++ tc_vchain k c' (8 + k + i)
  end.

Lemma tc_vchain_length : forall k c i, length (tc_vchain k c i) = c * (8 + k).
Proof.
  intros k c. induction c as [| c IH]; intro i; [reflexivity |].
  change (tc_vchain k (S c) i) with (mma_mult_cst_with_zero tcA tcB k i ++ tc_vchain k c (8 + k + i)).
  rewrite app_length, mma_mult_cst_with_zero_length, IH. lia.
Qed.

Lemma tc_vchain_run : forall k c i a,
  sss_compute (@mma_sss 2) (i, tc_vchain k c i) (i, tc_tovec a 0)
    (c * (8 + k) + i, tc_tovec (k ^ c * a) 0).
Proof.
  intros k c. induction c as [| c IH]; intros i a.
  - replace (0 * (8 + k) + i) with i by lia. replace (k ^ 0 * a) with a by (simpl; lia).
    exists 0. apply sss_steps_0. reflexivity.
  - change (tc_vchain k (S c) i) with (mma_mult_cst_with_zero tcA tcB k i ++ tc_vchain k c (8 + k + i)).
    eapply sss_compute_trans.
    + apply sss_progress_compute.
      eapply subcode_sss_progress; [| apply tc_mult].
      exists [], (tc_vchain k c (8 + k + i)). split; [reflexivity | simpl; lia].
    + replace (S c * (8 + k) + i) with (c * (8 + k) + (8 + k + i)) by lia.
      replace (k ^ S c * a) with (k ^ c * (k * a)) by (simpl; ring).
      eapply subcode_sss_compute; [| apply IH].
      exists (mma_mult_cst_with_zero tcA tcB k i), [].
      split; [rewrite app_nil_r; reflexivity | rewrite mma_mult_cst_with_zero_length; lia].
Qed.

(* the explicit instructions of a block: A := k * A, B the spare *)
Definition tc_kmulblock (k i : nat) : list tc_ki :=
  [tc_KDec 0 (3 + i); tc_KInc 0; tc_KDec 0 (5 + k + i)] ++ repeat (tc_KInc 1) k ++
  [tc_KInc 0; tc_KDec 0 i] ++ [tc_KInc 0; tc_KDec 1 (5 + k + i); tc_KDec 0 (8 + k + i)].

Fixpoint tc_kmulchain (k c i : nat) : list tc_ki :=
  match c with 0 => [] | S c' => tc_kmulblock k i ++ tc_kmulchain k c' (8 + k + i) end.

Lemma tc_incs_repeat : forall (n k : nat) (x : pos n), mma_incs x k = repeat (mm_inc x) k.
Proof. intros n k x. induction k as [| k IH]; [reflexivity |]. simpl. rewrite IH. reflexivity. Qed.

Lemma tc_kmulblock_eq : forall k i,
  map tc_ofki (tc_kmulblock k i) = E.compile (tc_P (mma_mult_cst_with_zero tcA tcB k i)).
Proof.
  intros k i. unfold tc_kmulblock, tc_P, E.compile.
  unfold mma_mult_cst_with_zero, mma_mult_cst, mma_jump, mma_transfert.
  rewrite tc_incs_repeat.
  rewrite !map_app, !map_map. simpl. rewrite !map_repeat. simpl.
  rewrite map_app, map_repeat. simpl. rewrite <- app_assoc. reflexivity.
Qed.

Lemma tc_kmulchain_eq : forall k c i,
  map tc_ofki (tc_kmulchain k c i) = E.compile (tc_P (tc_vchain k c i)).
Proof.
  intros k c. induction c as [| c IH]; intro i; [reflexivity |].
  change (tc_kmulchain k (S c) i) with (tc_kmulblock k i ++ tc_kmulchain k c (8 + k + i)).
  change (tc_vchain k (S c) i) with (mma_mult_cst_with_zero tcA tcB k i ++ tc_vchain k c (8 + k + i)).
  rewrite map_app, tc_kmulblock_eq, IH.
  unfold E.compile, tc_P. rewrite !map_app, !map_map. reflexivity.
Qed.

(* the specialised program: c copies of "multiply A by 3", then V *)
Definition tc_spec (c : nat) (V : list E.instr) : list E.instr :=
  E.compile (tc_P (tc_vchain 3 c 1)) ++ tc_greloc (c * 11) V.

(* an instruction read back through the machine: counters other than 0 become B *)
Definition tc_cn (c : nat) : nat := if Nat.eqb c 0 then 0 else 1.

Definition tc_knorm (i : tc_ki) : tc_ki :=
  match i with
  | tc_KInc c => tc_KInc (tc_cn c)
  | tc_KDec c j => tc_KDec (tc_cn c) j
  | tc_KHalt => tc_KHalt
  | tc_KCheck c q => tc_KCheck (tc_cn c) q
  | tc_KCommit c q => tc_KCommit (tc_cn c) q
  | tc_KCertify => tc_KCertify
  end.

Lemma tc_knorm_eq : forall i, tc_knorm i = tc_toki (tc_ofki i).
Proof.
  intros [c | c j | | c q | c q |]; simpl; unfold tc_cn, tc_cdec;
    try (destruct (Nat.eqb c 0)); simpl; rewrite ?UC.pcode_pdec; reflexivity.
Qed.

Definition tc_kspec_prog (c : nat) : list tc_ki :=
  tc_kmulchain 3 c 1 ++ tc_kreloc (c * 11) (tc_kpdec c).

Definition tc_kspec (c : nat) : nat := tc_kpcode (map tc_knorm (tc_kspec_prog c)).

Lemma tc_spec_length_prefix : forall c, length (E.compile (tc_P (tc_vchain 3 c 1))) = c * 11.
Proof.
  intro c. unfold E.compile, tc_P. rewrite !map_length, tc_vchain_length. lia.
Qed.

Lemma tc_kspec_prog_of : forall c, map tc_ofki (tc_kspec_prog c) = tc_spec c (tc_pdec c).
Proof.
  intro c. unfold tc_kspec_prog, tc_spec, tc_pdec. rewrite map_app, tc_kmulchain_eq, tc_kreloc_of.
  reflexivity.
Qed.

Theorem tc_kspec_code : forall c, tc_kspec c = tc_pcode (tc_spec c (tc_pdec c)).
Proof.
  intro c. rewrite <- tc_kspec_prog_of. unfold tc_kspec, tc_pcode.
  f_equal. rewrite map_map. apply map_ext. intro i. apply tc_knorm_eq.
Qed.

Print Assumptions tc_kspec_code.
Print Assumptions tc_pdec_pcode.
Print Assumptions tc_pcode_prog_code.

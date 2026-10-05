(** UniversalPCodes.v: numbers for the parts of a priced guest, and the one
    property the host machine checks, for the universal host U_P.

    The guest is the priced machine of EarnedPriced.v (the instructions of
    EarnedGeneric.v and PAY) over the universal property language cg_uprop
    of CompilerChecker.v: UBase q (a property of the counter language of
    EarnedGeneric.v) or URun r (run the routine coded by r on the checked
    value). The host is the machine of EarnedMultiPriced.v. This file fixes
    how a guest program, a guest property and a guest claim are written as
    numbers the host can hold in its counters.

      pair m n      the number (2n + 1) * 2^m. Every positive number is
                       pair m n for exactly one m and n; 0 is no pair.
      unpair x      the inverse: Some (m, n) when x = pair m n, None at 0.
      pcode p       the number of a guest property: UBase q is twice the
                       code of q (PZero 0, PEven 1, PGe n is n + 2), URun r
                       is 2r + 1. pdec is its inverse on every number.
      ccode c       the number of a guest counter: A 0, B 1.
      icode i       the number of a guest instruction, a pair of an opcode
                       (0 INC, 1 DEC, 2 HALT, 3 CHECK, 4 COMMIT, 5 CERTIFY,
                       6 PAY) and its operands. idecode reads it back,
                       and reads every number that is no instruction's code
                       as None.
      pu_prog_code P   the list of instruction codes of P as one number, by
                       the list code of EarnedGeneric.v: encode [] = 0 and
                       encode (x :: t) = pair x (encode t).
      pu_fetch_code    unpacks a program code k times and reads the head.

    The host checks one property, PSlot. A host counter holding
    pair (pcode p) v satisfies PSlot exactly when the universal
    checker cg_ueval accepts p at v. The checker is one fixed function, so
    one fixed host serves every guest written in cg_uprop, whatever machine
    the guest was compiled from.

    The module E below names the parts of the priced guest machine at the
    property language cg_uprop with the names of EarnedCore.v (E.step,
    E.val, E.CHECK, ...). Every name in E is an abbreviation of a
    definition or theorem of EarnedGeneric.v, EarnedPriced.v or
    CompilerChecker.v, or of the one small lemma pu_g_err_write.

    Dependencies: Coq standard library, EarnedGeneric.v, EarnedPriced.v,
    EarnedMultiPriced.v and CompilerChecker.v (which uses the vendored
    coq-undecidability library). No axioms, no Admitted.                     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file imports only the Coq standard library, the minimal machines and the
   checker of CompilerChecker.v. Its link to the abstract record (the host
   with the property PSlot meeting thiele_complete, and every computably
   presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.EarnedGeneric Minimal.EarnedPriced Minimal.EarnedMultiPriced.
Require Minimal.CompilerChecker.

Module G := Minimal.EarnedGeneric.
Module P := Minimal.EarnedPriced.
Module M := Minimal.EarnedMultiPriced.
Module CK := Minimal.CompilerChecker.

(* A write keeps the trap latch. *)
Lemma pu_g_err_write : forall {prop : Type} (k : @G.core prop) c n j,
  G.err (G.write k c n j) = G.err k.
Proof. intros prop k [] n j; reflexivity. Qed.

(* The priced guest at the universal property language, under the names of
   EarnedCore.v. *)
Module E.
  Notation prop := CK.cg_uprop.
  Notation prop_eqb := CK.cg_uprop_eqb.
  Notation eval := CK.cg_ueval.
  Notation holds := CK.cg_uholds.
  Notation eval_iff := CK.cg_ueval_iff.
  Notation instr := (@P.pr_instr CK.cg_uprop).
  Notation INC := P.INC.
  Notation DEC := P.DEC.
  Notation HALT := P.HALT.
  Notation CHECK := P.CHECK.
  Notation COMMIT := P.COMMIT.
  Notation CERTIFY := P.CERTIFY.
  Notation PAY := P.PAY.
  Notation ctr := G.ctr.
  Notation CA := G.CA.
  Notation CB := G.CB.
  Notation ctr_eqb := G.ctr_eqb.
  Notation state := (@G.state CK.cg_uprop).
  Notation core := (@G.core CK.cg_uprop).
  Notation fact := (@G.fact CK.cg_uprop).
  Notation mkfact := (@G.mkfact CK.cg_uprop).
  Notation mkst := (@G.mkst CK.cg_uprop).
  Notation core_of := (@G.core_of CK.cg_uprop).
  Notation mu := (@G.mu CK.cg_uprop).
  Notation cert := (@G.cert CK.cg_uprop).
  Notation val := (@G.val CK.cg_uprop).
  Notation ver := (@G.ver CK.cg_uprop).
  Notation ca := (@G.ca CK.cg_uprop).
  Notation cb := (@G.cb CK.cg_uprop).
  Notation pc := (@G.pc CK.cg_uprop).
  Notation err := (@G.err CK.cg_uprop).
  Notation facts := (@G.facts CK.cg_uprop).
  Notation chan := (@G.chan CK.cg_uprop).
  Notation fact_cap := G.fact_cap.
  Notation write := (@G.write CK.cg_uprop).
  Notation goto := (@G.goto CK.cg_uprop).
  Notation trap := (@G.trap CK.cg_uprop).
  Notation record_fact := (@G.record_fact CK.cg_uprop).
  Notation commit_to := (@G.commit_to CK.cg_uprop).
  Notation claim := (@G.claim CK.cg_uprop).
  Notation check_ok := (G.check_ok CK.cg_ueval).
  Notation commit_ok := (G.commit_ok CK.cg_uprop_eqb).
  Notation certify_ok := (@G.certify_ok CK.cg_uprop).
  Notation fetch := G.fetch.
  Notation start := (@G.start CK.cg_uprop).
  Notation cost := (@P.pr_cost CK.cg_uprop).
  Notation fires := (@P.pr_fires CK.cg_uprop).
  Notation next_instr := (@P.pr_next_instr CK.cg_uprop).
  Notation halted := (@P.pr_halted CK.cg_uprop).
  Notation cexec := (P.pr_cexec CK.cg_uprop_eqb CK.cg_ueval).
  Notation exec := (P.pr_exec CK.cg_uprop_eqb CK.cg_ueval).
  Notation step := (P.pr_step CK.cg_uprop_eqb CK.cg_ueval).
  Notation run := (P.pr_run CK.cg_uprop_eqb CK.cg_ueval).
  Notation run_prog := (P.pr_run_prog CK.cg_uprop_eqb CK.cg_ueval).
  Notation trace_of := (P.pr_trace_of CK.cg_uprop_eqb CK.cg_ueval).
  Notation untouched := (P.pr_untouched CK.cg_uprop_eqb CK.cg_ueval).
  Notation start_clean := (@G.generic_start_clean CK.cg_uprop).
  Notation ver_write := (@G.generic_ver_write CK.cg_uprop).
  Notation val_write := (@G.generic_val_write CK.cg_uprop).
  Notation facts_write := (@G.generic_facts_write CK.cg_uprop).
  Notation chan_write := (@G.generic_chan_write CK.cg_uprop).
  Notation err_write := (@pu_g_err_write CK.cg_uprop).
  Notation commit_ok_iff := (G.generic_commit_ok_iff CK.cg_uprop_eqb CK.cg_uprop_eqb_eq).
  Notation run_prog_trace := (P.pr_run_prog_trace CK.cg_uprop_eqb CK.cg_ueval).
  Notation run_prog_halted := (P.pr_run_prog_halted CK.cg_uprop_eqb CK.cg_ueval).
  Notation ver_mono := (P.pr_ver_mono CK.cg_uprop_eqb CK.cg_ueval).
  Notation ver_mono_run := (P.pr_ver_mono_run CK.cg_uprop_eqb CK.cg_ueval).
  Notation ver_same_val := (P.pr_ver_same_val CK.cg_uprop_eqb CK.cg_ueval).
  Notation only_certify_certifies :=
    (P.pr_only_certify_certifies CK.cg_uprop_eqb CK.cg_ueval).
  Notation chan_origin := (P.pr_chan_origin CK.cg_uprop_eqb CK.cg_ueval).
  Notation earned_commitment_provenance :=
    (P.pr_earned_commitment_provenance CK.cg_uprop_eqb CK.cg_uprop_eqb_eq CK.cg_ueval).
End E.

(* ================================================================= *)
(* Pairs of numbers as one number.                                    *)
(* ================================================================= *)

Definition pu_pair (m n : nat) : nat := (n + n + 1) * 2 ^ m.

(* Strip factors of 2, counting them in m, until the number is odd. The
   fuel argument is the number itself, which is always enough. *)
Fixpoint pu_unp (fuel x m : nat) : option (nat * nat) :=
  match fuel with
  | 0 => None
  | S f =>
      match x with
      | 0 => None
      | S _ => if Nat.odd x then Some (m, Nat.div2 x) else pu_unp f (Nat.div2 x) (S m)
      end
  end.

Definition pu_unpair (x : nat) : option (nat * nat) := pu_unp x x 0.

Lemma pu_unpair_zero : pu_unpair 0 = None.
Proof. reflexivity. Qed.

Lemma pu_pow2_pos : forall m, 0 < 2 ^ m.
Proof. intro m. apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia. Qed.

Lemma pu_pair_pos : forall m n, 0 < pu_pair m n.
Proof. intros m n. unfold pu_pair. pose proof (pu_pow2_pos m). nia. Qed.

Lemma pu_pair_S : forall m n, pu_pair (S m) n = 2 * pu_pair m n.
Proof. intros m n. unfold pu_pair. rewrite Nat.pow_succ_r'. lia. Qed.

Lemma pu_pair_0 : forall n, pu_pair 0 n = S (2 * n).
Proof. intro n. unfold pu_pair. simpl. lia. Qed.

Lemma pu_unp_fuel : forall f1 f2 x m, x <= f1 -> x <= f2 -> pu_unp f1 x m = pu_unp f2 x m.
Proof.
  induction f1 as [| f1 IH]; intros f2 x m H1 H2.
  - assert (x = 0) as -> by lia. destruct f2; reflexivity.
  - destruct x as [| x']; [destruct f2; reflexivity |].
    destruct f2 as [| f2]; [lia |].
    assert (Hd : Nat.div2 (S x') < S x') by (apply Nat.lt_div2; lia).
    change (pu_unp (S f1) (S x') m) with
      (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
       else pu_unp f1 (Nat.div2 (S x')) (S m)).
    change (pu_unp (S f2) (S x') m) with
      (if Nat.odd (S x') then Some (m, Nat.div2 (S x'))
       else pu_unp f2 (Nat.div2 (S x')) (S m)).
    destruct (Nat.odd (S x')); [reflexivity |].
    apply IH; lia.
Qed.

Lemma pu_unp_odd : forall y m, pu_unp (S (2 * y)) (S (2 * y)) m = Some (m, y).
Proof.
  intros y m.
  change (pu_unp (S (2 * y)) (S (2 * y)) m) with
    (if Nat.odd (S (2 * y)) then Some (m, Nat.div2 (S (2 * y)))
     else pu_unp (2 * y) (Nat.div2 (S (2 * y))) (S m)).
  replace (Nat.odd (S (2 * y))) with true
    by (replace (S (2 * y)) with (1 + 2 * y) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_succ_double. reflexivity.
Qed.

Lemma pu_unp_even : forall v m, 0 < v -> pu_unp (2 * v) (2 * v) m = pu_unp v v (S m).
Proof.
  intros v m Hv. destruct (2 * v) as [| w] eqn:E; [lia |].
  change (pu_unp (S w) (S w) m) with
    (if Nat.odd (S w) then Some (m, Nat.div2 (S w))
     else pu_unp w (Nat.div2 (S w)) (S m)).
  rewrite <- E.
  replace (Nat.odd (2 * v)) with false
    by (replace (2 * v) with (0 + 2 * v) by lia;
        rewrite Nat.odd_add_mul_2; reflexivity).
  rewrite Nat.div2_double. apply pu_unp_fuel; lia.
Qed.

Lemma pu_unp_pair : forall m n acc, pu_unp (pu_pair m n) (pu_pair m n) acc = Some (m + acc, n).
Proof.
  induction m as [| m IH]; intros n acc.
  - rewrite pu_pair_0. rewrite pu_unp_odd. reflexivity.
  - rewrite pu_pair_S. rewrite pu_unp_even by apply pu_pair_pos.
    rewrite IH. f_equal. f_equal. lia.
Qed.

Theorem pu_unpair_pair : forall m n, pu_unpair (pu_pair m n) = Some (m, n).
Proof.
  intros m n. unfold pu_unpair. rewrite pu_unp_pair. rewrite Nat.add_0_r. reflexivity.
Qed.

Theorem pu_pair_inj : forall m n m' n', pu_pair m n = pu_pair m' n' -> m = m' /\ n = n'.
Proof.
  intros m n m' n' H. apply (f_equal pu_unpair) in H.
  rewrite !pu_unpair_pair in H. injection H as -> ->. auto.
Qed.

(* Every positive number is a pair. *)
Lemma pu_pair_onto : forall x, 0 < x -> exists m n, x = pu_pair m n.
Proof.
  induction x as [x IH] using (well_founded_induction lt_wf). intros Hx.
  pose proof (Nat.div2_odd x) as Hd.
  destruct (Nat.odd x) eqn:Ho; simpl in Hd.
  - exists 0, (Nat.div2 x). rewrite pu_pair_0. lia.
  - assert (Hlt : Nat.div2 x < x) by (apply Nat.lt_div2; lia).
    assert (Hpos : 0 < Nat.div2 x) by lia.
    destruct (IH _ Hlt Hpos) as [m [n Hmn]].
    exists (S m), n. rewrite pu_pair_S, <- Hmn. lia.
Qed.

Theorem pu_unpair_some : forall x, 0 < x ->
  exists m n, pu_unpair x = Some (m, n) /\ x = pu_pair m n.
Proof.
  intros x Hx. destruct (pu_pair_onto x Hx) as [m [n ->]].
  exists m, n. split; [apply pu_unpair_pair | reflexivity].
Qed.

Theorem pu_unpair_none : forall x, pu_unpair x = None <-> x = 0.
Proof.
  intro x. split.
  - intro H. destruct x as [| x]; [reflexivity | exfalso].
    destruct (pu_unpair_some (S x)) as [m [n [Hs _]]]; [lia | congruence].
  - intros ->. reflexivity.
Qed.

Theorem pu_unpair_sound : forall x m n, pu_unpair x = Some (m, n) -> x = pu_pair m n.
Proof.
  intros x m n H. destruct x as [| x]; [discriminate |].
  destruct (pu_unpair_some (S x)) as [m' [n' [Hs Hx]]]; [lia |].
  rewrite H in Hs. injection Hs as -> ->. exact Hx.
Qed.

(* The list code of EarnedGeneric.v is built from pair. *)
Lemma pu_pair_encode : forall x t, G.encode (x :: t) = pu_pair x (G.encode t).
Proof. intros x t. simpl. unfold pu_pair. lia. Qed.

Lemma pu_unpair_encode_nil : pu_unpair (G.encode []) = None.
Proof. reflexivity. Qed.

Lemma pu_unpair_encode_cons : forall x t,
  pu_unpair (G.encode (x :: t)) = Some (x, G.encode t).
Proof. intros x t. rewrite pu_pair_encode. apply pu_unpair_pair. Qed.

(* ================================================================= *)
(* Guest properties and counters as numbers.                          *)
(* ================================================================= *)

(* Properties of the counter language of EarnedGeneric.v. *)
Definition pu_cpcode (q : G.cprop) : nat :=
  match q with G.PZero => 0 | G.PEven => 1 | G.PGe n => n + 2 end.

Definition pu_cpdec (n : nat) : G.cprop :=
  match n with 0 => G.PZero | 1 => G.PEven | S (S m) => G.PGe m end.

Lemma pu_cpdec_cpcode : forall q, pu_cpdec (pu_cpcode q) = q.
Proof.
  intros [| | n]; [reflexivity | reflexivity |].
  simpl. replace (n + 2) with (S (S n)) by lia. reflexivity.
Qed.

Lemma pu_cpcode_cpdec : forall n, pu_cpcode (pu_cpdec n) = n.
Proof. intros [| [| n]]; simpl; [reflexivity | reflexivity | lia]. Qed.

(* Universal properties: even numbers for UBase, odd numbers for URun. *)
Definition pu_pcode (p : E.prop) : nat :=
  match p with CK.UBase q => 2 * pu_cpcode q | CK.URun r => S (2 * r) end.

Definition pu_pdec (n : nat) : E.prop :=
  if Nat.even n then CK.UBase (pu_cpdec (Nat.div2 n)) else CK.URun (Nat.div2 n).

Lemma pu_even_double : forall n, Nat.even (2 * n) = true.
Proof. intro n. rewrite Nat.even_mul. reflexivity. Qed.

Lemma pu_even_sdouble : forall n, Nat.even (S (2 * n)) = false.
Proof.
  intro n. replace (S (2 * n)) with (1 + 2 * n) by lia.
  rewrite Nat.even_add_mul_2. reflexivity.
Qed.

Theorem pu_pdec_pcode : forall p, pu_pdec (pu_pcode p) = p.
Proof.
  intros [q | r]; unfold pu_pdec, pu_pcode.
  - rewrite pu_even_double, Nat.div2_double, pu_cpdec_cpcode. reflexivity.
  - rewrite pu_even_sdouble, Nat.div2_succ_double. reflexivity.
Qed.

Theorem pu_pcode_pdec : forall n, pu_pcode (pu_pdec n) = n.
Proof.
  intro n. unfold pu_pdec. pose proof (Nat.div2_odd n) as Hd.
  rewrite <- Nat.negb_even in Hd.
  destruct (Nat.even n); simpl in Hd; simpl pu_pcode.
  - rewrite pu_cpcode_cpdec. lia.
  - lia.
Qed.

Theorem pu_pcode_inj : forall p q, pu_pcode p = pu_pcode q -> p = q.
Proof.
  intros p q H. rewrite <- (pu_pdec_pcode p), <- (pu_pdec_pcode q), H. reflexivity.
Qed.

Definition pu_ccode (c : E.ctr) : nat := match c with E.CA => 0 | E.CB => 1 end.

Definition pu_cdec (n : nat) : option E.ctr :=
  match n with 0 => Some E.CA | 1 => Some E.CB | _ => None end.

Theorem pu_cdec_ccode : forall c, pu_cdec (pu_ccode c) = Some c.
Proof. intros []; reflexivity. Qed.

Theorem pu_cdec_sound : forall n c, pu_cdec n = Some c -> pu_ccode c = n.
Proof.
  intros [| [| n]] c H; simpl in H; try discriminate; injection H as <-; reflexivity.
Qed.

Theorem pu_ccode_inj : forall c d, pu_ccode c = pu_ccode d -> c = d.
Proof. intros [] [] H; simpl in H; try discriminate; reflexivity. Qed.

Lemma pu_ccode_lt : forall c, pu_ccode c < 2.
Proof. intros []; simpl; lia. Qed.

(* ================================================================= *)
(* The host property language: one property, PSlot.                   *)
(* ================================================================= *)

Inductive pu_hprop : Type := PSlot.

(* The one property equals itself; with one constructor the match has one
   case. *)
Definition pu_hprop_eqb (p q : pu_hprop) : bool :=
  match p, q with PSlot, PSlot => true end.

Lemma pu_hprop_eqb_eq : forall p q, pu_hprop_eqb p q = true <-> p = q.
Proof. intros [] []. split; reflexivity. Qed.

(* A counter holding pair m v satisfies PSlot when guest property pdec m
   holds of v. A counter holding 0 holds no pair and never satisfies it. *)
Definition pu_heval (p : pu_hprop) (x : nat) : bool :=
  match pu_unpair x with Some (m, v) => CK.cg_ueval (pu_pdec m) v | None => false end.

Definition pu_hholds (p : pu_hprop) (x : nat) : Prop :=
  match pu_unpair x with Some (m, v) => CK.cg_uholds (pu_pdec m) v | None => False end.

Theorem pu_heval_iff : forall p x, pu_heval p x = true <-> pu_hholds p x.
Proof.
  intros p x. unfold pu_heval, pu_hholds.
  destruct (pu_unpair x) as [[m v] |]; [apply E.eval_iff | split; [discriminate | tauto]].
Qed.

Theorem pu_heval_pair : forall p v, pu_heval PSlot (pu_pair (pu_pcode p) v) = E.eval p v.
Proof. intros p v. unfold pu_heval. rewrite pu_unpair_pair, pu_pdec_pcode. reflexivity. Qed.

Theorem pu_hholds_pair : forall p v, pu_hholds PSlot (pu_pair (pu_pcode p) v) <-> E.holds p v.
Proof. intros p v. unfold pu_hholds. rewrite pu_unpair_pair, pu_pdec_pcode. tauto. Qed.

Theorem pu_heval_zero : pu_heval PSlot 0 = false.
Proof. reflexivity. Qed.

(* A counter satisfies PSlot exactly when it holds the code of a guest
   claim together with a value the claim holds of. *)
Theorem pu_hholds_iff : forall x,
  pu_hholds PSlot x <-> exists p v, x = pu_pair (pu_pcode p) v /\ E.holds p v.
Proof.
  intro x. split.
  - intro H. unfold pu_hholds in H.
    destruct (pu_unpair x) as [[m v] |] eqn:Hu; [| destruct H].
    exists (pu_pdec m), v. rewrite pu_pcode_pdec. split; [| exact H].
    apply pu_unpair_sound, Hu.
  - intros [p [v [-> Hh]]]. apply pu_hholds_pair, Hh.
Qed.

(* ================================================================= *)
(* Guest instructions as numbers.                                     *)
(* ================================================================= *)

Definition pu_icode (i : E.instr) : nat :=
  match i with
  | E.INC c => pu_pair 0 (pu_ccode c)
  | E.DEC c j => pu_pair 1 (pu_pair (pu_ccode c) j)
  | E.HALT => pu_pair 2 0
  | E.CHECK p c => pu_pair 3 (pu_pair (pu_ccode c) (pu_pcode p))
  | E.COMMIT p c => pu_pair 4 (pu_pair (pu_ccode c) (pu_pcode p))
  | E.CERTIFY => pu_pair 5 0
  | E.PAY => pu_pair 6 0
  end.

Definition pu_idecode (x : nat) : option E.instr :=
  match pu_unpair x with
  | Some (0, a) => option_map E.INC (pu_cdec a)
  | Some (1, a) =>
      match pu_unpair a with
      | Some (c, j) => option_map (fun c => E.DEC c j) (pu_cdec c)
      | None => None
      end
  | Some (2, 0) => Some E.HALT
  | Some (3, a) =>
      match pu_unpair a with
      | Some (c, q) => option_map (fun c => E.CHECK (pu_pdec q) c) (pu_cdec c)
      | None => None
      end
  | Some (4, a) =>
      match pu_unpair a with
      | Some (c, q) => option_map (fun c => E.COMMIT (pu_pdec q) c) (pu_cdec c)
      | None => None
      end
  | Some (5, 0) => Some E.CERTIFY
  | Some (6, 0) => Some E.PAY
  | _ => None
  end.

Theorem pu_idecode_icode : forall i, pu_idecode (pu_icode i) = Some i.
Proof.
  intros [c | c j | | p c | p c | |]; unfold pu_idecode, pu_icode;
    rewrite ?pu_unpair_pair, ?pu_cdec_ccode, ?pu_pdec_pcode; reflexivity.
Qed.

(* idecode reads back only codes: whatever it decodes was that code. *)
Theorem pu_idecode_sound : forall x i, pu_idecode x = Some i -> pu_icode i = x.
Proof.
  intros x i H. unfold pu_idecode in H.
  destruct (pu_unpair x) as [[o a] |] eqn:Hx; [| discriminate].
  apply pu_unpair_sound in Hx. subst x.
  destruct o as [| [| [| [| [| [| [| o]]]]]]].
  - destruct (pu_cdec a) as [c |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply pu_cdec_sound in Hc. subst. reflexivity.
  - destruct (pu_unpair a) as [[c j] |] eqn:Ha; [| discriminate].
    destruct (pu_cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply pu_cdec_sound in Hc. apply pu_unpair_sound in Ha.
    subst. reflexivity.
  - destruct a; [| discriminate]. injection H as <-. reflexivity.
  - destruct (pu_unpair a) as [[c q] |] eqn:Ha; [| discriminate].
    destruct (pu_cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply pu_cdec_sound in Hc. apply pu_unpair_sound in Ha.
    rewrite pu_pcode_pdec. subst. reflexivity.
  - destruct (pu_unpair a) as [[c q] |] eqn:Ha; [| discriminate].
    destruct (pu_cdec c) as [d |] eqn:Hc; simpl in H; [| discriminate].
    injection H as <-. simpl. apply pu_cdec_sound in Hc. apply pu_unpair_sound in Ha.
    rewrite pu_pcode_pdec. subst. reflexivity.
  - destruct a; [| discriminate]. injection H as <-. reflexivity.
  - destruct a; [| discriminate]. injection H as <-. reflexivity.
  - discriminate.
Qed.

Theorem pu_icode_inj : forall i j, pu_icode i = pu_icode j -> i = j.
Proof.
  intros i j H. apply (f_equal pu_idecode) in H. rewrite !pu_idecode_icode in H.
  injection H as ->. reflexivity.
Qed.

Lemma pu_icode_pos : forall i, 0 < pu_icode i.
Proof. intros []; apply pu_pair_pos. Qed.

(* The opcode and operand of each instruction code. *)
Lemma pu_unpair_icode : forall i, exists o a, pu_unpair (pu_icode i) = Some (o, a) /\ o <= 6.
Proof.
  intros []; simpl; eexists; eexists; (split; [apply pu_unpair_pair | lia]).
Qed.

(* ================================================================= *)
(* Programs as numbers, and the fetch the host performs.              *)
(* ================================================================= *)

Definition pu_prog_code (P : list E.instr) : nat := G.encode (map pu_icode P).

Theorem pu_prog_code_decode : forall P, G.decode (pu_prog_code P) = map pu_icode P.
Proof. intro P. unfold pu_prog_code. apply G.decode_encode. Qed.

Lemma pu_prog_code_nil : pu_prog_code [] = 0.
Proof. reflexivity. Qed.

Lemma pu_prog_code_cons : forall i P, pu_prog_code (i :: P) = pu_pair (pu_icode i) (pu_prog_code P).
Proof. intros i P. unfold pu_prog_code. simpl map. apply pu_pair_encode. Qed.

Theorem pu_prog_code_inj : forall P Q, pu_prog_code P = pu_prog_code Q -> P = Q.
Proof.
  induction P as [| i P IH]; intros [| j Q] H.
  - reflexivity.
  - rewrite pu_prog_code_nil, pu_prog_code_cons in H. pose proof (pu_pair_pos (pu_icode j) (pu_prog_code Q)).
    lia.
  - rewrite pu_prog_code_nil, pu_prog_code_cons in H. pose proof (pu_pair_pos (pu_icode i) (pu_prog_code P)).
    lia.
  - rewrite !pu_prog_code_cons in H. apply pu_pair_inj in H as [Hi HP].
    apply pu_icode_inj in Hi. apply IH in HP. subst. reflexivity.
Qed.

(* Strip k elements from a list code: the number left after k unpackings.
   A code that runs out first leaves 0. *)
Fixpoint pu_skip_code (code k : nat) : nat :=
  match k with
  | 0 => code
  | S k' => match pu_unpair code with Some (_, t) => pu_skip_code t k' | None => 0 end
  end.

(* The head of a list code after k unpackings: the k-th element. *)
Fixpoint pu_fetch_code (code : nat) (k : nat) : option nat :=
  match k with
  | 0 => option_map fst (pu_unpair code)
  | S k' => match pu_unpair code with Some (_, t) => pu_fetch_code t k' | None => None end
  end.

Lemma pu_skip_code_S : forall code k,
  pu_skip_code code (S k) =
  match pu_unpair code with Some (_, t) => pu_skip_code t k | None => 0 end.
Proof. reflexivity. Qed.

Lemma pu_fetch_code_S : forall code k,
  pu_fetch_code code (S k) =
  match pu_unpair code with Some (_, t) => pu_fetch_code t k | None => None end.
Proof. reflexivity. Qed.

(* pu_fetch_code is pu_skip_code followed by one more unpacking. *)
Theorem pu_fetch_code_skip : forall k code,
  pu_fetch_code code k = option_map fst (pu_unpair (pu_skip_code code k)).
Proof.
  induction k as [| k IH]; intro code; simpl; [reflexivity |].
  destruct (pu_unpair code) as [[h t] |]; [apply IH | reflexivity].
Qed.

Theorem pu_skip_code_encode : forall k l, pu_skip_code (G.encode l) k = G.encode (skipn k l).
Proof.
  induction k as [| k IH]; intro l; [reflexivity |].
  destruct l as [| x t].
  - reflexivity.
  - rewrite pu_skip_code_S, pu_unpair_encode_cons. apply IH.
Qed.

Theorem pu_fetch_code_encode : forall k l, pu_fetch_code (G.encode l) k = nth_error l k.
Proof.
  induction k as [| k IH]; intros [| x t].
  - reflexivity.
  - unfold pu_fetch_code. rewrite pu_unpair_encode_cons. reflexivity.
  - reflexivity.
  - rewrite pu_fetch_code_S, pu_unpair_encode_cons. apply IH.
Qed.

Lemma pu_nth_error_map_opt : forall (A B : Type) (f : A -> B) (l : list A) k,
  nth_error (map f l) k = option_map f (nth_error l k).
Proof.
  intros A B f l. induction l as [| x l IH]; intros [| k]; simpl; auto.
Qed.

Lemma pu_skipn_map_comm : forall (A B : Type) (f : A -> B) (l : list A) k,
  skipn k (map f l) = map f (skipn k l).
Proof.
  intros A B f l. induction l as [| x l IH]; intros [| k]; simpl; auto.
Qed.

(* What the host's fetch computes: the k-th unpacking of a program code is
   the code of the k-th instruction of the program (counting from 0), and
   None past the end. *)
Theorem pu_fetch_code_prog : forall P k,
  pu_fetch_code (pu_prog_code P) k = option_map pu_icode (nth_error P k).
Proof.
  intros P k. unfold pu_prog_code. rewrite pu_fetch_code_encode. apply pu_nth_error_map_opt.
Qed.

(* After k unpackings the program code is the code of the rest of the
   program. *)
Theorem pu_skip_code_prog : forall P k, pu_skip_code (pu_prog_code P) k = pu_prog_code (skipn k P).
Proof.
  intros P k. unfold pu_prog_code. rewrite pu_skip_code_encode. f_equal.
  apply pu_skipn_map_comm.
Qed.

(* One unpacking of the rest of the program: the head is the code of the
   k-th instruction and the tail is the code of the program after it. *)
Theorem pu_unpair_skip_prog : forall P k i,
  nth_error P k = Some i ->
  pu_unpair (pu_skip_code (pu_prog_code P) k) = Some (pu_icode i, pu_prog_code (skipn (S k) P)).
Proof.
  induction P as [| x P IH]; intros [| k] i H; simpl in H; try discriminate.
  - injection H as <-. change (pu_skip_code (pu_prog_code (x :: P)) 0) with (pu_prog_code (x :: P)).
    change (skipn 1 (x :: P)) with P.
    rewrite pu_prog_code_cons. apply pu_unpair_pair.
  - rewrite pu_skip_code_S, pu_prog_code_cons, pu_unpair_pair.
    change (skipn (S (S k)) (x :: P)) with (skipn (S k) P). apply IH, H.
Qed.

(* Past the end of the program, the unpacking finds 0. *)
Theorem pu_skip_prog_past_end : forall P k,
  nth_error P k = None -> pu_skip_code (pu_prog_code P) k = 0.
Proof.
  intros P k H. rewrite pu_skip_code_prog.
  apply nth_error_None in H. rewrite skipn_all2 by exact H. reflexivity.
Qed.

(* Fetch and decode together give back the guest's instruction fetch. *)
Theorem pu_fetch_decode_prog : forall P k,
  match pu_fetch_code (pu_prog_code P) k with Some x => pu_idecode x | None => None end
  = nth_error P k.
Proof.
  intros P k. rewrite pu_fetch_code_prog.
  destruct (nth_error P k); simpl; [apply pu_idecode_icode | reflexivity].
Qed.

(* The guest fetches at a 1-based pc: pc 0 fetches nothing, pc S k fetches
   the k-th instruction. *)
Theorem pu_guest_fetch_code : forall P k,
  option_map pu_icode (E.fetch P (S k)) = pu_fetch_code (pu_prog_code P) k.
Proof. intros P k. rewrite pu_fetch_code_prog. reflexivity. Qed.

(* ================================================================= *)
(* The host machine on PSlot.                                         *)
(* ================================================================= *)

(* A host run that raises the flag earned it on a PSlot claim about one
   register, by CHECK, COMMIT at the same version, CERTIFY. *)
Corollary pu_host_earned_certification_provenance :
  forall (s0 : @M.pu_state pu_hprop) (tr : list (@M.pu_instr pu_hprop)),
  M.pu_clean_start s0 -> M.cert (M.pu_run pu_hprop_eqb pu_heval tr s0) = true ->
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2 ++ M.CERTIFY :: post /\
    M.pu_check_ok pu_heval (M.core_of (M.pu_run pu_hprop_eqb pu_heval pre1 s0)) p c = true /\
    M.pu_commit_ok pu_hprop_eqb
      (M.core_of (M.pu_run pu_hprop_eqb pu_heval (pre1 ++ M.CHECK p c :: mid1) s0)) p c = true /\
    M.pu_certify_ok (M.core_of (M.pu_run pu_hprop_eqb pu_heval
      (pre1 ++ M.CHECK p c :: mid1 ++ M.COMMIT p c :: mid2) s0)) = true /\
    M.vers (M.core_of (M.pu_run pu_hprop_eqb pu_heval pre1 s0)) c
      = M.vers (M.core_of (M.pu_run pu_hprop_eqb pu_heval (pre1 ++ M.CHECK p c :: mid1) s0)) c /\
    M.pu_untouched pu_hprop_eqb pu_heval
      (M.pu_run pu_hprop_eqb pu_heval (pre1 ++ [M.CHECK p c]) s0) mid1 c.
Proof. exact (M.pu_multi_earned_certification_provenance pu_hprop_eqb pu_hprop_eqb_eq pu_heval). Qed.

(* A live host fact on PSlot about register r means r holds the code of a
   guest claim p together with a value v, and p holds of v. *)
Corollary pu_host_slot_soundness :
  forall (s0 : @M.pu_state pu_hprop) (tr : list (@M.pu_instr pu_hprop)) (f : @M.pu_fact pu_hprop),
  M.pu_clean_start s0 ->
  let k := M.core_of (M.pu_run pu_hprop_eqb pu_heval tr s0) in
  In f (M.facts k) -> M.f_ver f = M.vers k (M.f_reg f) ->
  exists p v, M.vals k (M.f_reg f) = pu_pair (pu_pcode p) v /\ E.holds p v.
Proof.
  intros s0 tr f H0 k Hin Hv.
  pose proof (M.pu_multi_checker_soundness pu_hprop_eqb pu_heval pu_hholds pu_heval_iff
                s0 tr f H0 Hin Hv) as Hh.
  destruct (M.f_prop f). apply pu_hholds_iff, Hh.
Qed.

(* A COMMIT of PSlot on register r that would succeed means r holds a
   guest claim code and a value the claim holds of. *)
Corollary pu_host_committed_slot_holds :
  forall (s0 : @M.pu_state pu_hprop) (tr : list (@M.pu_instr pu_hprop)) r,
  M.pu_clean_start s0 ->
  M.pu_commit_ok pu_hprop_eqb (M.core_of (M.pu_run pu_hprop_eqb pu_heval tr s0)) PSlot r = true ->
  exists p v, M.vals (M.core_of (M.pu_run pu_hprop_eqb pu_heval tr s0)) r = pu_pair (pu_pcode p) v
              /\ E.holds p v.
Proof.
  intros s0 tr r H0 H.
  apply pu_hholds_iff.
  exact (M.pu_multi_committed_claim_holds pu_hprop_eqb pu_hprop_eqb_eq pu_heval pu_hholds pu_heval_iff
           s0 tr PSlot r H0 H).
Qed.

(* ================================================================= *)
(* Assumption audit. Every line must print                            *)
(* "Closed under the global context".                                 *)
(* ================================================================= *)

Print Assumptions pu_unpair_pair.
Print Assumptions pu_pair_inj.
Print Assumptions pu_unpair_some.
Print Assumptions pu_unpair_none.
Print Assumptions pu_unpair_sound.
Print Assumptions pu_pair_encode.
Print Assumptions pu_g_err_write.
Print Assumptions pu_cpdec_cpcode.
Print Assumptions pu_cpcode_cpdec.
Print Assumptions pu_pdec_pcode.
Print Assumptions pu_pcode_pdec.
Print Assumptions pu_cdec_ccode.
Print Assumptions pu_heval_iff.
Print Assumptions pu_heval_pair.
Print Assumptions pu_hholds_iff.
Print Assumptions pu_idecode_icode.
Print Assumptions pu_idecode_sound.
Print Assumptions pu_icode_inj.
Print Assumptions pu_prog_code_decode.
Print Assumptions pu_prog_code_inj.
Print Assumptions pu_fetch_code_skip.
Print Assumptions pu_fetch_code_prog.
Print Assumptions pu_skip_code_prog.
Print Assumptions pu_unpair_skip_prog.
Print Assumptions pu_skip_prog_past_end.
Print Assumptions pu_fetch_decode_prog.
Print Assumptions pu_guest_fetch_code.
Print Assumptions pu_host_earned_certification_provenance.
Print Assumptions pu_host_slot_soundness.
Print Assumptions pu_host_committed_slot_holds.

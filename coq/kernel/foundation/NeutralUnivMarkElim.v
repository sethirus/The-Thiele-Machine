(** NeutralUnivMarkElim.v: a mark that reads one register adds nothing.

    On CNH, MARK r (record := record || r >= 1, one unit) is replaced by the
    six-line block

      l: DEC r (l+4);  l+1: PAY;  l+2: INC z;  l+3: DEC z (l+6);  l+4: INC r;  l+5: TICK

    which ends at line l+6 with the same registers, the record raised exactly
    when r >= 1, and exactly one unit paid, and whose two record moves sit on
    lines that never raise (PAY) or always raise (TICK).  So the line rule
    (N3) costs nothing on the ledger: whatever a zero-test mark decides, the
    program's own branch can decide at the same price.                     *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is a program equivalence on the canonical host of NeutralUnivCanon.v.
   That file and NeutralUnivDef.v connect it to ThieleComplete.v and
   NeutralComplete.v; it uses no name of the foundation chain directly. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.

Section Elim.
Variables (P : list cmove) (l r z : nat).
Hypothesis F0 : cfetch P l = Some (CDec r (l + 4)).
Hypothesis F1 : cfetch P (l + 1) = Some CPay.
Hypothesis F2 : cfetch P (l + 2) = Some (CInc z).
Hypothesis F3 : cfetch P (l + 3) = Some (CDec z (l + 6)).
Hypothesis F4 : cfetch P (l + 4) = Some (CInc r).
Hypothesis F5 : cfetch P (l + 5) = Some CTick.
Hypothesis Drz : r <> z.

Lemma next_at : forall s m, cfetch P (cpc s) = Some m -> m <> CHalt -> cnext P s = Some m.
Proof. intros s m F H. unfold cnext. rewrite F. destruct m; congruence. Qed.

Theorem mark_elim : forall s, cpc s = l -> creg s z = 0 ->
  exists n, n <= 4 /\
    let s' := hr (H:=CNH) P s n in
    cpc s' = l + 6 /\ (forall x, creg s' x = creg s x) /\
    cflag s' = cflag s || Nat.leb 1 (creg s r) /\ cled s' = S (cled s) /\
    hl (H:=CNH) P s n = 1.
Proof.
  intros [p g f d] Hp Hz. simpl in Hp, Hz. subst p.
  destruct (g r) as [| k] eqn:Gr.
  - (* zero branch: DEC falls through, PAY, INC z, DEC z jumps *)
    exists 4. split; [lia |].
    assert (E : hr (H:=CNH) P (mkcs l g f d) 4 =
                mkcs (l + 6) (upd (upd g z 1) z 0) f (S d) /\ hl (H:=CNH) P (mkcs l g f d) 4 = 1).
    { simpl. change (hnext CNH P) with (cnext P).
      rewrite (next_at (mkcs l g f d) _ F0) by discriminate. simpl. rewrite Gr.
      replace (S l) with (l + 1) by lia.
      rewrite (next_at (mkcs (l + 1) g f d) _ F1) by discriminate. simpl.
      replace (S (l + 1)) with (l + 2) by lia.
      rewrite (next_at (mkcs (l + 2) g f (S d)) _ F2) by discriminate. simpl.
      replace (S (l + 2)) with (l + 3) by lia.
      rewrite (next_at (mkcs (l + 3) (upd g z (S (g z))) f (S d)) _ F3) by discriminate. simpl.
      assert (V : upd g z (S (g z)) z = 1) by (unfold upd; rewrite Nat.eqb_refl, Hz; reflexivity).
      rewrite V, Hz. split; reflexivity. }
    destruct E as [E L]. cbv zeta. rewrite E, L. simpl.
    split; [reflexivity |]. split; [| split; [rewrite Gr; simpl; rewrite orb_false_r; reflexivity | split; reflexivity]].
    intros x. unfold upd. destruct (Nat.eqb x z) eqn:Q; [apply Nat.eqb_eq in Q; subst x; auto | reflexivity].
  - (* positive branch: DEC jumps, INC r, TICK *)
    exists 3. split; [lia |].
    assert (E : hr (H:=CNH) P (mkcs l g f d) 3 =
                mkcs (l + 6) (upd (upd g r k) r (S k)) true (S d) /\ hl (H:=CNH) P (mkcs l g f d) 3 = 1).
    { simpl. change (hnext CNH P) with (cnext P).
      rewrite (next_at (mkcs l g f d) _ F0) by discriminate. simpl. rewrite Gr.
      rewrite (next_at (mkcs (l + 4) (upd g r k) f d) _ F4) by discriminate. simpl.
      replace (S (l + 4)) with (l + 5) by lia.
      assert (V : upd g r k r = k) by (unfold upd; rewrite Nat.eqb_refl; reflexivity). rewrite V.
      rewrite (next_at (mkcs (l + 5) (upd (upd g r k) r (S k)) f d) _ F5) by discriminate. simpl.
      replace (S (l + 5)) with (l + 6) by lia. split; reflexivity. }
    destruct E as [E L]. cbv zeta. rewrite E, L. simpl.
    split; [reflexivity |]. split; [| split; [rewrite Gr; simpl; rewrite orb_true_r; reflexivity | split; reflexivity]].
    intros x. unfold upd. destruct (Nat.eqb x r) eqn:Q; [apply Nat.eqb_eq in Q; subst x; auto | reflexivity].
Qed.

End Elim.

(* MARK r itself, for comparison: one step, the same three effects. *)
Lemma mark_one : forall s r, cstep s (CMark r) =
  mkcs (S (cpc s)) (creg s) (cflag s || Nat.leb 1 (creg s r)) (S (cled s)).
Proof. reflexivity. Qed.

Print Assumptions mark_elim.

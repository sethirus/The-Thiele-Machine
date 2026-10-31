(** NeutralUnivPhantom.v: a neutral-specific cheat, the phantom rise.

    CNH plus LOW, a record move at price 1 that puts the record down.  The
    program [TICK; LOW; DEC 0 3; TICK; HALT] raises its record before the
    guest has done anything, lowers it again before the first matching
    time, and then runs the guest of C1 honestly.  It meets (N1), (N2) with
    surcharge 2, the register-host shape (N4) and the clean load (N5); every
    matching point shows the right record.  But its record rises at a point
    where the guest's record does not: the suggested "never otherwise" fails
    [phantom_rise].  What excludes it is (N0)'s permanence (and (N3)): with a
    permanent record the localization is automatic (NeutralUnivDef.naive_rise_free). *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is a cheat on the canonical host of NeutralUnivCanon.v, tested against
   the clauses of NeutralUnivDef.v. Those files connect it to
   ThieleComplete.v and NeutralComplete.v; it uses no name of the
   foundation chain directly. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.
Require Import Kernel.NeutralUnivNeed.
Require Import Minimal.NeutralComplete.

Inductive pmove : Type := PC (m : cmove) | PLow.

Definition pstep (s : cst) (m : pmove) : cst :=
  match m with PC c => cstep s c | PLow => mkcs (S (cpc s)) (creg s) false (S (cled s)) end.
Definition pcost (m : pmove) : nat := match m with PC c => ccost c | PLow => 1 end.
Lemma ptoll : forall s m, cflag s = false -> cflag (pstep s m) = true -> pcost m >= 1.
Proof. intros s [c |] H0 H1; simpl in *; [exact (ctoll s c H0 H1) | discriminate]. Qed.
Definition pnext (P : list pmove) (s : cst) : option pmove :=
  match (match cpc s with 0 => None | S k => nth_error P k end) with Some (PC CHalt) => None | o => o end.
Definition PH : host := mk_host cst pmove pstep pcost cflag ptoll (list pmove) pnext.

Definition ph_reg : reg_host PH.
Proof.
  refine (mk_rh PH cpc creg (fun _ => false) (fun m => match m with PC c => ckind c | PLow => RRec end)
            _ _ _ _ _ _ _ _).
  - intros [[r | r j | | r | |] |]; reflexivity.
  - intros s m E. discriminate E.
  - intros s m r _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as ->. simpl. auto.
  - intros s m r j _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as -> ->.
    simpl. destruct (creg s r); simpl; auto.
  - intros s m K. destruct m as [[] |]; simpl in K; try discriminate. simpl. auto.
  - intros s m _ K. destruct m as [[] |]; simpl in K; try discriminate; simpl; auto.
  - intros P s1 s2 _ Hp. simpl. unfold pnext. rewrite Hp. reflexivity.
  - intros P s E. discriminate E.
Defined.

Definition Pph : list pmove := [PC CTick; PLow; PC (CDec 0 3); PC CTick; PC CHalt].
Definition phf (m : nat) : nat := m + 2.

Theorem phantom :
  clean_template PH ph_reg ctpl /\
  halt_clause C1 PH O2 o2 2 Pph (ctpl (dcode 1)) tt (fun h => d2 (b_reg ph_reg h)) /\
  in_order C1 PH O2 o2 2 Pph (ctpl (dcode 1)) tt (fun h => d2 (b_reg ph_reg h)) phf /\
  (* a rise at time 0, before the first matching time, with the guest's record down there *)
  (hflag PH (hr (H:=PH) Pph (ctpl (dcode 1)) 0) = false /\
   hflag PH (hr (H:=PH) Pph (ctpl (dcode 1)) 1) = true /\ 0 < phf 0 /\ glat (C:=C1) tt 0 = false) /\
  (* not permanent, so not neutral-complete *)
  ~ (forall s m, hflag PH s = true -> hflag PH (hstep PH s m) = true) /\
  ~ exists raise, line_raise PH ph_reg Pph raise.
Proof.
  assert (M : forall m, m <= 3 -> match_at C1 PH O2 o2 2 Pph (ctpl (dcode 1)) tt
                                     (fun h => d2 (b_reg ph_reg h)) (phf m) m).
  { intros m Hm. destruct m as [| [| [| [|]]]]; try lia;
      (split; [reflexivity |]); (split; [reflexivity |]); (exists 2; split; [lia | reflexivity]). }
  split; [repeat split |]. split; [split |]; [| | split; [| split; [| split]]].
  - split; intros _; [exists 3; exact C1_stop | exists 5; reflexivity].
  - intros m0 Hl Hs. rewrite (C1_stop_only m0 Hl Hs). exists 5. split; [reflexivity | apply (M 3); lia].
  - split; [intros m Hl; unfold phf; lia | intros m Hl; apply M, C1_live, Hl].
  - split; [reflexivity |]. split; [reflexivity |]. split; [unfold phf; lia | reflexivity].
  - intros Hp. specialize (Hp (mkcs 1 (fun _ => 0) true 0) PLow eq_refl). discriminate Hp.
  - intros [ra Hra].
    destruct (Hra (mkcs 2 (fun _ => 0) true 0) PLow eq_refl eq_refl eq_refl) as [T | A]; [discriminate T |].
    discriminate A.
Qed.

Print Assumptions phantom.

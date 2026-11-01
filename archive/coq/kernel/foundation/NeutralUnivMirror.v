(** NeutralUnivMirror.v: (N3) at work.  A two-guest class Cy whose guests raise
    their record or not according to a register, an honest host that
    decides by its own counter computation (and meets the whole definition
    with surcharge 0), and two hosts that let a record move decide:

      oracle host   the program executes MARK 1, a record move that reads a
                    register (any predicate of the registers would do);
      mirror host   the program executes MIR, a record move that reads a
                    hidden copy of the guest's datum that the load template
                    put outside the registers.

    Both meet (N0) (N1) (N2) with surcharge 0, (N4) and (N5), and both fail
    (N3): the same program line raises the record for one guest and not
    for the other.                                                         *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

(* ================================================================= *)
(* The class: MARK 1 from registers (0, y).                           *)
(* ================================================================= *)

Definition Qy : list cmove := [CMark 1; CHalt].
Definition ycode (y : bool) : nat -> nat := cregs2 0 (if y then 1 else 0).
Definition Cy : gclass := cnh_class bool (fun _ => Qy) (fun y => ctpl (ycode y)).
Definition yobs (y : bool) (s : cst) : nat * nat := (creg s 0, creg s 1).
Definition ydec (y : bool) (rho : nat -> nat) : nat * nat := (rho 0, rho 1).

Lemma Cy_stop : forall y, gnext Cy y (grun (C:=Cy) y 1) = None.
Proof. intros []; reflexivity. Qed.

Lemma Cy_live : forall y m, live_before (C:=Cy) y m -> m <= 1.
Proof. intros y m Hl. exact (live_bound Cy y 1 m (Cy_stop y) Hl). Qed.

(* ================================================================= *)
(* The honest host: branch on register 1, then TICK or PAY.           *)
(* ================================================================= *)

Definition Py : list cmove := [CDec 1 4; CPay; CHalt; CInc 1; CTick; CHalt].
Definition yf (y : bool) (m : nat) : nat := match m with 0 => 0 | _ => if y then 3 else 2 end.

Lemma Py_nomark : forall l r, cfetch Py l <> Some (CMark r).
Proof. intros [| [| [| [| [| [| [| l]]]]]]] r; simpl; try discriminate. destruct l; discriminate. Qed.

Theorem honest_y : neutral_universal Cy CNH (fun _ => (nat * nat)%type) yobs 0.
Proof.
  exists Py, cnh_reg, (fun l => tick_at (cfetch Py l)), ctpl, ycode, ydec.
  split; [exact cnh_host_nc |]. split; [exact (cnh_line_raise_nomark Py Py_nomark) |].
  split; [exact ctpl_clean |].
  intros y. split; [split |].
  - split.
    + intros _. exists 1. exact (Cy_stop y).
    + intros _. exists (yf y 1). destruct y; reflexivity.
  - intros m0 Hl Hs. assert (m0 = 1).
    { pose proof (Cy_live y m0 Hl). destruct m0 as [| [|]]; [| reflexivity | lia].
      destruct y; discriminate Hs. }
    subst m0. exists (yf y 1). destruct y; (split; [reflexivity |]);
      (split; [reflexivity | split; [reflexivity | exists 0; split; [lia | reflexivity]]]).
  - exists (yf y). split.
    + intros m Hl. pose proof (Cy_live y (S m) Hl). destruct m; [destruct y; simpl; lia | lia].
    + intros m Hl. pose proof (Cy_live y m Hl). destruct m as [| [|]]; [| | lia];
        destruct y; (split; [reflexivity |]);
        (split; [reflexivity | exists 0; split; [lia | reflexivity]]).
Qed.

(* ================================================================= *)
(* The oracle host: the program lets MARK 1 decide.                   *)
(* ================================================================= *)

Theorem oracle_y :
  host_nc CNH cnh_reg /\ clean_template CNH cnh_reg ctpl /\
  (forall y, halt_clause Cy CNH (fun _ => (nat * nat)%type) yobs 0 Qy (ctpl (ycode y)) y
               (fun h => ydec y (b_reg cnh_reg h)) /\
             in_order Cy CNH (fun _ => (nat * nat)%type) yobs 0 Qy (ctpl (ycode y)) y
               (fun h => ydec y (b_reg cnh_reg h)) (fun m => m)) /\
  ~ exists raise, line_raise CNH cnh_reg Qy raise.
Proof.
  split; [exact cnh_host_nc |]. split; [exact ctpl_clean |]. split.
  - intros y. apply (lockstep_universal Cy CNH (fun _ => (nat * nat)%type) yobs Qy (ctpl (ycode y)) y).
    + intros s m. apply cnh_perm.
    + intros n. assert (E : hr (H:=CNH) Qy (ctpl (ycode y)) n = grun (C:=Cy) y n).
      { unfold grun. simpl gstart. generalize (ctpl (ycode y)). induction n as [| n IH]; intros s; [reflexivity |].
        simpl. change (hnext CNH Qy s) with (cnext Qy s). destruct (cnext Qy s); [apply IH | reflexivity]. }
      rewrite E. reflexivity.
    + intros n. assert (E : hr (H:=CNH) Qy (ctpl (ycode y)) n = grun (C:=Cy) y n).
      { unfold grun. simpl gstart. generalize (ctpl (ycode y)). induction n as [| n IH]; intros s; [reflexivity |].
        simpl. change (hnext CNH Qy s) with (cnext Qy s). destruct (cnext Qy s); [apply IH | reflexivity]. }
      rewrite E. reflexivity.
    + intros n. assert (E : hr (H:=CNH) Qy (ctpl (ycode y)) n = grun (C:=Cy) y n).
      { unfold grun. simpl gstart. generalize (ctpl (ycode y)). induction n as [| n IH]; intros s; [reflexivity |].
        simpl. change (hnext CNH Qy s) with (cnext Qy s). destruct (cnext Qy s); [apply IH | reflexivity]. }
      rewrite E. reflexivity.
    + intros n. unfold gledger. simpl gstart. generalize (ctpl (ycode y)).
      induction n as [| n IH]; intros s; [reflexivity |].
      simpl. change (hnext CNH Qy s) with (cnext Qy s). destruct (cnext Qy s); [| reflexivity].
      rewrite IH. reflexivity.
  - apply (cnh_mark_not_line Qy 1 1). reflexivity.
Qed.

(* In actual runs the same line raises for one guest and not the other. *)
Example oracle_decides :
  cpc (ctpl (ycode true)) = cpc (ctpl (ycode false)) /\
  cflag (hr (H:=CNH) Qy (ctpl (ycode true)) 1) = true /\
  cflag (hr (H:=CNH) Qy (ctpl (ycode false)) 1) = false.
Proof. repeat split. Qed.

(* ================================================================= *)
(* The mirror host: a record move that reads a hidden component.      *)
(* ================================================================= *)

Inductive mmove : Type := MC (m : cmove) | MIR.

Record mst : Type := mkm { mc : cst; mhid : nat }.

Definition mcost (m : mmove) : nat := match m with MC c => ccost c | MIR => 1 end.

Definition mstep (s : mst) (m : mmove) : mst :=
  match m with
  | MC c => mkm (cstep (mc s) c) (mhid s)
  | MIR => mkm (mkcs (S (cpc (mc s))) (creg (mc s)) (cflag (mc s) || Nat.leb 1 (mhid s)) (S (cled (mc s))))
               (mhid s)
  end.

Definition mflag (s : mst) : bool := cflag (mc s).

Lemma mtoll : forall s m, mflag s = false -> mflag (mstep s m) = true -> mcost m >= 1.
Proof.
  intros [c h] [x |] H0 H1; unfold mflag in *; simpl in *; [exact (ctoll c x H0 H1) | lia].
Qed.

Definition mfetch (P : list mmove) (n : nat) : option mmove :=
  match n with 0 => None | S k => nth_error P k end.

Definition mnext (P : list mmove) (s : mst) : option mmove :=
  match mfetch P (cpc (mc s)) with Some (MC CHalt) => None | o => o end.

Definition MH : host := mk_host mst mmove mstep mcost mflag mtoll (list mmove) mnext.

Definition mkind (m : mmove) : rkind := match m with MC c => ckind c | MIR => RRec end.

Definition mh_reg : reg_host MH.
Proof.
  refine (mk_rh MH (fun s => cpc (mc s)) (fun s => creg (mc s)) (fun _ => false) mkind _ _ _ _ _ _ _ _).
  - intros [[r | r j | | r | |] |]; reflexivity.
  - intros s m E. discriminate E.
  - intros s m r _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as ->.
    simpl. auto.
  - intros s m r j _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as -> ->.
    simpl. destruct (creg (mc s) r); simpl; auto.
  - intros s m K. destruct m as [[] |]; simpl in K; try discriminate. simpl. auto.
  - intros s m _ K. destruct m as [[] |]; simpl in K; try discriminate; simpl; auto.
  - intros P s1 s2 _ Hp. simpl. unfold mnext. rewrite Hp. reflexivity.
  - intros P s E. discriminate E.
Defined.

Definition mh_base : universal_base (hmach MH).
Proof.
  refine (mk_ub (hmach MH) (fun s => cwin (mc s)) (fun _ => True) (fun i => MC (ccompile i))
            (fun a b => mkm (cload a b) 0) _ _ _).
  - intros a b. reflexivity.
  - intros a b. exact I.
  - intros [c h] i _. split; [| exact I]. simpl. exact (proj1 (ub_sim cnh_base c i I)).
Defined.

Definition mh_iface : neutral_interface (hmach MH) :=
  mk_ni (hmach MH) mh_base (fun m => is_counter (mkind m)) (fun s => cled (mc s)).

Theorem mh_nc : neutral_complete_with mh_iface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |]. split.
    + intros s [c |] Hb; simpl in Hb; [| discriminate]. simpl. unfold mflag. simpl.
      apply cnh_counter_blind. destruct (ckind c); simpl in Hb; congruence.
    + intros [c h] [x |] H; simpl in *; unfold mflag in *; simpl in *; [apply cnh_perm, H | rewrite H; reflexivity].
  - intros a b. reflexivity.
  - split.
    + intros [[r | r j | | r | |] |]; reflexivity.
    + intros [[p r f l] h] [[x | x j | | x | |] |]; simpl; try lia. destruct (r x); simpl; lia.
  - exists [MC (CMark 0)], 1, 0, 0, 0. split; reflexivity.
Qed.

Theorem mh_host_nc : host_nc MH mh_reg.
Proof. exists mh_iface. split; [exact mh_nc | intros m; reflexivity]. Qed.

(* The template copies register 1 into the hidden component. *)
Definition mtpl (rho : nat -> nat) : mst := mkm (ctpl rho) (rho 1).

Lemma mtpl_clean : clean_template MH mh_reg mtpl.
Proof. repeat split. Qed.

Definition Pm : list mmove := [MIR; MC CHalt].

Lemma Pm_not_line : ~ exists raise, line_raise MH mh_reg Pm raise.
Proof.
  intros [ra Hra].
  set (s0 := mkm (mkcs 1 (fun _ => 0) false 0) 0). set (s1 := mkm (mkcs 1 (fun _ => 0) false 0) 1).
  destruct (Hra s0 MIR eq_refl eq_refl eq_refl) as [T | A0]; [discriminate T |].
  destruct (Hra s1 MIR eq_refl eq_refl eq_refl) as [T | A1]; [discriminate T |].
  simpl in A0, A1. rewrite <- A0 in A1. discriminate A1.
Qed.

Definition mf (y : bool) (m : nat) : nat := match m with 0 => 0 | _ => 1 end.

Theorem mirror_y :
  host_nc MH mh_reg /\ clean_template MH mh_reg mtpl /\
  (forall y, halt_clause Cy MH (fun _ => (nat * nat)%type) yobs 0 Pm (mtpl (ycode y)) y
               (fun h => ydec y (b_reg mh_reg h)) /\
             in_order Cy MH (fun _ => (nat * nat)%type) yobs 0 Pm (mtpl (ycode y)) y
               (fun h => ydec y (b_reg mh_reg h)) (mf y)) /\
  ~ exists raise, line_raise MH mh_reg Pm raise.
Proof.
  split; [exact mh_host_nc |]. split; [exact mtpl_clean |]. split; [| exact Pm_not_line].
  intros y. split; [split |].
  - split.
    + intros _. exists 1. exact (Cy_stop y).
    + intros _. exists 1. destruct y; reflexivity.
  - intros m0 Hl Hs. assert (m0 = 1).
    { pose proof (Cy_live y m0 Hl). destruct m0 as [| [|]]; [| reflexivity | lia].
      destruct y; discriminate Hs. }
    subst m0. exists 1. destruct y; (split; [reflexivity |]);
      (split; [reflexivity | split; [reflexivity | exists 0; split; [lia | reflexivity]]]).
  - split.
    + intros m Hl. pose proof (Cy_live y (S m) Hl). destruct m; [simpl; lia | lia].
    + intros m Hl. pose proof (Cy_live y m Hl). destruct m as [| [|]]; [| | lia];
        destruct y; (split; [reflexivity |]);
        (split; [reflexivity | exists 0; split; [lia | reflexivity]]).
Qed.

Example mirror_decides :
  cflag (mc (hr (H:=MH) Pm (mtpl (ycode true)) 1)) = true /\
  cflag (mc (hr (H:=MH) Pm (mtpl (ycode false)) 1)) = false /\
  creg (mc (hr (H:=MH) Pm (mtpl (ycode true)) 1)) 1 = 1.
Proof. repeat split. Qed.

Print Assumptions honest_y.
Print Assumptions oracle_y.
Print Assumptions mirror_y.

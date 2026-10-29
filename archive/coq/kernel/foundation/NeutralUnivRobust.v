(** NeutralUnivRobust.v: the neutral definition against hidden-copy hosts.

    XH Z zc rf zr: CNH with an extra component z : Z (any type), updated by
    zc at every CNH move (so a counter move may step a hidden copy of the
    guest), plus one extra record move XR at price 1 (registers alone, next
    line) that raises iff rf holds of the state and z, and updates z by zr.
    XH is neutral-complete (xh_nc) and a register host (xh_reg) for EVERY
    choice of Z, zc, rf, zr: N0 and N4 are blind to the hidden part.

    (1) Neutral shadow: Z = a hidden copy of the guest, stepped by every
        DEC 0 (a guest step built into a counter move), program = the honest
        [DEC 0 1; TICK; HALT].  It meets the whole definition with
        surcharge 0 (shadow_universal), the copy really is stepped
        (shadow_steps), and the copy is idle: the host's line, registers,
        record and ledger are those of the plain CNH run (shadow_idle).
        The definition accepts it, and what it accepts is harmless.

    (2) Neutral mirror, register-honest: the register computation is the
        honest countdown, but the raise is made by XR, which carries out
        the hidden copy's own next record move (MARK 1 on the copy) and
        raises iff that move raised the copy's record.  It meets N0, N1,
        N2 (surcharge 0), N4, N5 and the suggested "earned again", the copy
        is really stepped by the host's own record move (mirror_carries),
        and it FAILS N3 (mirror2_not_line): the line of XR raises from one
        state and not from another with the same line, registers and record.

    What each clause secures (proved in NeutralUnivDef/NeutralUnivNeed/here):
      N4  the line and registers of a run, hence control flow and halting
          before a trap, come from counter moves (rh_base_determined);
      N3+N4  so does the record, and the ledger (nr_determined): no hidden
          part, however it is stepped, can affect what the host shows before
          a trap; a hidden-copy host meeting them is a register host with an
          idle passenger (shadow_idle);
      N3  excludes every host whose rise is decided by anything but the
          program line: oracle (NeutralUnivMirror.oracle_y), hidden datum
          (NeutralUnivMirror.mirror_y), hidden guest copy (mirror2_not_line).      *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivTools.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

Section XH.
Variable Z : Type.
Variable z00 : Z.
Variable zc : cst -> cmove -> Z -> Z.
Variable rf : cst -> Z -> bool.
Variable zr : cst -> Z -> Z.

Inductive xmv : Type := XC (m : cmove) | XR.

Definition xst : Type := (cst * Z)%type.

Definition xstep (s : xst) (m : xmv) : xst :=
  match m with
  | XC c => (cstep (fst s) c, zc (fst s) c (snd s))
  | XR => (mkcs (S (cpc (fst s))) (creg (fst s)) (cflag (fst s) || rf (fst s) (snd s)) (S (cled (fst s))),
           zr (fst s) (snd s))
  end.

Definition xcost (m : xmv) : nat := match m with XC c => ccost c | XR => 1 end.
Definition xflag (s : xst) : bool := cflag (fst s).

Lemma xtoll : forall s m, xflag s = false -> xflag (xstep s m) = true -> xcost m >= 1.
Proof. intros [c z] [m |] H0 H1; unfold xflag in *; simpl in *; [exact (ctoll c m H0 H1) | lia]. Qed.

Definition xfetch (P : list xmv) (n : nat) : option xmv :=
  match n with 0 => None | S k => nth_error P k end.
Definition xnext (P : list xmv) (s : xst) : option xmv :=
  match xfetch P (cpc (fst s)) with Some (XC CHalt) => None | o => o end.

Definition XH : host := mk_host xst xmv xstep xcost xflag xtoll (list xmv) xnext.

Definition xkind (m : xmv) : rkind := match m with XC c => ckind c | XR => RRec end.

Definition xh_reg : reg_host XH.
Proof.
  refine (mk_rh XH (fun s => cpc (fst s)) (fun s => creg (fst s)) (fun _ => false) xkind _ _ _ _ _ _ _ _).
  - intros [[r | r j | | r | |] |]; reflexivity.
  - intros s m E. discriminate E.
  - intros s m r _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as ->. simpl. auto.
  - intros s m r j _ K. destruct m as [[] |]; simpl in K; try discriminate. injection K as -> ->.
    simpl. destruct (creg (fst s) r); simpl; auto.
  - intros s m K. destruct m as [[] |]; simpl in K; try discriminate. simpl. auto.
  - intros s m _ K. destruct m as [[] |]; simpl in K; try discriminate; simpl; auto.
  - intros P s1 s2 _ Hp. simpl. unfold xnext. rewrite Hp. reflexivity.
  - intros P s E. discriminate E.
Defined.

Definition xh_base : universal_base (hmach XH).
Proof.
  refine (mk_ub (hmach XH) (fun s => cwin (fst s)) (fun _ => True) (fun i => XC (ccompile i))
            (fun a b => (cload a b, z00)) _ _ _).
  - intros a b. reflexivity.
  - intros a b. exact I.
  - intros [c z] i _. split; [| exact I]. simpl. exact (proj1 (ub_sim cnh_base c i I)).
Defined.

Definition xh_iface : neutral_interface (hmach XH) :=
  mk_ni (hmach XH) xh_base (fun m => is_counter (xkind m)) (fun s => cled (fst s)).

Theorem xh_nc : neutral_complete_with xh_iface.
Proof.
  split; [| split; [| split]].
  - split; [intros [[|] | [|] j]; reflexivity |]. split.
    + intros s [c |] Hb; simpl in Hb; [| discriminate]. simpl. unfold xflag. simpl.
      apply cnh_counter_blind. destruct (ckind c); simpl in Hb; congruence.
    + intros [c z] [x |] H; simpl in *; unfold xflag in *; simpl in *; [apply cnh_perm, H | rewrite H; reflexivity].
  - intros a b. reflexivity.
  - split.
    + intros [[r | r j | | r | |] |]; reflexivity.
    + intros [[p r f l] z] [[x | x j | | x | |] |]; simpl; try lia. destruct (r x); simpl; lia.
  - exists [XC (CMark 0)], 1, 0, 0, 0. split; reflexivity.
Qed.

Theorem xh_host_nc : host_nc XH xh_reg.
Proof. exists xh_iface. split; [exact xh_nc | intros m; reflexivity]. Qed.

(* Programs of plain CNH moves: the visible part runs as on CNH. *)
Lemma xh_lift : forall (Q : list cmove) n s z,
  fst (hr (H:=XH) (map XC Q) (s, z) n) = hr (H:=CNH) Q s n /\
  hl (H:=XH) (map XC Q) (s, z) n = hl (H:=CNH) Q s n /\
  (hnext XH (map XC Q) (hr (H:=XH) (map XC Q) (s, z) n) = None <->
   hnext CNH Q (hr (H:=CNH) Q s n) = None).
Proof.
  assert (F : forall Q l, xfetch (map XC Q) l = option_map XC (cfetch Q l)).
  { intros Q [| l]; [reflexivity |]. simpl. apply nth_error_map. }
  assert (N : forall Q s z, xnext (map XC Q) (s, z) = option_map XC (cnext Q s)).
  { intros Q s z. unfold xnext, cnext. simpl. rewrite F. destruct (cfetch Q (cpc s)) as [[] |]; reflexivity. }
  intros Q n. induction n as [| n IH]; intros s z.
  - split; [reflexivity |]. split; [reflexivity |].
    change (xnext (map XC Q) (s, z) = None <-> cnext Q s = None). rewrite N.
    destruct (cnext Q s); simpl; split; intros; congruence.
  - assert (NX : hnext XH (map XC Q) (s, z) = option_map XC (cnext Q s)) by exact (N Q s z).
    change (hnext CNH Q s) with (cnext Q s) in *.
    cbn [hr hl]. rewrite NX. change (hnext CNH Q s) with (cnext Q s).
    destruct (cnext Q s) as [m |] eqn:Em; cbn [option_map].
    + destruct (IH (cstep s m) (zc s m z)) as (A & B & C').
      split; [exact A |]. split; [simpl; rewrite B; reflexivity | exact C'].
    + split; [reflexivity |]. split; [reflexivity |].
      change (hnext XH (map XC Q) (s, z) = None <-> cnext Q s = None). rewrite NX, Em. simpl.
      split; intros; reflexivity.
Qed.

Lemma xh_line_raise_XC : forall Q, (forall l r, cfetch Q l <> Some (CMark r)) ->
  line_raise XH xh_reg (map XC Q) (fun l => tick_at (cfetch Q l)).
Proof.
  intros Q Hm [s z] m _ Hn K. right. simpl in *. unfold xnext, xfetch in Hn.
  cbn [fst] in Hn. destruct (cpc s) as [| l] eqn:P; [simpl in Hn; discriminate |]. rewrite nth_error_map in Hn.
  destruct (nth_error Q l) as [o |] eqn:E; [| simpl in Hn; discriminate]. simpl in Hn.
  assert (Fq : cfetch Q (S l) = Some o) by exact E.
  destruct o as [x | x j | | x | |]; try (injection Hn as <-); try discriminate; simpl in *; unfold xflag; simpl.
  - exfalso. exact (Hm (S l) x Fq).
  - rewrite Fq. simpl. rewrite orb_true_r. reflexivity.
  - rewrite Fq. simpl. rewrite orb_false_r. reflexivity.
Qed.

Definition xtpl (zinit : (nat -> nat) -> Z) (rho : nat -> nat) : xst := (ctpl rho, zinit rho).

Lemma xtpl_clean : forall zinit, clean_template XH xh_reg (xtpl zinit).
Proof. intros zinit. repeat split. Qed.

End XH.


(* ================================================================= *)
(* (1) The neutral shadow: a hidden guest copy stepped by DEC 0.      *)
(* ================================================================= *)

Definition gstep_hidden (g : cst) : cst := match cnext Qd g with Some m => cstep g m | None => g end.
Definition szc (s : cst) (c : cmove) (g : cst) : cst :=
  match c with CDec 0 _ => gstep_hidden g | _ => g end.
Definition SH : host := XH cst szc (fun _ _ => false) (fun _ g => g).
Definition sreg : reg_host SH := xh_reg cst szc (fun _ _ => false) (fun _ g => g).

Theorem shadow_universal : neutral_universal Cdown SH (fun _ => (nat * nat)%type) dobs 0.
Proof.
  exists (map XC Pd), sreg, (fun l => tick_at (cfetch Pd l)), (xtpl cst ctpl), dcode, (fun _ rho => (rho 0, rho 1)).
  split; [exact (xh_host_nc cst (ctpl (fun _ => 0)) szc (fun _ _ => false) (fun _ g => g)) |].
  split; [apply xh_line_raise_XC; intros [| [| [| [| l]]]] r; simpl; try discriminate; destruct l; discriminate |].
  split; [apply xtpl_clean |].
  intros x. destruct (down_universal) as (P & R & ra & tpl & code & dec & _ & _ & _ & _). clear P R ra tpl code dec.
  assert (H1 : creg (ctpl (dcode x)) 1 = 1) by reflexivity.
  assert (L : forall n, hr (H:=CNH) Pd (ctpl (dcode x)) n = grun (C:=Cdown) x n /\
                        hl (H:=CNH) Pd (ctpl (dcode x)) n = gledger (C:=Cdown) x n).
  { intros n. destruct (down_lockstep n _ H1) as (A & B & _).
    change (grun (C:=Cdown) x n) with (gr (C:=Cdown) (i:=x) (ctpl (dcode x)) n).
    change (gledger (C:=Cdown) x n) with (gl (C:=Cdown) (i:=x) (ctpl (dcode x)) n).
    rewrite (down_gr_any x), (down_gl_any x). split; [exact A | exact B]. }
  pose proof (fun n => xh_lift cst szc (fun _ _ => false) (fun _ g => g) Pd n
                         (ctpl (dcode x)) (ctpl (dcode x))) as XL.
  destruct (lockstep_universal Cdown SH (fun _ => (nat * nat)%type) dobs (map XC Pd) (xtpl cst ctpl (dcode x)) x
              (fun h => (b_reg sreg h 0, b_reg sreg h 1))) as [Hh Ho].
  - intros s m Hs. destruct s as [p r f l]; simpl in Hs; subst f.
    destruct m as [y | y j | | y | |]; simpl; auto. destruct (r y); reflexivity.
  - intros n. destruct (XL n) as (_ & _ & E). unfold xtpl. rewrite E, (proj1 (L n)).
    change (hnext CNH Pd) with (cnext Pd). change (gnext Cdown x) with (cnext Qd).
    pose proof (down_step (grun (C:=Cdown) x n)) as D.
    assert (Hr : creg (grun (C:=Cdown) x n) 1 = 1).
    { rewrite <- (proj1 (L n)). exact (proj2 (proj2 (down_lockstep n _ H1))). }
    specialize (D Hr). set (g := grun (C:=Cdown) x n) in *.
    destruct (cnext Pd g), (cnext Qd g); try contradiction; split; intros; first [reflexivity | congruence].
  - intros n. assert (Hf : fst (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode x)) n) = grun (C:=Cdown) x n)
      by (destruct (XL n) as (A & _ & _); exact (eq_trans A (proj1 (L n)))).
    change ((creg (fst (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode x)) n)) 0,
             creg (fst (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode x)) n)) 1) = dobs x (grun (C:=Cdown) x n)).
    rewrite Hf. reflexivity.
  - intros n. assert (Hf : fst (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode x)) n) = grun (C:=Cdown) x n)
      by (destruct (XL n) as (A & _ & _); exact (eq_trans A (proj1 (L n)))).
    change (cflag (fst (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode x)) n)) = cflag (grun (C:=Cdown) x n)).
    rewrite Hf. reflexivity.
  - intros n. destruct (XL n) as (_ & B & _). exact (eq_trans B (proj2 (L n))).
  - split; [exact Hh |]. exists (fun m => m). exact Ho.
Qed.

(* The copy is really stepped by the host's counter move ... *)
Example shadow_steps :
  snd (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode 2)) 1) = gstep_hidden (ctpl (dcode 2)) /\
  creg (snd (hr (H:=SH) (map XC Pd) (xtpl cst ctpl (dcode 2)) 1)) 0 = 1.
Proof. split; reflexivity. Qed.

(* ... and it is idle: whatever it holds, the visible run is CNH's. *)
Theorem shadow_idle : forall n s g g',
  fst (hr (H:=SH) (map XC Pd) (s, g) n) = fst (hr (H:=SH) (map XC Pd) (s, g') n) /\
  hl (H:=SH) (map XC Pd) (s, g) n = hl (H:=SH) (map XC Pd) (s, g') n.
Proof.
  intros n s g g'.
  destruct (xh_lift cst szc (fun _ _ => false) (fun _ g => g) Pd n s g) as (A & B & _).
  destruct (xh_lift cst szc (fun _ _ => false) (fun _ g => g) Pd n s g') as (A' & B' & _).
  exact (conj (eq_trans A (eq_sym A')) (eq_trans B (eq_sym B'))).
Qed.

(* ================================================================= *)
(* (2) The register-honest neutral mirror.                            *)
(* ================================================================= *)

(* Guests: [DEC 0 1; MARK 1; HALT] from (x, y): count down, then raise iff y >= 1. *)
Definition Cxy : gclass := cnh_class (nat * bool) (fun _ => Qd)
  (fun i => ctpl (cregs2 (fst i) (if snd i then 1 else 0))).
Definition xycode (i : nat * bool) : nat -> nat := cregs2 (fst i) (if snd i then 1 else 0).

(* XR carries out the hidden copy's next record move, raising iff it raises the copy's record. *)
Definition mrf (s : cst) (g : cst) : bool :=
  match cnext Qd g with
  | Some (CMark r) => cflag (cstep g (CMark r))
  | Some CTick => true
  | _ => false
  end.
Definition mzr (s : cst) (g : cst) : cst :=
  match cnext Qd g with Some (CMark r) => cstep g (CMark r) | Some CTick => cstep g CTick
                      | Some CPay => cstep g CPay | _ => g end.

Definition MH2 : host := XH cst szc mrf mzr.
Definition mreg2 : reg_host MH2 := xh_reg cst szc mrf mzr.

Definition Pmir : list xmv := [XC (CDec 0 1); XR; XC CHalt].

(* The host's whole state is (guest, guest) at every time. *)
Lemma mir_step : forall g,
  match hnext MH2 Pmir (g, g), cnext Qd g with
  | None, None => True
  | Some a, Some b => hstep MH2 (g, g) a = (cstep g b, cstep g b) /\ hcost MH2 a = ccost b
  | _, _ => False
  end.
Proof.
  intros [p r f l]. simpl. unfold xnext, xfetch, cnext, cfetch. simpl.
  destruct p as [| [| [| [| p]]]]; simpl; auto.
  all: try (destruct p; simpl; auto; fail).
  all: unfold szc, gstep_hidden, mrf, mzr, cnext, cfetch; simpl; try rewrite orb_assoc, orb_diag; split; reflexivity.
Qed.

Lemma mir_run : forall n g,
  hr (H:=MH2) Pmir (g, g) n = (gr (C:=Cxy) (i:=(0, false)) g n, gr (C:=Cxy) (i:=(0, false)) g n) /\
  hl (H:=MH2) Pmir (g, g) n = gl (C:=Cxy) (i:=(0, false)) g n /\
  (hnext MH2 Pmir (hr (H:=MH2) Pmir (g, g) n) = None <-> cnext Qd (gr (C:=Cxy) (i:=(0, false)) g n) = None).
Proof.
  induction n as [| n IH]; intros g.
  - split; [reflexivity |]. split; [reflexivity |]. pose proof (mir_step g) as D.
    change (hr (H:=MH2) Pmir (g, g) 0) with (g, g). change (gr (C:=Cxy) (i:=(0, false)) g 0) with g.
    destruct (hnext MH2 Pmir (g, g)), (cnext Qd g); try contradiction;
      split; intros; first [reflexivity | congruence].
  - pose proof (mir_step g) as D.
    change (hr (H:=MH2) Pmir (g, g) (S n)) with
      (match hnext MH2 Pmir (g, g) with None => (g, g) | Some m => hr (H:=MH2) Pmir (hstep MH2 (g, g) m) n end).
    change (hl (H:=MH2) Pmir (g, g) (S n)) with
      (match hnext MH2 Pmir (g, g) with None => 0 | Some m => hcost MH2 m + hl (H:=MH2) Pmir (hstep MH2 (g, g) m) n end).
    change (gr (C:=Cxy) (i:=(0, false)) g (S n)) with
      (match cnext Qd g with None => g | Some m => gr (C:=Cxy) (i:=(0, false)) (cstep g m) n end).
    change (gl (C:=Cxy) (i:=(0, false)) g (S n)) with
      (match cnext Qd g with None => 0 | Some m => ccost m + gl (C:=Cxy) (i:=(0, false)) (cstep g m) n end).
    destruct (hnext MH2 Pmir (g, g)) as [a |] eqn:Ea, (cnext Qd g) as [b |] eqn:Eb; try contradiction.
    + destruct D as [E C']. rewrite E, C'.
      destruct (IH (cstep g b)) as (A & B & N). split; [exact A |]. split; [rewrite B; reflexivity | exact N].
    + split; [reflexivity |]. split; [reflexivity |]. rewrite Ea, Eb. split; intros; reflexivity.
Qed.

Lemma Cxy_gr_any : forall i s n, gr (C:=Cxy) (i:=i) s n = gr (C:=Cxy) (i:=(0, false)) s n.
Proof. intros i s n. revert s. induction n; intros s; simpl; [reflexivity |]. destruct (cnext Qd s); auto. Qed.
Lemma Cxy_gl_any : forall i s n, gl (C:=Cxy) (i:=i) s n = gl (C:=Cxy) (i:=(0, false)) s n.
Proof. intros i s n. revert s. induction n; intros s; simpl; [reflexivity |]. destruct (cnext Qd s); auto. Qed.

Theorem mirror2_meets_rest : forall i,
  host_nc MH2 mreg2 /\ clean_template MH2 mreg2 (xtpl cst ctpl) /\
  halt_clause Cxy MH2 (fun _ => (nat * nat)%type) (fun _ s => (creg s 0, creg s 1)) 0 Pmir
    (xtpl cst ctpl (xycode i)) i (fun h => (b_reg mreg2 h 0, b_reg mreg2 h 1)) /\
  in_order Cxy MH2 (fun _ => (nat * nat)%type) (fun _ s => (creg s 0, creg s 1)) 0 Pmir
    (xtpl cst ctpl (xycode i)) i (fun h => (b_reg mreg2 h 0, b_reg mreg2 h 1)) (fun m => m).
Proof.
  intros i. split; [exact (xh_host_nc cst (ctpl (fun _ => 0)) szc mrf mzr) |]. split; [apply xtpl_clean |].
  set (g0 := ctpl (xycode i)).
  assert (X : forall n, hr (H:=MH2) Pmir (xtpl cst ctpl (xycode i)) n = (grun (C:=Cxy) i n, grun (C:=Cxy) i n) /\
                        hl (H:=MH2) Pmir (xtpl cst ctpl (xycode i)) n = gledger (C:=Cxy) i n /\
                        (hnext MH2 Pmir (hr (H:=MH2) Pmir (xtpl cst ctpl (xycode i)) n) = None <->
                         gnext Cxy i (grun (C:=Cxy) i n) = None)).
  { intros n. destruct (mir_run n g0) as (A & B & N).
    pose proof (Cxy_gr_any i g0 n) as G. pose proof (Cxy_gl_any i g0 n) as G'.
    change (xtpl cst ctpl (xycode i)) with (g0, g0).
    change (grun (C:=Cxy) i n) with (gr (C:=Cxy) (i:=i) g0 n).
    change (gledger (C:=Cxy) i n) with (gl (C:=Cxy) (i:=i) g0 n).
    change (gnext Cxy i) with (cnext Qd).
    rewrite G, G'. exact (conj A (conj B N)). }
  apply (lockstep_universal Cxy MH2 (fun _ => (nat * nat)%type) (fun _ s => (creg s 0, creg s 1)) Pmir
           (xtpl cst ctpl (xycode i)) i (fun h => (b_reg mreg2 h 0, b_reg mreg2 h 1))).
  - intros s m. apply cnh_perm.
  - intros n. exact (proj2 (proj2 (X n))).
  - intros n. destruct (X n) as (A & _ & _). rewrite A. reflexivity.
  - intros n. destruct (X n) as (A & _ & _). rewrite A. reflexivity.
  - intros n. exact (proj1 (proj2 (X n))).
Qed.

(* The copy's own record move is carried out by the host's record move. *)
Example mirror_carries :
  snd (hr (H:=MH2) Pmir (xtpl cst ctpl (xycode (0, true))) 2) = cstep (cstep (ctpl (xycode (0, true))) (CDec 0 1)) (CMark 1) /\
  cflag (fst (hr (H:=MH2) Pmir (xtpl cst ctpl (xycode (0, true))) 2)) = true /\
  cflag (fst (hr (H:=MH2) Pmir (xtpl cst ctpl (xycode (0, false))) 2)) = false.
Proof. repeat split. Qed.

(* N3 excludes it: at line 2 the same move raises from one state and not
   from another with the same line, registers and record. *)
Theorem mirror2_not_line : ~ exists raise, line_raise MH2 mreg2 Pmir raise.
Proof.
  intros [ra Hra].
  set (v := mkcs 2 (fun _ => 0) false 0).
  set (g1 := mkcs 2 (fun _ => 1) false 0).
  destruct (Hra (v, g1) XR eq_refl eq_refl eq_refl) as [T | A1]; [discriminate T |].
  destruct (Hra (v, v) XR eq_refl eq_refl eq_refl) as [T | A0]; [discriminate T |].
  simpl in A0, A1. unfold xflag in A0, A1. simpl in A0, A1. rewrite <- A0 in A1. discriminate A1.
Qed.

Print Assumptions xh_nc.
Print Assumptions shadow_universal.
Print Assumptions shadow_idle.
Print Assumptions mirror2_meets_rest.
Print Assumptions mirror2_not_line.

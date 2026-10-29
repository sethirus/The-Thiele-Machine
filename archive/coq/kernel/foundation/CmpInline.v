(** CmpInline.v: the first compiler stage, from programs with procedure
    calls to programs without calls, in one global variable space.

    A call in a frame that starts at variable base and has nv variables is
    replaced by: assignments that load the arguments into the callee frame
    (which starts at base + nv and has cmp_procsz pr variables), assignments
    that set the other locals of the callee to 0, the callee body compiled
    the same way in the callee frame, and assignments that copy the results
    into the caller's variables. Every variable x of a frame is the global
    variable base + x. Calls nest to the depth given by the fuel n; the fuel
    is large enough when every called procedure number is below it
    (cmp_wfs) and every procedure only calls smaller numbers (cmp_wfp).

    A frame of a global state G: the frame (base, nv) of G is the function
    x |-> G (base + x) on x < nv. The statement of both directions is that a
    run of the original from e and a run of the compiled program from G
    correspond when the frame of G is e, with the result again in the frame,
    and with every variable below base untouched:

      cmp_inl_fwd   a derivation of the original gives a derivation of the
                    compiled program
      cmp_inl_bwd   a derivation of the compiled program gives a derivation
                    of the original (so a program that does not halt
                    compiles to one that does not halt)

    The compiled program is call free (cmp_inl_nocall).

    Dependencies: Coq standard library and CmpLang.v. No axioms and no
    unfinished proofs.                                                              *)

(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this file
   is one stage of the verified compiler pipeline of CmpPipeline.v and
   imports only the Coq standard library and CmpLang.v. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.CmpLang.

(* ================================================================= *)
(* Renaming variables.                                                *)
(* ================================================================= *)

Fixpoint cmp_ashift (b : nat) (a : cmp_aexp) : cmp_aexp :=
  match a with
  | CNum n => CNum n
  | CVar x => CVar (b + x)
  | CAdd a c => CAdd (cmp_ashift b a) (cmp_ashift b c)
  | CSub a c => CSub (cmp_ashift b a) (cmp_ashift b c)
  end.

Fixpoint cmp_bshift (b : nat) (c : cmp_bexp) : cmp_bexp :=
  match c with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq x y => BEq (cmp_ashift b x) (cmp_ashift b y)
  | BLt x y => BLt (cmp_ashift b x) (cmp_ashift b y)
  | BNot c => BNot (cmp_bshift b c)
  | BAnd c d => BAnd (cmp_bshift b c) (cmp_bshift b d)
  | BOr c d => BOr (cmp_bshift b c) (cmp_bshift b d)
  end.

Lemma cmp_ashift_eval : forall b a G, cmp_aeval G (cmp_ashift b a) = cmp_aeval (fun x => G (b + x)) a.
Proof. induction a; intros G; simpl; auto. Qed.

Lemma cmp_bshift_eval : forall b c G, cmp_beval G (cmp_bshift b c) = cmp_beval (fun x => G (b + x)) c.
Proof.
  induction c; intros G; simpl; auto;
    try (rewrite !cmp_ashift_eval; reflexivity);
    try (rewrite IHc; reflexivity);
    try (rewrite IHc1, IHc2; reflexivity).
Qed.

Lemma cmp_ashift_max : forall b a, cmp_avmax (cmp_ashift b a) <= b + cmp_avmax a.
Proof. induction a; simpl; lia. Qed.

Lemma cmp_bshift_max : forall b c, cmp_bvmax (cmp_bshift b c) <= b + cmp_bvmax c.
Proof.
  intros b c. induction c as [| | x y | x y | c IH | c1 IH1 c2 IH2 | c1 IH1 c2 IH2]; simpl; try lia.
  - pose proof (cmp_ashift_max b x). pose proof (cmp_ashift_max b y). lia.
  - pose proof (cmp_ashift_max b x). pose proof (cmp_ashift_max b y). lia.
Qed.

Lemma cmp_aeval_below : forall a G1 G2,
  (forall r, r < cmp_avmax a -> G1 r = G2 r) -> cmp_aeval G1 a = cmp_aeval G2 a.
Proof.
  induction a as [n | x | a1 IH1 a2 IH2 | a1 IH1 a2 IH2]; intros G1 G2 H; simpl in *.
  - reflexivity.
  - apply H. lia.
  - rewrite (IH1 G1 G2), (IH2 G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
  - rewrite (IH1 G1 G2), (IH2 G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
Qed.

Lemma cmp_beval_below : forall c G1 G2,
  (forall r, r < cmp_bvmax c -> G1 r = G2 r) -> cmp_beval G1 c = cmp_beval G2 c.
Proof.
  induction c as [| | x y | x y | c IH | c1 IH1 c2 IH2 | c1 IH1 c2 IH2]; intros G1 G2 H; simpl in *.
  - reflexivity.
  - reflexivity.
  - rewrite (cmp_aeval_below x G1 G2), (cmp_aeval_below y G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
  - rewrite (cmp_aeval_below x G1 G2), (cmp_aeval_below y G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
  - rewrite (IH G1 G2); [reflexivity | exact H].
  - rewrite (IH1 G1 G2), (IH2 G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
  - rewrite (IH1 G1 G2), (IH2 G1 G2); [reflexivity | |]; intros r Hr; apply H; lia.
Qed.

(* ================================================================= *)
(* Straight-line assignments.                                         *)
(* ================================================================= *)

Definition cmp_asg (p : nat * cmp_aexp) : cmp_stmt := SAssign (fst p) (snd p).

Fixpoint cmp_seqs (l : list cmp_stmt) : cmp_stmt :=
  match l with [] => SSkip | s :: r => SSeq s (cmp_seqs r) end.

Definition cmp_runa (G : cmp_env) (l : list (nat * cmp_aexp)) : cmp_env :=
  fold_left (fun G p => cmp_upd G (fst p) (cmp_aeval G (snd p))) l G.

Lemma cmp_seqs_eval : forall ps l G,
  cmp_ceval ps G (cmp_seqs (map cmp_asg l)) (cmp_runa G l) (length l).
Proof.
  induction l as [| p l IH]; intros G; simpl.
  - constructor.
  - change (S (length l)) with (1 + length l).
    destruct p as [x a]. econstructor; [apply CEAssign | apply IH].
Qed.

Lemma cmp_seqs_inv : forall ps l G G1 c,
  cmp_ceval ps G (cmp_seqs (map cmp_asg l)) G1 c -> G1 = cmp_runa G l /\ c = length l.
Proof.
  induction l as [| p l IH]; intros G G1 c H; simpl in H.
  - inversion H; subst. split; reflexivity.
  - destruct p as [x a]. cbn [map cmp_seqs] in H. inversion H; subst.
    match goal with
    | [ Ha : cmp_ceval _ _ (cmp_asg _) _ _, Hb : cmp_ceval _ _ (cmp_seqs _) _ _ |- _ ] =>
        unfold cmp_asg in Ha; cbn in Ha; inversion Ha; subst;
        destruct (IH _ _ _ Hb) as [-> ->]; split; reflexivity
    end.
Qed.

Lemma cmp_runa_app : forall l1 l2 G, cmp_runa G (l1 ++ l2) = cmp_runa (cmp_runa G l1) l2.
Proof. intros. unfold cmp_runa. apply fold_left_app. Qed.

Lemma cmp_runa_cons : forall p l G,
  cmp_runa G (p :: l) = cmp_runa (cmp_upd G (fst p) (cmp_aeval G (snd p))) l.
Proof. reflexivity. Qed.

(* Assigning b + k := E k for k in i .. i + m - 1, when no E k reads a
   variable at or above b: variables outside the block are untouched ... *)
Lemma cmp_runa_block_out : forall (E : nat -> cmp_aexp) b m i G r,
  (r < b + i \/ b + i + m <= r) ->
  cmp_runa G (map (fun k => (b + k, E k)) (seq i m)) r = G r.
Proof.
  intros E b m. induction m as [| m IH]; intros i G r Hr; cbn [seq map]; [reflexivity |].
  rewrite cmp_runa_cons. cbn [fst snd]. rewrite IH by lia.
  unfold cmp_upd. destruct (Nat.eqb_spec r (b + i)); [lia | reflexivity].
Qed.

(* ... and variable b + k holds the value of E k in the old state. *)
Lemma cmp_runa_block_in : forall (E : nat -> cmp_aexp) b m i G r,
  (forall k, i <= k -> k < i + m -> cmp_avmax (E k) <= b) ->
  b + i <= r -> r < b + i + m ->
  cmp_runa G (map (fun k => (b + k, E k)) (seq i m)) r = cmp_aeval G (E (r - b)).
Proof.
  intros E b m. induction m as [| m IH]; intros i G r HE H1 H2; [lia |].
  cbn [seq map]. rewrite cmp_runa_cons. cbn [fst snd].
  destruct (Nat.eq_dec r (b + i)) as [Er | Er].
  - subst r. rewrite cmp_runa_block_out by lia. rewrite cmp_upd_same.
    replace (b + i - b) with i by lia. reflexivity.
  - rewrite IH by (try lia; intros k Hk1 Hk2; apply HE; lia).
    apply cmp_aeval_below. intros q Hq.
    assert (Hk : cmp_avmax (E (r - b)) <= b) by (apply HE; lia).
    unfold cmp_upd. destruct (Nat.eqb_spec q (b + i)); [lia | reflexivity].
Qed.

(* ================================================================= *)
(* The compiler stage.                                                *)
(* ================================================================= *)

(* The assignments before a call: parameter k of the callee frame gets
   argument k (read in the caller frame), every other local gets 0. *)
Definition cmp_pre (base nv : nat) (pr : cmp_proc) (args : list cmp_aexp) : list (nat * cmp_aexp) :=
  map (fun k => (base + nv + k, cmp_ashift base (nth k args (CNum 0)))) (seq 0 (pr_np pr))
  ++ map (fun k => (base + nv + k, CNum 0)) (seq (pr_np pr) (cmp_procsz pr - pr_np pr)).

(* The assignments after a call: result i goes to variable d_i of the caller. *)
Definition cmp_post' (base b' : nat) (ds : list nat) (rs : list cmp_aexp) : list (nat * cmp_aexp) :=
  map (fun dv => (base + fst dv, cmp_ashift b' (snd dv))) (combine ds rs).

Definition cmp_post (base nv : nat) (pr : cmp_proc) (ds : list nat) : list (nat * cmp_aexp) :=
  cmp_post' base (base + nv) ds (pr_rets pr).

(* Compile a statement of a frame (base, nv); callee compiles the body of a
   called procedure in the frame that starts at b'. *)
Fixpoint cmp_inl_aux (ps : list cmp_proc) (callee : cmp_proc -> nat -> cmp_stmt) (base nv : nat)
  (s : cmp_stmt) : cmp_stmt :=
  match s with
  | SSkip => SSkip
  | SAssign x a => SAssign (base + x) (cmp_ashift base a)
  | SSeq s t => SSeq (cmp_inl_aux ps callee base nv s) (cmp_inl_aux ps callee base nv t)
  | SIf b s t => SIf (cmp_bshift base b) (cmp_inl_aux ps callee base nv s) (cmp_inl_aux ps callee base nv t)
  | SWhile b s => SWhile (cmp_bshift base b) (cmp_inl_aux ps callee base nv s)
  | SCall ds p args =>
      match nth_error ps p with
      | None => SSkip
      | Some pr =>
          SSeq (cmp_seqs (map cmp_asg (cmp_pre base nv pr args)))
            (SSeq (callee pr (base + nv))
                  (cmp_seqs (map cmp_asg (cmp_post base nv pr ds))))
      end
  end.

(* Calls are unfolded to the depth n. A call at depth 0 leaves the callee
   body out (such programs are excluded by cmp_wf), a call to a procedure
   that does not exist compiles to nothing. *)
Fixpoint cmp_inl (ps : list cmp_proc) (n : nat) : nat -> nat -> cmp_stmt -> cmp_stmt :=
  match n with
  | 0 => fun base nv s => cmp_inl_aux ps (fun _ _ => SSkip) base nv s
  | S n' => fun base nv s =>
      cmp_inl_aux ps (fun pr b' => cmp_inl ps n' b' (cmp_procsz pr) (pr_body pr)) base nv s
  end.

Fixpoint cmp_nocall (s : cmp_stmt) : Prop :=
  match s with
  | SSkip | SAssign _ _ => True
  | SSeq s t | SIf _ s t => cmp_nocall s /\ cmp_nocall t
  | SWhile _ s => cmp_nocall s
  | SCall _ _ _ => False
  end.

Lemma cmp_seqs_nocall : forall l, cmp_nocall (cmp_seqs (map cmp_asg l)).
Proof. induction l as [| p l IH]; simpl; [exact I | split; [exact I | exact IH]]. Qed.

Theorem cmp_inl_nocall : forall ps n s base nv, cmp_nocall (cmp_inl ps n base nv s).
Proof.
  intros ps n. induction n as [| n IHn]; intros s base nv;
    induction s as [| x a | s1 IH1 s2 IH2 | b s1 IH1 s2 IH2 | b s IHs | ds p args];
    simpl; auto.
  - destruct (nth_error ps p) as [pr |]; [| exact I]. split; [apply cmp_seqs_nocall |]. split; [exact I | apply cmp_seqs_nocall].
  - destruct (nth_error ps p) as [pr |]; [| exact I]. split; [apply cmp_seqs_nocall |]. split; [apply IHn | apply cmp_seqs_nocall].
Qed.

(* ================================================================= *)
(* The assignments around a call.                                     *)
(* ================================================================= *)

Lemma cmp_lmax_ge : forall l x, In x l -> x <= cmp_lmax l.
Proof. induction l as [| y l IH]; intros x H; [destruct H |]. simpl. destruct H as [<- | H]; [lia | pose proof (IH x H); lia]. Qed.

Lemma cmp_nth_avmax : forall args k nv, cmp_lmax (map cmp_avmax args) <= nv ->
  cmp_avmax (nth k args (CNum 0)) <= nv.
Proof.
  induction args as [| a args IH]; intros k nv H; simpl in *; [destruct k; simpl; lia |].
  destruct k as [| k]; simpl; [lia |]. apply IH. lia.
Qed.

Lemma cmp_procsz_np : forall pr, pr_np pr <= cmp_procsz pr.
Proof. intros. unfold cmp_procsz. lia. Qed.

Definition cmp_view (base : nat) (G : cmp_env) : cmp_env := fun x => G (base + x).

Lemma cmp_pre_spec : forall base nv pr args G,
  cmp_lmax (map cmp_avmax args) <= nv ->
  let G' := cmp_runa G (cmp_pre base nv pr args) in
  (forall r, r < base + nv -> G' r = G r) /\
  (forall k, k < pr_np pr -> G' (base + nv + k) = cmp_aeval (cmp_view base G) (nth k args (CNum 0))) /\
  (forall k, pr_np pr <= k -> k < cmp_procsz pr -> G' (base + nv + k) = 0).
Proof.
  intros base nv pr args G Hargs G'. unfold G', cmp_pre. rewrite cmp_runa_app.
  pose proof (cmp_procsz_np pr) as Hnp.
  set (G1 := cmp_runa G (map (fun k => (base + nv + k, cmp_ashift base (nth k args (CNum 0)))) (seq 0 (pr_np pr)))).
  split; [| split].
  - intros r Hr.
    rewrite cmp_runa_block_out by lia. unfold G1. rewrite cmp_runa_block_out by lia. reflexivity.
  - intros k Hk.
    rewrite (cmp_runa_block_out (fun _ => CNum 0) (base + nv) (cmp_procsz pr - pr_np pr) (pr_np pr)) by lia.
    unfold G1. rewrite (cmp_runa_block_in (fun k => cmp_ashift base (nth k args (CNum 0))) (base + nv)
      (pr_np pr) 0 G (base + nv + k)).
    + replace (base + nv + k - (base + nv)) with k by lia. rewrite cmp_ashift_eval. apply cmp_aeval_eqv. intros x. reflexivity.
    + intros j _ _. pose proof (cmp_ashift_max base (nth j args (CNum 0))).
      pose proof (cmp_nth_avmax args j nv Hargs). lia.
    + lia.
    + lia.
  - intros k Hk1 Hk2.
    rewrite (cmp_runa_block_in (fun _ => CNum 0) (base + nv) (cmp_procsz pr - pr_np pr) (pr_np pr) G1 (base + nv + k)).
    + replace (base + nv + k - (base + nv)) with k by lia. reflexivity.
    + intros j _ _. simpl. lia.
    + lia.
    + lia.
Qed.

Lemma cmp_post_spec : forall ds rs base b' G W,
  (forall y, G (b' + y) = W y) ->
  (forall d, In d ds -> base + d < b') ->
  (forall y, cmp_runa G (cmp_post' base b' ds rs) (b' + y) = W y) /\
  (forall r, (forall d, In d ds -> r <> base + d) -> cmp_runa G (cmp_post' base b' ds rs) r = G r) /\
  (forall y, cmp_runa G (cmp_post' base b' ds rs) (base + y) =
             cmp_assigns (cmp_view base G) ds (map (cmp_aeval W) rs) y).
Proof.
  induction ds as [| d ds IH]; intros [| r rs] base b' G W HW Hd.
  - simpl. unfold cmp_post'. simpl. unfold cmp_runa. simpl. repeat split; auto.
  - simpl. unfold cmp_post'. simpl. unfold cmp_runa. simpl. repeat split; auto.
  - simpl. unfold cmp_post'. simpl. unfold cmp_runa. simpl. repeat split; auto.
  - unfold cmp_post'. cbn [combine map]. rewrite cmp_runa_cons. cbn [fst snd].
    set (v := cmp_aeval G (cmp_ashift b' r)).
    set (G1 := cmp_upd G (base + d) v).
    assert (Hd0 : base + d < b') by (apply Hd; left; reflexivity).
    assert (HW1 : forall y, G1 (b' + y) = W y).
    { intros y. unfold G1. rewrite cmp_upd_other by lia. apply HW. }
    destruct (IH rs base b' G1 W HW1 (fun d' Hin => Hd d' (or_intror Hin))) as (A & B & C).
    unfold cmp_post' in A, B, C.
    split; [exact A | split].
    + intros q Hq. rewrite B.
      * unfold G1. rewrite cmp_upd_other; [reflexivity |]. apply Hq. left. reflexivity.
      * intros d' Hin. apply Hq. right. exact Hin.
    + intros y. rewrite C. cbn [map]. cbn [cmp_assigns].
      assert (Hv : v = cmp_aeval W r).
      { unfold v. rewrite cmp_ashift_eval. apply cmp_aeval_eqv. exact HW. }
      apply cmp_assigns_eqv.
      intros z. unfold cmp_view, G1, cmp_upd. destruct (Nat.eqb_spec z d) as [-> | Hz].
      * rewrite Nat.eqb_refl. destruct (Nat.eqb_spec (base + d) (base + d)); [exact Hv | lia].
      * destruct (Nat.eqb_spec (base + z) (base + d)); [lia | reflexivity].
Qed.

(* ================================================================= *)
(* Frames.                                                            *)
(* ================================================================= *)

Definition cmp_frame (base nv : nat) (e G : cmp_env) : Prop :=
  forall x, x < nv -> G (base + x) = e x.

Lemma cmp_frame_aeval : forall a base nv e G,
  cmp_avmax a <= nv -> cmp_frame base nv e G -> cmp_aeval (cmp_view base G) a = cmp_aeval e a.
Proof.
  intros a base nv e G Ha Hf. apply cmp_aeval_below. intros r Hr. unfold cmp_view. apply Hf. lia.
Qed.

Lemma cmp_frame_beval : forall c base nv e G,
  cmp_bvmax c <= nv -> cmp_frame base nv e G -> cmp_beval (cmp_view base G) c = cmp_beval e c.
Proof.
  intros c base nv e G Hc Hf. apply cmp_beval_below. intros r Hr. unfold cmp_view. apply Hf. lia.
Qed.

Lemma cmp_wfs_mono : forall s m m', cmp_wfs m s -> m <= m' -> cmp_wfs m' s.
Proof.
  induction s; simpl; intros m m' H Hm; auto.
  - destruct H as [H1 H2]. split; [eapply IHs1 | eapply IHs2]; eauto.
  - destruct H as [H1 H2]. split; [eapply IHs1 | eapply IHs2]; eauto.
  - eapply IHs; eauto.
  - lia.
Qed.

Lemma cmp_assigns_agree : forall ds vs nv e f,
  (forall y, y < nv -> e y = f y) ->
  forall y, y < nv -> cmp_assigns e ds vs y = cmp_assigns f ds vs y.
Proof.
  induction ds as [| d ds IH]; intros [| v vs] nv e f H y Hy; simpl; auto.
  apply (IH vs nv (cmp_upd e d v) (cmp_upd f d v)); [| exact Hy]. intros z Hz. unfold cmp_upd. destruct (Nat.eqb z d); [reflexivity | apply H; exact Hz].
Qed.

Lemma cmp_inl_skip : forall ps n base nv, cmp_inl ps n base nv SSkip = SSkip.
Proof. intros ps [| n] base nv; reflexivity. Qed.
Lemma cmp_inl_assign : forall ps n base nv x a,
  cmp_inl ps n base nv (SAssign x a) = SAssign (base + x) (cmp_ashift base a).
Proof. intros ps [| n] base nv x a; reflexivity. Qed.
Lemma cmp_inl_seq : forall ps n base nv s t,
  cmp_inl ps n base nv (SSeq s t) = SSeq (cmp_inl ps n base nv s) (cmp_inl ps n base nv t).
Proof. intros ps [| n] base nv s t; reflexivity. Qed.
Lemma cmp_inl_if : forall ps n base nv b s t,
  cmp_inl ps n base nv (SIf b s t) = SIf (cmp_bshift base b) (cmp_inl ps n base nv s) (cmp_inl ps n base nv t).
Proof. intros ps [| n] base nv b s t; reflexivity. Qed.
Lemma cmp_inl_while : forall ps n base nv b s,
  cmp_inl ps n base nv (SWhile b s) = SWhile (cmp_bshift base b) (cmp_inl ps n base nv s).
Proof. intros ps [| n] base nv b s; reflexivity. Qed.
Lemma cmp_inl_call : forall ps n base nv ds p args pr,
  nth_error ps p = Some pr ->
  cmp_inl ps (S n) base nv (SCall ds p args) =
  SSeq (cmp_seqs (map cmp_asg (cmp_pre base nv pr args)))
    (SSeq (cmp_inl ps n (base + nv) (cmp_procsz pr) (pr_body pr))
          (cmp_seqs (map cmp_asg (cmp_post base nv pr ds)))).
Proof. intros ps n base nv ds p args pr H. simpl. rewrite H. reflexivity. Qed.

Lemma cmp_call_pre_frame : forall base nv pr args e G,
  cmp_lmax (map cmp_avmax args) <= nv -> cmp_frame base nv e G ->
  cmp_frame (base + nv) (cmp_procsz pr) (cmp_args pr args e) (cmp_runa G (cmp_pre base nv pr args)) /\
  (forall r, r < base + nv -> cmp_runa G (cmp_pre base nv pr args) r = G r).
Proof.
  intros base nv pr args e G Hargs Hfr.
  destruct (cmp_pre_spec base nv pr args G Hargs) as (P1 & P2 & P3).
  split; [| exact P1].
  intros x Hx. unfold cmp_args. destruct (Nat.ltb_spec x (pr_np pr)) as [Hlt | Hge].
  - rewrite (P2 x Hlt). rewrite cmp_frame_aeval with (nv := nv) (e := e);
      [reflexivity | apply cmp_nth_avmax; exact Hargs | exact Hfr].
  - apply P3; [exact Hge | exact Hx].
Qed.

Lemma cmp_call_post_frame : forall base nv pr ds e e1 G G'',
  (forall d, In d ds -> d < nv) -> cmp_lmax (map cmp_avmax (pr_rets pr)) <= cmp_procsz pr ->
  cmp_frame base nv e G -> (forall r, r < base + nv -> G'' r = G r) ->
  cmp_frame (base + nv) (cmp_procsz pr) e1 G'' ->
  cmp_frame base nv (cmp_assigns e ds (map (cmp_aeval e1) (pr_rets pr)))
            (cmp_runa G'' (cmp_post base nv pr ds)) /\
  (forall r, r < base -> cmp_runa G'' (cmp_post base nv pr ds) r = G'' r).
Proof.
  intros base nv pr ds e e1 G G'' Hds Hrets Hfr HGG HF2.
  set (W := fun y => G'' (base + nv + y)).
  destruct (cmp_post_spec ds (pr_rets pr) base (base + nv) G'' W (fun y => eq_refl)
              (fun d Hd => ltac:(pose proof (Hds d Hd); lia))) as (Q1 & Q2 & Q3).
  unfold cmp_post. split.
  - intros y Hy. rewrite Q3.
    assert (Hm : map (cmp_aeval W) (pr_rets pr) = map (cmp_aeval e1) (pr_rets pr)).
    { apply map_ext_in. intros r Hr. apply cmp_aeval_below. intros q Hq.
      unfold W. apply HF2.
      assert (Hr' : cmp_avmax r <= cmp_lmax (map cmp_avmax (pr_rets pr)))
        by (apply cmp_lmax_ge; apply in_map; exact Hr).
      lia. }
    rewrite Hm. apply cmp_assigns_agree with (nv := nv); [| exact Hy].
    intros z Hz. unfold cmp_view. rewrite (HGG (base + z)) by lia. apply Hfr. exact Hz.
  - intros r Hr. apply Q2. intros d Hd. pose proof (Hds d Hd). lia.
Qed.

(* ================================================================= *)
(* Forward: a derivation of the original gives one of the compiled.   *)
(* ================================================================= *)

Theorem cmp_inl_fwd : forall ps e s e1 c, cmp_ceval ps e s e1 c ->
  forall n base nv G, cmp_wfp ps -> cmp_wfs n s -> cmp_svmax s <= nv -> cmp_frame base nv e G ->
  exists G1 c', cmp_ceval [] G (cmp_inl ps n base nv s) G1 c' /\ cmp_frame base nv e1 G1 /\
                (forall r, r < base -> G1 r = G r).
Proof.
  intros ps e s e1 c H. induction H; intros n base nv G Hwp Hws Hsv Hfr.
  - exists G, 0. rewrite cmp_inl_skip. split; [constructor | split; [exact Hfr | intros; reflexivity]].
  - cbn [cmp_svmax] in Hsv. rewrite cmp_inl_assign.
    exists (cmp_upd G (base + x) (cmp_aeval G (cmp_ashift base a))), 1.
    split; [constructor |]. split.
    + intros y Hy. rewrite cmp_ashift_eval. unfold cmp_upd.
      destruct (Nat.eqb_spec y x) as [-> | Hne].
      * destruct (Nat.eqb_spec (base + x) (base + x)); [| lia].
        change (cmp_aeval (cmp_view base G) a = cmp_aeval e a).
        apply (cmp_frame_aeval a base nv e G); [lia | exact Hfr].
      * destruct (Nat.eqb_spec (base + y) (base + x)); [lia |]. apply Hfr. exact Hy.
    + intros r Hr. unfold cmp_upd. destruct (Nat.eqb_spec r (base + x)); [lia | reflexivity].
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct Hws as [Hw1 Hw2]. rewrite cmp_inl_seq.
    destruct (IHcmp_ceval1 n base nv G Hwp Hw1 ltac:(lia) Hfr) as (G1 & c1' & D1 & F1 & U1).
    destruct (IHcmp_ceval2 n base nv G1 Hwp Hw2 ltac:(lia) F1) as (G2 & c2' & D2 & F2 & U2).
    exists G2, (c1' + c2'). split; [econstructor; eauto |]. split; [exact F2 |].
    intros r Hr. rewrite U2, U1; auto.
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct Hws as [Hw1 Hw2]. rewrite cmp_inl_if.
    destruct (IHcmp_ceval n base nv G Hwp Hw1 ltac:(lia) Hfr) as (G1 & c1' & D1 & F1 & U1).
    exists G1, (S c1'). split; [| split; assumption].
    apply CEIfT; [| exact D1].
    rewrite cmp_bshift_eval. change (cmp_beval (cmp_view base G) b = true). rewrite (cmp_frame_beval b base nv e G) by (try lia; exact Hfr). exact H.
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct Hws as [Hw1 Hw2]. rewrite cmp_inl_if.
    destruct (IHcmp_ceval n base nv G Hwp Hw2 ltac:(lia) Hfr) as (G1 & c1' & D1 & F1 & U1).
    exists G1, (S c1'). split; [| split; assumption].
    apply CEIfF; [| exact D1].
    rewrite cmp_bshift_eval. change (cmp_beval (cmp_view base G) b = false). rewrite (cmp_frame_beval b base nv e G) by (try lia; exact Hfr). exact H.
  - cbn [cmp_svmax] in Hsv. rewrite cmp_inl_while. exists G, 1. split; [| split; [exact Hfr | intros; reflexivity]].
    apply CEWhileF. rewrite cmp_bshift_eval. change (cmp_beval (cmp_view base G) b = false). rewrite (cmp_frame_beval b base nv e G) by (try lia; exact Hfr). exact H.
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. rewrite cmp_inl_while.
    destruct (IHcmp_ceval1 n base nv G Hwp Hws ltac:(lia) Hfr) as (G1 & c1' & D1 & F1 & U1).
    destruct (IHcmp_ceval2 n base nv G1 Hwp ltac:(cbn [cmp_wfs]; exact Hws) ltac:(cbn [cmp_svmax]; lia) F1) as (G2 & c2' & D2 & F2 & U2).
    rewrite cmp_inl_while in D2.
    exists G2, (S (c1' + c2')). split.
    + apply CEWhileT with (e1 := G1); [| exact D1 | exact D2].
      rewrite cmp_bshift_eval. change (cmp_beval (cmp_view base G) b = true). rewrite (cmp_frame_beval b base nv e G) by (try lia; exact Hfr). exact H.
    + split; [exact F2 |]. intros r Hr. rewrite U2, U1; auto.
  - (* a call *)
    cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct n as [| n]; [lia |].
    rewrite (cmp_inl_call ps n base nv ds p args pr H).
    assert (Hds : forall d, In d ds -> d < nv).
    { intros d Hd. pose proof (cmp_lmax_ge (map S ds) (S d) (in_map S ds d Hd)). lia. }
    assert (Hargs : cmp_lmax (map cmp_avmax args) <= nv) by lia.
    destruct (cmp_call_pre_frame base nv pr args e G Hargs Hfr) as (Hfr' & P1).
    set (G' := cmp_runa G (cmp_pre base nv pr args)) in *.
    assert (Hwb : cmp_wfs n (pr_body pr)).
    { apply cmp_wfs_mono with (m := p); [exact (Hwp p pr H) | lia]. }
    assert (Hsb : cmp_svmax (pr_body pr) <= cmp_procsz pr) by (unfold cmp_procsz; lia).
    destruct (IHcmp_ceval n (base + nv) (cmp_procsz pr) G' Hwp Hwb Hsb Hfr') as (G'' & c'' & D2 & F2 & U2).
    assert (Hrets : cmp_lmax (map cmp_avmax (pr_rets pr)) <= cmp_procsz pr) by (unfold cmp_procsz; lia).
    destruct (cmp_call_post_frame base nv pr ds e e1 G G'' Hds Hrets Hfr
                (fun r Hr => ltac:(rewrite (U2 r Hr); apply P1; exact Hr)) F2) as (Q1 & Q2).
    exists (cmp_runa G'' (cmp_post base nv pr ds)),
           (length (cmp_pre base nv pr args) + (c'' + length (cmp_post base nv pr ds))).
    split; [| split; [exact Q1 |]].
    + econstructor; [apply cmp_seqs_eval | econstructor; [exact D2 | apply cmp_seqs_eval]].
    + intros r Hr. rewrite Q2 by exact Hr. rewrite (U2 r) by lia. apply P1. lia.
Qed.

(* ================================================================= *)
(* Backward: a derivation of the compiled program gives one of the    *)
(* original.                                                          *)
(* ================================================================= *)

Definition cmp_bwd_stmt (ps : list cmp_proc) (n : nat) (s : cmp_stmt) : Prop :=
  forall base nv G G1 c' e,
    cmp_wfp ps -> n <= length ps -> cmp_wfs n s -> cmp_svmax s <= nv ->
    cmp_ceval [] G (cmp_inl ps n base nv s) G1 c' -> cmp_frame base nv e G ->
    exists e1 c, cmp_ceval ps e s e1 c /\ cmp_frame base nv e1 G1 /\
                 (forall r, r < base -> G1 r = G r).

Lemma cmp_inl_bwd_aux : forall ps n,
  (forall ds p args, cmp_bwd_stmt ps n (SCall ds p args)) ->
  forall s, cmp_bwd_stmt ps n s.
Proof.
  intros ps n Hcall s. induction s as [| x a | s1 IH1 s2 IH2 | b s1 IH1 s2 IH2 | b s IHs | ds p args];
    intros base nv G G1 c' e Hwp Hn Hws Hsv D Hfr.
  - rewrite cmp_inl_skip in D. destruct (cmp_ceval_skip_inv _ _ _ _ D) as [-> ->].
    exists e, 0. split; [constructor | split; [exact Hfr | intros; reflexivity]].
  - cbn [cmp_svmax] in Hsv. rewrite cmp_inl_assign in D.
    destruct (cmp_ceval_assign_inv _ _ _ _ _ _ D) as [-> ->].
    exists (cmp_upd e x (cmp_aeval e a)), 1. split; [constructor |]. split.
    + intros y Hy. rewrite cmp_ashift_eval. unfold cmp_upd.
      destruct (Nat.eqb_spec y x) as [-> | Hne].
      * destruct (Nat.eqb_spec (base + x) (base + x)); [| lia].
        change (cmp_aeval (cmp_view base G) a = cmp_aeval e a).
        apply (cmp_frame_aeval a base nv e G); [lia | exact Hfr].
      * destruct (Nat.eqb_spec (base + y) (base + x)); [lia |]. apply Hfr. exact Hy.
    + intros r Hr. unfold cmp_upd. destruct (Nat.eqb_spec r (base + x)); [lia | reflexivity].
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct Hws as [Hw1 Hw2]. rewrite cmp_inl_seq in D.
    destruct (cmp_ceval_seq_inv _ _ _ _ _ _ D) as (Gm & d1 & d2 & D1 & D2 & ->).
    destruct (IH1 base nv G Gm d1 e Hwp Hn Hw1 ltac:(lia) D1 Hfr) as (e1 & c1 & E1 & F1 & U1).
    destruct (IH2 base nv Gm G1 d2 e1 Hwp Hn Hw2 ltac:(lia) D2 F1) as (e2 & c2 & E2 & F2 & U2).
    exists e2, (c1 + c2). split; [econstructor; eauto |]. split; [exact F2 |].
    intros r Hr. rewrite U2, U1; auto.
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. destruct Hws as [Hw1 Hw2]. rewrite cmp_inl_if in D.
    assert (Hb0 : cmp_beval G (cmp_bshift base b) = cmp_beval e b).
    { rewrite cmp_bshift_eval. change (cmp_beval (cmp_view base G) b = cmp_beval e b).
      apply (cmp_frame_beval b base nv e G); [lia | exact Hfr]. }
    destruct (cmp_ceval_if_inv _ _ _ _ _ _ _ D) as [[Hb (d & D1 & ->)] | [Hb (d & D1 & ->)]];
      rewrite Hb0 in Hb.
    + destruct (IH1 base nv G G1 d e Hwp Hn Hw1 ltac:(lia) D1 Hfr) as (e1 & c1 & E1 & F1 & U1).
      exists e1, (S c1). split; [apply CEIfT; assumption | split; assumption].
    + destruct (IH2 base nv G G1 d e Hwp Hn Hw2 ltac:(lia) D1 Hfr) as (e1 & c1 & E1 & F1 & U1).
      exists e1, (S c1). split; [apply CEIfF; assumption | split; assumption].
  - cbn [cmp_wfs cmp_svmax] in Hws, Hsv. rewrite cmp_inl_while in D.
    assert (Hbe : forall G0 e0, cmp_frame base nv e0 G0 ->
                  cmp_beval G0 (cmp_bshift base b) = cmp_beval e0 b).
    { intros G0 e0 Hf. rewrite cmp_bshift_eval.
      change (cmp_beval (cmp_view base G0) b = cmp_beval e0 b).
      apply (cmp_frame_beval b base nv e0 G0); [lia | exact Hf]. }
    revert G G1 e D Hfr. induction c' as [c' IHc] using lt_wf_ind. intros G G1 e D Hfr.
    destruct (cmp_ceval_while_inv _ _ _ _ _ _ D) as [(Hb & -> & ->) | (Hb & Gm & d1 & d2 & D1 & D2 & ->)].
    + rewrite (Hbe G e Hfr) in Hb. exists e, 1.
      split; [apply CEWhileF; exact Hb | split; [exact Hfr | intros; reflexivity]].
    + rewrite (Hbe G e Hfr) in Hb.
      destruct (IHs base nv G Gm d1 e Hwp Hn Hws ltac:(lia) D1 Hfr) as (e1 & c1 & E1 & F1 & U1).
      destruct (IHc d2 ltac:(lia) Gm G1 e1 D2 F1) as (e2 & c2 & E2 & F2 & U2).
      exists e2, (S (c1 + c2)). split; [apply CEWhileT with (e1 := e1); assumption |].
      split; [exact F2 |]. intros r Hr. rewrite U2, U1; auto.
  - exact (Hcall ds p args base nv G G1 c' e Hwp Hn Hws Hsv D Hfr).
Qed.

Lemma cmp_inl_bwd_all : forall n ps s, cmp_bwd_stmt ps n s.
Proof.
  induction n as [| n IHn]; intros ps s.
  - apply cmp_inl_bwd_aux. intros ds p args base nv G G1 c' e Hwp Hn Hws. cbn in Hws. lia.
  - apply cmp_inl_bwd_aux. intros ds p args base nv G G1 c' e Hwp Hn Hws Hsv D Hfr.
    cbn [cmp_wfs cmp_svmax] in Hws, Hsv.
    destruct (nth_error ps p) as [pr |] eqn:Hp.
    2: { apply nth_error_None in Hp. lia. }
    rewrite (cmp_inl_call ps n base nv ds p args pr Hp) in D.
    destruct (cmp_ceval_seq_inv _ _ _ _ _ _ D) as (G' & d1 & d23 & D1 & D23 & ->).
    destruct (cmp_ceval_seq_inv _ _ _ _ _ _ D23) as (G'' & d2 & d3 & D2 & D3 & ->).
    destruct (cmp_seqs_inv _ _ _ _ _ D1) as [-> _].
    destruct (cmp_seqs_inv _ _ _ _ _ D3) as [-> _].
    assert (Hds : forall d, In d ds -> d < nv).
    { intros d Hd. pose proof (cmp_lmax_ge (map S ds) (S d) (in_map S ds d Hd)). lia. }
    assert (Hargs : cmp_lmax (map cmp_avmax args) <= nv) by lia.
    destruct (cmp_call_pre_frame base nv pr args e G Hargs Hfr) as (Hfr' & P1).
    assert (Hwb : cmp_wfs n (pr_body pr)).
    { apply cmp_wfs_mono with (m := p); [exact (Hwp p pr Hp) | lia]. }
    assert (Hsb : cmp_svmax (pr_body pr) <= cmp_procsz pr) by (unfold cmp_procsz; lia).
    destruct (IHn ps (pr_body pr) (base + nv) (cmp_procsz pr) _ _ d2 _ Hwp ltac:(lia) Hwb Hsb D2 Hfr')
      as (e1 & c & E1 & F2 & U2).
    assert (Hrets : cmp_lmax (map cmp_avmax (pr_rets pr)) <= cmp_procsz pr) by (unfold cmp_procsz; lia).
    destruct (cmp_call_post_frame base nv pr ds e e1 G _ Hds Hrets Hfr
                (fun r Hr => ltac:(rewrite (U2 r Hr); apply P1; exact Hr)) F2) as (Q1 & Q2).
    exists (cmp_assigns e ds (map (cmp_aeval e1) (pr_rets pr))), (S c).
    split; [eapply CECall; eauto | split; [exact Q1 |]].
    intros r Hr. rewrite Q2 by exact Hr. rewrite (U2 r) by lia. apply P1. lia.
Qed.

Theorem cmp_inl_bwd : forall ps n s base nv G G1 c' e,
  cmp_wfp ps -> n <= length ps -> cmp_wfs n s -> cmp_svmax s <= nv ->
  cmp_ceval [] G (cmp_inl ps n base nv s) G1 c' -> cmp_frame base nv e G ->
  exists e1 c, cmp_ceval ps e s e1 c /\ cmp_frame base nv e1 G1 /\
               (forall r, r < base -> G1 r = G r).
Proof. intros. eapply cmp_inl_bwd_all; eauto. Qed.

Print Assumptions cmp_inl_fwd.
Print Assumptions cmp_inl_bwd.
Print Assumptions cmp_inl_nocall.

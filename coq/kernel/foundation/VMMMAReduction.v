(** Repeated output-preserving reduction of alternate Minsky machines to
    three counters. *)

From Coq Require Import Arith Lia List Peano_dec.
From Undecidability.Shared.Libs.DLW.Utils Require Import godel_coding.
From Undecidability.Shared.Libs.DLW.Vec Require Import pos vec.
From Undecidability.Shared.Libs.DLW.Code Require Import subcode sss
  compiler_correction.
From Undecidability.MinskyMachines Require Import MM MMA.
From Undecidability.MinskyMachines.MMA Require Import mma_defs
  mma3_mma2_compiler.
From Kernel Require Import VMSelfGuest VMSelfRun MMAOutputEpilogue
  VMMMA3GuestCompiler.

Fixpoint mma_pos_last (n : nat) : Fin.t (S n) :=
  match n with
  | 0 => Fin.F1
  | S n' => Fin.FS (mma_pos_last n')
  end.

Fixpoint mma_dim_eq (n : nat) : S (S n) + 1 = 3 + n.
Proof.
  destruct n as [|n].
  - reflexivity.
  - cbn. f_equal. exact (mma_dim_eq n).
Defined.

Definition mma_cast_program {a b} (e : a = b)
    (p : list (mm_instr (Fin.t a))) : list (mm_instr (Fin.t b)) :=
  match e with eq_refl => p end.

Lemma mma_cast_program_length : forall a b (e : a = b) p,
  length (mma_cast_program e p) = length p.
Proof. intros a b [] p. reflexivity. Qed.

Definition mma_cast_vec {a b} (e : a = b) (v : vec nat a) : vec nat b :=
  match e with eq_refl => v end.

Definition mma_cast_pos {a b} (e : a = b) (x : Fin.t a) : Fin.t b :=
  Fin.cast x e.

Lemma mma_fin_cast_refl : forall n (x : Fin.t n), Fin.cast x eq_refl = x.
Proof.
  intros n x. induction x as [n|n x IH].
  - reflexivity.
  - cbn [Fin.cast]. f_equal.
    rewrite (UIP_nat _ _ (f_equal Nat.pred eq_refl) eq_refl). exact IH.
Qed.

Lemma mma_cast_vec_pos : forall a b (e : a = b) v x,
  vec_pos (mma_cast_vec e v) (mma_cast_pos e x) = vec_pos v x.
Proof.
  intros a b e v x. destruct e. unfold mma_cast_vec, mma_cast_pos.
  rewrite mma_fin_cast_refl. reflexivity.
Qed.

Lemma mma_cast_pos_index : forall a b (e : a = b) (x : Fin.t a),
  pos2nat (mma_cast_pos e x) = pos2nat x.
Proof.
  intros a b e x. destruct e. unfold mma_cast_pos.
  rewrite mma_fin_cast_refl. reflexivity.
Qed.

Lemma mma_cast_output : forall a b (e : a = b) p start pc final,
  sss_output (@mma_sss a) (1, p) (1, start) (pc, final) ->
  sss_output (@mma_sss b) (1, mma_cast_program e p)
    (1, mma_cast_vec e start) (pc, mma_cast_vec e final).
Proof. intros a b [] p start pc final H. exact H. Qed.

Definition mma_pack_vec (n : nat) (v : vec nat (3 + n)) : vec nat (2 + n) :=
  let parts := vec_split 3 n v in
  vec_app (0 ## gc_enc godel_coding_235 (fst parts) ## vec_nil) (snd parts).

Lemma mma_pack_vec_sim : forall n (v : vec nat (3 + n)),
  let w := mma_pack_vec n v in
  vec_pos w pos0 = 0 /\
  vec_pos w pos1 = gc_enc godel_coding_235 (fst (vec_split 3 n v)) /\
  forall x, vec_pos v (pos_right 3 x) = vec_pos w (pos_right 2 x).
Proof.
  intros n v. unfold mma_pack_vec.
  destruct (vec_split 3 n v) as [front tail] eqn:Hsplit. cbn.
  split.
  - change (vec_pos (vec_app (0 ## gc_enc godel_coding_235 front ## vec_nil) tail)
      (pos_left n pos0) = 0). rewrite vec_pos_app_left. reflexivity.
  - split.
    + change (vec_pos (vec_app (0 ## gc_enc godel_coding_235 front ## vec_nil) tail)
        (pos_left n pos1) = gc_enc godel_coding_235 front).
      rewrite vec_pos_app_left. reflexivity.
    + intro x.
      pose proof (vec_app_split 3 n v) as Happ. rewrite Hsplit in Happ. cbn in Happ.
      rewrite <- Happ. reflexivity.
Qed.

Definition mma_reduce_once (n : nat) (p : list (mm_instr (Fin.t (3 + n))))
    : list (mm_instr (Fin.t (2 + n))) :=
  gc_code (mma3_mma2_compiler n) (1, p) 1.

Theorem mma_reduce_once_output : forall m p start pc final,
  sss_output (@mma_sss (3 + S m)) (1, p) (1, start) (pc, final) ->
  exists target,
    sss_output (@mma_sss (2 + S m)) (1, mma_reduce_once (S m) p)
      (1, mma_pack_vec (S m) start)
      (1 + length (mma_reduce_once (S m) p), target) /\
    vec_pos final (pos_right 3 (mma_pos_last m)) =
      vec_pos target (pos_right 2 (mma_pos_last m)).
Proof.
  intros m p start pc final Hout.
  destruct (@compiler_t_output_sound' _ _ _ _
    (@mma_sss (3 + S m)) (@mma_sss (2 + S m)) _
    (mma3_mma2_compiler (S m)) (1, p) 1 start
    (mma_pack_vec (S m) start) pc final
    (mma_pack_vec_sim (S m) start) Hout) as (target & Htarget & Hsim).
  exists target. split; [exact Htarget|].
  exact (proj2 (proj2 Hsim) (mma_pos_last m)).
Qed.

Fixpoint mma_reduce_all (n : nat)
    : list (mm_instr (Fin.t (3 + n))) -> list (mm_instr (Fin.t 3)) :=
  match n as k return
      list (mm_instr (Fin.t (3 + k))) -> list (mm_instr (Fin.t 3)) with
  | 0 => fun p => p
  | S m => fun p => mma_reduce_all m (mma_reduce_once (S m) p)
  end.

Fixpoint mma_pack_all (n : nat) : vec nat (3 + n) -> vec nat 3 :=
  match n as k return vec nat (3 + k) -> vec nat 3 with
  | 0 => fun v => v
  | S m => fun v => mma_pack_all m (mma_pack_vec (S m) v)
  end.

Definition mma_all_last (n : nat) : Fin.t (3 + n) :=
  match n with
  | 0 => pos2
  | S m => pos_right 3 (mma_pos_last m)
  end.

Lemma mma_pos_last_index : forall n, pos2nat (mma_pos_last n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  cbn [mma_pos_last]. rewrite pos2nat_nxt, IH. reflexivity.
Qed.

Lemma mma_epilogue_last_index : forall n,
  pos2nat (mma_last_pos (S (S n))) = 2 + n.
Proof.
  intro n. unfold mma_last_pos. rewrite pos2nat_right, pos2nat_fst.
  rewrite Nat.add_0_r. reflexivity.
Qed.

Lemma mma_all_last_index : forall n, pos2nat (mma_all_last n) = 2 + n.
Proof.
  intros [|n]; [reflexivity|].
  cbn [mma_all_last]. rewrite pos2nat_right, mma_pos_last_index. lia.
Qed.

Lemma mma_cast_epilogue_last : forall n,
  mma_cast_pos (mma_dim_eq n) (mma_last_pos (S (S n))) = mma_all_last n.
Proof.
  intro n. apply pos2nat_inj.
  rewrite mma_cast_pos_index, mma_epilogue_last_index,
    mma_all_last_index. reflexivity.
Qed.

Lemma mma_once_last_is_next : forall m,
  @pos_right 2 (S m) (mma_pos_last m) = mma_all_last m.
Proof. intros [|m]; reflexivity. Qed.

Theorem mma_reduce_all_output : forall n p start pc final,
  sss_output (@mma_sss (3 + n)) (1, p) (1, start) (pc, final) ->
  exists pc3 target,
    sss_output (@mma_sss 3) (1, mma_reduce_all n p)
      (1, mma_pack_all n start) (pc3, target) /\
    vec_pos final (mma_all_last n) = vec_pos target pos2.
Proof.
  induction n as [|n IH]; intros p start pc final Hout.
  - exists pc, final. split; [exact Hout|reflexivity].
  - destruct (mma_reduce_once_output n p start pc final Hout)
      as (mid & Hmid & Hlast).
    destruct (IH (mma_reduce_once (S n) p) (mma_pack_vec (S n) start)
      (1 + length (mma_reduce_once (S n) p)) mid Hmid)
      as (pc3 & target & Htarget & Htargetlast).
    exists pc3, target. split; [exact Htarget|].
    cbn [mma_reduce_all mma_pack_all].
    unfold mma_all_last at 1. fold (mma_all_last n).
    rewrite Hlast, mma_once_last_is_next. exact Htargetlast.
Qed.

Theorem mma_reduce_all_output_canonical : forall n p start final,
  sss_output (@mma_sss (3 + n)) (1, p) (1, start)
    (1 + length p, final) ->
  exists target,
    sss_output (@mma_sss 3) (1, mma_reduce_all n p)
      (1, mma_pack_all n start)
      (1 + length (mma_reduce_all n p), target) /\
    vec_pos final (mma_all_last n) = vec_pos target pos2.
Proof.
  induction n as [|n IH]; intros p start final Hout.
  - exists final. split; [exact Hout|reflexivity].
  - destruct (mma_reduce_once_output n p start (1 + length p) final Hout)
      as (mid & Hmid & Hlast).
    destruct (IH (mma_reduce_once (S n) p) (mma_pack_vec (S n) start)
      mid Hmid) as (target & Htarget & Htargetlast).
    exists target. split; [exact Htarget|].
    cbn [mma_reduce_all mma_pack_all].
    unfold mma_all_last at 1. fold (mma_all_last n).
    rewrite Hlast, mma_once_last_is_next. exact Htargetlast.
Qed.

Theorem mma_output_to_three : forall n p start pc final,
  sss_output (@mma_sss (S (S n))) (1, p) (1, start) (pc, final) ->
  exists target,
    sss_output (@mma_sss 3)
      (1, mma_reduce_all n
        (mma_cast_program (mma_dim_eq n) (@mma_with_output (S n) pos1 p)))
      (1, mma_pack_all n
        (mma_cast_vec (mma_dim_eq n) (mma_extend_vec start 0)))
      (1 + length (mma_reduce_all n
        (mma_cast_program (mma_dim_eq n) (@mma_with_output (S n) pos1 p))),
       target) /\
    vec_pos target pos2 = vec_pos final pos0.
Proof.
  intros n p start pc final Hout.
  destruct (mma_with_output_correct n p start pc final Hout)
    as (extended_final & Hextended & Hlast).
  pose proof (mma_cast_output (S (S n) + 1) (3 + n) (mma_dim_eq n)
    (@mma_with_output (S n) pos1 p) (mma_extend_vec start 0)
    (1 + length (@mma_with_output (S n) pos1 p)) extended_final Hextended)
    as Hcast.
  replace (1 + length (@mma_with_output (S n) pos1 p)) with
    (1 + length (mma_cast_program (mma_dim_eq n)
      (@mma_with_output (S n) pos1 p))) in Hcast by
    (rewrite mma_cast_program_length; reflexivity).
  destruct (mma_reduce_all_output_canonical n
    (mma_cast_program (mma_dim_eq n) (@mma_with_output (S n) pos1 p))
    (mma_cast_vec (mma_dim_eq n) (mma_extend_vec start 0))
    (mma_cast_vec (mma_dim_eq n) extended_final) Hcast)
    as (target & Htarget & Htargetlast).
  exists target. split; [exact Htarget|].
  rewrite <- Htargetlast, <- mma_cast_epilogue_last.
  rewrite mma_cast_vec_pos. exact Hlast.
Qed.

Definition mma3_guest_start (v : vec nat 3) : GConf :=
  {| gc_pc := 0; gc_mu := 0;
     gc_g := {| gr0 := vec_pos v pos0;
                gr1 := vec_pos v pos1;
                gr2 := vec_pos v pos2;
                gr3 := 0 |} |}.

Lemma mma3_guest_start_rel : forall (p : list (mm_instr (Fin.t 3))) v,
  mma3_rel (length p) (1, v) (mma3_guest_start v).
Proof.
  intros p v. unfold mma3_rel, mma3_guest_start, mma3_addr.
  cbn [gc_pc gc_g gr0 gr1 gr2 Nat.eqb]. repeat split; reflexivity.
Qed.

Theorem mma_three_to_guest : forall p start pc final,
  sss_output (@mma_sss 3) (1, p) (1, start) (pc, final) ->
  exists fuel,
    g_terminal (mma3_compile p)
      (g_run fuel (mma3_compile p) (mma3_guest_start start)) /\
    gr2 (gc_g (g_run fuel (mma3_compile p) (mma3_guest_start start))) =
      vec_pos final pos2.
Proof.
  intros p start pc final Hout.
  destruct (mma3_compile_output p (1, start) (pc, final)
    (mma3_guest_start start) Hout (mma3_guest_start_rel p start))
    as (fuel & Hterminal & Hrel).
  exists fuel. split; [exact Hterminal|].
  exact (proj2 (proj2 (proj2 Hrel))).
Qed.

Definition mma3_swap_pos : Fin.t 3 -> Fin.t 3.
Proof.
  intro x. refine (Fin.caseS' x (fun _ => Fin.t 3) pos2 _).
  intro x1. refine (Fin.caseS' x1 (fun _ => Fin.t 3) pos1 _).
  intro x2. refine (Fin.caseS' x2 (fun _ => Fin.t 3) pos0 _).
  intro x0. exact (Fin.case0 (fun _ => Fin.t 3) x0).
Defined.

Definition mma3_swap_vec (v : vec nat 3) : vec nat 3 :=
  vec_set_pos (fun x => vec_pos v (mma3_swap_pos x)).

Definition mma3_swap_instr (i : mm_instr (Fin.t 3)) : mm_instr (Fin.t 3) :=
  match i with
  | mm_inc x => mm_inc (mma3_swap_pos x)
  | mm_dec x target => mm_dec (mma3_swap_pos x) target
  end.

Definition mma3_swap_program (p : list (mm_instr (Fin.t 3))) :=
  map mma3_swap_instr p.

Lemma mma3_swap_pos_values :
  mma3_swap_pos pos0 = pos2 /\ mma3_swap_pos pos1 = pos1 /\
  mma3_swap_pos pos2 = pos0.
Proof. repeat split; reflexivity. Qed.

Lemma mma3_swap_pos_involutive : forall x,
  mma3_swap_pos (mma3_swap_pos x) = x.
Proof.
  intro x. destruct (fin3_cases x) as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma mma3_swap_vec_lookup : forall v x,
  vec_pos (mma3_swap_vec v) x = vec_pos v (mma3_swap_pos x).
Proof.
  intros v x. unfold mma3_swap_vec.
  exact (vec_pos_set (fun y => vec_pos v (mma3_swap_pos y)) x).
Qed.

Lemma mma3_swap_vec_involutive : forall v,
  mma3_swap_vec (mma3_swap_vec v) = v.
Proof.
  intro v. apply vec_pos_ext. intro x. rewrite !mma3_swap_vec_lookup,
    mma3_swap_pos_involutive. reflexivity.
Qed.

Lemma mma3_swap_vec_change : forall v x value,
  mma3_swap_vec (vec_change v x value) =
  vec_change (mma3_swap_vec v) (mma3_swap_pos x) value.
Proof.
  intros v x value. apply vec_pos_ext. intro y.
  rewrite mma3_swap_vec_lookup.
  destruct (pos_eq_dec y (mma3_swap_pos x)) as [->|Hneq].
  - rewrite mma3_swap_pos_involutive.
    rewrite !vec_change_eq by reflexivity. reflexivity.
  - rewrite vec_change_neq.
    + rewrite vec_change_neq by (intro Heq; apply Hneq; symmetry; exact Heq).
      rewrite mma3_swap_vec_lookup. reflexivity.
    + intro Heq. apply Hneq.
      pose proof (f_equal mma3_swap_pos Heq) as Hswap.
      rewrite mma3_swap_pos_involutive in Hswap. symmetry. exact Hswap.
Qed.

Lemma mma3_swap_instr_step : forall i state final,
  @mma_sss 3 i state final ->
  @mma_sss 3 (mma3_swap_instr i)
    (fst state, mma3_swap_vec (snd state))
    (fst final, mma3_swap_vec (snd final)).
Proof.
  intros i state final Hstep. inversion Hstep; subst;
    cbn [mma3_swap_instr fst snd].
  - rewrite mma3_swap_vec_change.
    replace (vec_pos v x) with
      (vec_pos (mma3_swap_vec v) (mma3_swap_pos x)).
    + apply in_mma_sss_inc.
    + rewrite mma3_swap_vec_lookup, mma3_swap_pos_involutive. reflexivity.
  - apply in_mma_sss_dec_0.
    rewrite mma3_swap_vec_lookup, mma3_swap_pos_involutive. assumption.
  - rewrite mma3_swap_vec_change.
    apply in_mma_sss_dec_1 with (u := u).
    rewrite mma3_swap_vec_lookup, mma3_swap_pos_involutive. assumption.
Qed.

Definition mma3_swap_state (s : nat * vec nat 3) : nat * vec nat 3 :=
  (fst s, mma3_swap_vec (snd s)).

Lemma mma3_swap_program_step : forall p state final,
  sss_step (@mma_sss 3) (1, p) state final ->
  sss_step (@mma_sss 3) (1, mma3_swap_program p)
    (mma3_swap_state state) (mma3_swap_state final).
Proof.
  intros p state final (k & l & i & r & d & Hp & Hstate & Hstep).
  inversion Hp; subst k. subst state.
  exists 1, (map mma3_swap_instr l), (mma3_swap_instr i),
    (map mma3_swap_instr r), (mma3_swap_vec d).
  repeat split.
  - unfold mma3_swap_program. rewrite map_app. reflexivity.
  - cbn [mma3_swap_state fst snd]. rewrite map_length. reflexivity.
  - apply mma3_swap_instr_step. exact Hstep.
Qed.

Lemma mma3_swap_program_steps : forall p n state final,
  sss_steps (@mma_sss 3) (1, p) n state final ->
  sss_steps (@mma_sss 3) (1, mma3_swap_program p) n
    (mma3_swap_state state) (mma3_swap_state final).
Proof.
  intros p n state final Hsteps. induction Hsteps.
  - apply in_sss_steps_0.
  - apply in_sss_steps_S with (mma3_swap_state st2).
    + apply mma3_swap_program_step. exact H.
    + exact IHHsteps.
Qed.

Theorem mma3_swap_output : forall p start pc final,
  sss_output (@mma_sss 3) (1, p) (1, start) (pc, final) ->
  sss_output (@mma_sss 3) (1, mma3_swap_program p)
    (1, mma3_swap_vec start) (pc, mma3_swap_vec final).
Proof.
  intros p start pc final ((n & Hsteps) & Hout). split.
  - exists n. apply mma3_swap_program_steps in Hsteps. exact Hsteps.
  - unfold out_code, code_start, code_end in *. cbn in *.
    unfold mma3_swap_program. rewrite map_length. exact Hout.
Qed.

Theorem mma_three_to_guest_r0 : forall p start pc final,
  sss_output (@mma_sss 3) (1, p) (1, start) (pc, final) ->
  exists fuel,
    g_terminal (mma3_compile p)
      (g_run fuel (mma3_compile p) (mma3_guest_start start)) /\
    gr0 (gc_g (g_run fuel (mma3_compile p) (mma3_guest_start start))) =
      vec_pos final pos0.
Proof.
  intros p start pc final Hout.
  destruct (mma3_compile_output p (1, start) (pc, final)
    (mma3_guest_start start) Hout (mma3_guest_start_rel p start))
    as (fuel & Hterminal & Hrel).
  exists fuel. split; [exact Hterminal|].
  exact (proj1 (proj2 Hrel)).
Qed.

Theorem mma_output_to_guest_r0 : forall n p start pc final,
  sss_output (@mma_sss (S (S n))) (1, p) (1, start) (pc, final) ->
  exists fuel,
    let p3 := mma_reduce_all n
      (mma_cast_program (mma_dim_eq n) (@mma_with_output (S n) pos1 p)) in
    let start3 := mma_pack_all n
      (mma_cast_vec (mma_dim_eq n) (mma_extend_vec start 0)) in
    g_terminal (mma3_compile (mma3_swap_program p3))
      (g_run fuel (mma3_compile (mma3_swap_program p3))
        (mma3_guest_start (mma3_swap_vec start3))) /\
    gr0 (gc_g (g_run fuel (mma3_compile (mma3_swap_program p3))
      (mma3_guest_start (mma3_swap_vec start3)))) = vec_pos final pos0.
Proof.
  intros n p start pc final Hout.
  destruct (mma_output_to_three n p start pc final Hout)
    as (target & Hthree & Hvalue).
  pose proof (mma3_swap_output _ _ _ _ Hthree) as Hswapped.
  destruct (mma_three_to_guest_r0 _ _ _ _ Hswapped)
    as (fuel & Hterminal & Hresult).
  exists fuel. cbn zeta. split; [exact Hterminal|].
  rewrite mma3_swap_vec_lookup in Hresult.
  rewrite (proj1 mma3_swap_pos_values) in Hresult.
  rewrite Hresult. exact Hvalue.
Qed.

Print Assumptions mma_reduce_once_output.
Print Assumptions mma_reduce_all_output.
Print Assumptions mma_reduce_all_output_canonical.
Print Assumptions mma_output_to_three.
Print Assumptions mma_three_to_guest.
Print Assumptions mma3_swap_output.
Print Assumptions mma_output_to_guest_r0.

(** NecFSqueeze: the squeeze bound m + k <= 2^cost * m is tight everywhere,
    and each of its premises is needed.

    For every m and every c there is a finite machine with a permanent reading,
    a cost meeting the halving price, m states reading yes, and one move of
    cost c that turns (2^c - 1) * m no-states yes, so m + k = 2^c * m
    ([nec_f_squeeze_tight]). For every m, k and c with m + k <= 2^c * m the
    same machine has a move of cost exactly c turning a list of exactly k
    no-states yes ([nec_f_squeeze_tight_every_k]); together with the bound,
    the least cost of such a move is exactly the least c with
    m + k <= 2^c * m. The machine is a grid: m rows, 2^c columns, the reading
    is "column zero", and the move sends every cell to column zero of its row.

    Dropping finiteness, permanence or the halving price each breaks the
    bound ([nec_f_squeeze_needs_finite], [nec_f_squeeze_needs_permanent],
    [nec_f_squeeze_needs_halving]). The repo's rounded-logarithm form is
    strictly weaker than the integer form ([nec_f_rounded_log_form_weaker]). *)

From Coq Require Import List Bool Arith Lia.
From Coq Require Import Logic.FinFun Logic.Eqdep_dec.
Import ListNotations.
From Kernel Require Import PermanentCertification.
From Kernel Require Import PermanentRecordPricing.
From Kernel Require Import FiniteCertMachine.

(** * A finite type with n members *)

Definition NecFFin (n : nat) : Type := {k : nat | Nat.ltb k n = true}.

Lemma nec_f_fin_eq : forall n (a b : NecFFin n), proj1_sig a = proj1_sig b -> a = b.
Proof.
  intros n [x Hx] [y Hy] H. simpl in H. subst y. f_equal.
  apply UIP_dec. exact bool_dec.
Qed.

Definition nec_f_fin_eq_dec (n : nat) : forall a b : NecFFin n, {a = b} + {a <> b}.
Proof.
  intros a b. destruct (Nat.eq_dec (proj1_sig a) (proj1_sig b)) as [H | H].
  - left. apply nec_f_fin_eq. exact H.
  - right. intro E. apply H. rewrite E. reflexivity.
Defined.

Definition nec_f_fin_of (n k : nat) : option (NecFFin n) :=
  match lt_dec k n with
  | left H => Some (exist _ k (proj2 (Nat.ltb_lt k n) H))
  | right _ => None
  end.

Definition nec_f_collect (n : nat) (l : list nat) : list (NecFFin n) :=
  fold_right (fun k acc => match nec_f_fin_of n k with Some x => x :: acc | None => acc end) [] l.

Definition nec_f_enum (n : nat) : list (NecFFin n) := nec_f_collect n (seq 0 n).

Lemma nec_f_collect_values :
  forall n l, (forall k, In k l -> k < n) -> map (@proj1_sig _ _) (nec_f_collect n l) = l.
Proof.
  intros n l. induction l as [| a l IH]; intros H; simpl; [reflexivity |].
  unfold nec_f_fin_of. destruct (lt_dec a n) as [Ha | Ha].
  - simpl. rewrite IH; [reflexivity | intros k Hk; apply H; right; exact Hk].
  - exfalso. apply Ha. apply H. left. reflexivity.
Qed.

Lemma nec_f_enum_values : forall n, map (@proj1_sig _ _) (nec_f_enum n) = seq 0 n.
Proof.
  intro n. apply nec_f_collect_values. intros k Hk. apply in_seq in Hk. lia.
Qed.

Lemma nec_f_enum_length : forall n, length (nec_f_enum n) = n.
Proof.
  intro n. transitivity (length (map (@proj1_sig _ _) (nec_f_enum n))).
  - symmetry. apply map_length.
  - rewrite nec_f_enum_values. apply seq_length.
Qed.

Lemma nec_f_enum_nodup : forall n, NoDup (nec_f_enum n).
Proof.
  intro n. apply (NoDup_map_inv (@proj1_sig _ _)). rewrite nec_f_enum_values. apply seq_NoDup.
Qed.

Lemma nec_f_enum_full : forall n (x : NecFFin n), In x (nec_f_enum n).
Proof.
  intros n x.
  assert (Hx : In (proj1_sig x) (map (@proj1_sig _ _) (nec_f_enum n))).
  { rewrite nec_f_enum_values. apply in_seq. destruct x as [k Hk]. simpl.
    apply Nat.ltb_lt in Hk. lia. }
  apply in_map_iff in Hx as [y [Hy Hin]].
  rewrite (nec_f_fin_eq n x y (eq_sym Hy)). exact Hin.
Qed.

(** * Lists of pairs *)

Lemma nec_f_nodup_prod :
  forall (A B : Type) (l : list A) (l' : list B),
    NoDup l -> NoDup l' -> NoDup (list_prod l l').
Proof.
  intros A B l l' Hl Hl'. induction l as [| a l IH]; simpl; [constructor |].
  inversion Hl as [| ? ? Ha Hl0]; subst.
  apply nodup_app_disjoint.
  - apply Injective_map_NoDup; [intros x y H; inversion H; reflexivity | exact Hl'].
  - apply IH. exact Hl0.
  - intros [x y] Hxy Hin. apply in_map_iff in Hxy as [z [Hz _]]. inversion Hz; subst.
    apply in_prod_iff in Hin as [Hin _]. contradiction.
Qed.

Lemma nec_f_filter_prod_snd :
  forall (A B : Type) (g : B -> bool) (l : list A) (l' : list B),
    length (filter (fun x => g (snd x)) (list_prod l l')) = length l * length (filter g l').
Proof.
  intros A B g l l'. induction l as [| a l IH]; simpl; [reflexivity |].
  rewrite filter_app, app_length, IH. f_equal.
  clear IH. induction l' as [| b l' IH']; simpl; [reflexivity |].
  destruct (g b); simpl; rewrite IH'; reflexivity.
Qed.

Lemma nec_f_nodup_map_on :
  forall (A B : Type) (f : A -> B) (l : list A),
    NoDup l -> (forall a b, In a l -> In b l -> f a = f b -> a = b) -> NoDup (map f l).
Proof.
  intros A B f l Hnd Hinj. induction l as [| x xs IH]; simpl; [constructor |].
  inversion Hnd as [| ? ? Hx Hxs]; subst. constructor.
  - intro Hin. apply in_map_iff in Hin as [y [Hy Hyin]].
    assert (y = x) by (apply Hinj; [right; exact Hyin | left; reflexivity | exact Hy]).
    subst. contradiction.
  - apply IH; [exact Hxs |]. intros a b Ha Hb. apply Hinj; right; assumption.
Qed.

(** * The grid machine *)

Section Grid.

Variables (m c : nat).

Lemma nec_f_pow_pos : 0 < 2 ^ c.
Proof. induction c as [| c' IH]; simpl; lia. Qed.

Definition NecFGrid : Type := (NecFFin m * NecFFin (2 ^ c))%type.

Definition nec_f_col0 : NecFFin (2 ^ c) :=
  exist _ 0 (proj2 (Nat.ltb_lt 0 (2 ^ c)) nec_f_pow_pos).

Definition nec_f_grid_eq_dec : forall a b : NecFGrid, {a = b} + {a <> b}.
Proof.
  intros [a1 a2] [b1 b2].
  destruct (nec_f_fin_eq_dec m a1 b1) as [H1 | H1];
    [destruct (nec_f_fin_eq_dec (2 ^ c) a2 b2) as [H2 | H2] |].
  - left. subst. reflexivity.
  - right. intro E. inversion E. contradiction.
  - right. intro E. inversion E. contradiction.
Defined.

Definition nec_f_grid_cert (x : NecFGrid) : bool := Nat.eqb (proj1_sig (snd x)) 0.

Definition nec_f_grid_step (x : NecFGrid) (_ : unit) : NecFGrid := (fst x, nec_f_col0).

Definition nec_f_grid_cost (_ : unit) : nat := c.

Definition nec_f_grid_all : list NecFGrid := list_prod (nec_f_enum m) (nec_f_enum (2 ^ c)).

Theorem nec_f_grid_finite : finite_states nec_f_grid_all.
Proof.
  split.
  - apply nec_f_nodup_prod; apply nec_f_enum_nodup.
  - intros [a b]. apply in_prod; apply nec_f_enum_full.
Qed.

Theorem nec_f_grid_permanent : permanent nec_f_grid_step nec_f_grid_cert.
Proof. intros x i _. reflexivity. Qed.

Lemma nec_f_grid_fiber :
  forall (D : list NecFGrid) y,
    NoDup D ->
    length (filter (hits NecFGrid NecFGrid nec_f_grid_eq_dec
                       (fun x => nec_f_grid_step x tt) y) D) <= 2 ^ c.
Proof.
  intros D y HD.
  set (L := filter (hits NecFGrid NecFGrid nec_f_grid_eq_dec (fun x => nec_f_grid_step x tt) y) D).
  assert (HL : forall x, In x L -> (fst x, nec_f_col0) = y).
  { intros x Hx. unfold L in Hx. apply filter_In in Hx as [_ Hh]. unfold hits in Hh.
    destruct (nec_f_grid_eq_dec (nec_f_grid_step x tt) y) as [E | _]; [exact E | discriminate]. }
  assert (Hnd : NoDup (map snd L)).
  { apply nec_f_nodup_map_on; [apply NoDup_filter; exact HD |].
    intros [a1 a2] [b1 b2] Ha Hb E. simpl in E. subst b2.
    pose proof (HL _ Ha) as Ea. pose proof (HL _ Hb) as Eb. simpl in Ea, Eb.
    rewrite <- Eb in Ea. inversion Ea. reflexivity. }
  pose proof (NoDup_incl_length Hnd (fun z _ => nec_f_enum_full (2 ^ c) z)) as Hle.
  rewrite map_length, nec_f_enum_length in Hle. exact Hle.
Qed.

Theorem nec_f_grid_halving : compression_priced nec_f_grid_step nec_f_grid_cost nec_f_grid_eq_dec.
Proof.
  intros [] D HD. unfold image_size, nec_f_grid_cost.
  apply fiber_bound_compression; [exact HD |]. intro y. apply nec_f_grid_fiber. exact HD.
Qed.

(** The no-states of the grid: all of them flip under the move. *)
Definition nec_f_grid_flips : list NecFGrid :=
  filter (fun x => negb (nec_f_grid_cert x)) nec_f_grid_all.

Lemma nec_f_grid_flips_spec :
  forall x, In x nec_f_grid_flips ->
    nec_f_grid_cert x = false /\ nec_f_grid_cert (nec_f_grid_step x tt) = true.
Proof.
  intros x Hx. apply filter_In in Hx as [_ H]. apply negb_true_iff in H.
  split; [exact H | reflexivity].
Qed.

Lemma nec_f_col0_count :
  length (filter (fun b : NecFFin (2 ^ c) => Nat.eqb (proj1_sig b) 0) (nec_f_enum (2 ^ c))) = 1.
Proof.
  assert (Hgen : forall (l : list (NecFFin (2 ^ c))),
             length (filter (fun b => Nat.eqb (proj1_sig b) 0) l)
             = length (filter (fun k => Nat.eqb k 0) (map (@proj1_sig _ _) l))).
  { induction l as [| a l IH]; simpl; [reflexivity |].
    destruct (Nat.eqb (proj1_sig a) 0); simpl; rewrite IH; reflexivity. }
  rewrite Hgen, nec_f_enum_values.
  pose proof nec_f_pow_pos as Hp.
  destruct (2 ^ c) as [| p]; [lia |]. simpl.
  assert (Hz : forall s n, 0 < s -> filter (fun k => Nat.eqb k 0) (seq s n) = []).
  { intros s n. revert s. induction n as [| n IH]; intros s Hs; simpl; [reflexivity |].
    destruct s; [lia |]. simpl. apply IH. lia. }
  rewrite Hz by lia. reflexivity.
Qed.

Lemma nec_f_grid_yes_count : length (certified_states NecFGrid nec_f_grid_cert nec_f_grid_all) = m.
Proof.
  unfold certified_states, nec_f_grid_all.
  transitivity (length (nec_f_enum m) *
    length (filter (fun b : NecFFin (2 ^ c) => Nat.eqb (proj1_sig b) 0) (nec_f_enum (2 ^ c)))).
  - apply (nec_f_filter_prod_snd _ _ (fun b : NecFFin (2 ^ c) => Nat.eqb (proj1_sig b) 0)).
  - rewrite nec_f_col0_count, nec_f_enum_length. lia.
Qed.

Lemma nec_f_grid_flips_count : length nec_f_grid_flips + m = 2 ^ c * m.
Proof.
  pose proof (filter_split_length NecFGrid nec_f_grid_cert nec_f_grid_all) as H.
  pose proof nec_f_grid_yes_count as Hy. unfold certified_states in Hy.
  assert (Hall : length nec_f_grid_all = m * 2 ^ c).
  { unfold nec_f_grid_all, NecFGrid. rewrite prod_length, !nec_f_enum_length. reflexivity. }
  assert (Hy' : length (filter nec_f_grid_cert nec_f_grid_all) = m) by exact Hy.
  unfold nec_f_grid_flips. rewrite Hall, Hy' in H. lia.
Qed.

End Grid.

(** The squeeze bound is attained for every m and every c. *)
Theorem nec_f_squeeze_tight :
  forall m c,
    finite_states (nec_f_grid_all m c) /\
    permanent (nec_f_grid_step m c) (nec_f_grid_cert m c) /\
    compression_priced (nec_f_grid_step m c) (nec_f_grid_cost c) (nec_f_grid_eq_dec m c) /\
    nec_f_grid_cost c tt = c /\
    NoDup (nec_f_grid_flips m c) /\
    (forall s, In s (nec_f_grid_flips m c) ->
       nec_f_grid_cert m c s = false /\ nec_f_grid_cert m c (nec_f_grid_step m c s tt) = true) /\
    length (certified_states _ (nec_f_grid_cert m c) (nec_f_grid_all m c)) = m /\
    length (nec_f_grid_flips m c) + m = 2 ^ c * m.
Proof.
  intros m c.
  split; [apply nec_f_grid_finite | split; [apply nec_f_grid_permanent |]].
  split; [apply nec_f_grid_halving | split; [reflexivity |]].
  split; [apply NoDup_filter, nec_f_grid_finite |].
  split; [apply nec_f_grid_flips_spec |].
  split; [apply nec_f_grid_yes_count | apply nec_f_grid_flips_count].
Qed.


(** The membership of a prefix, stated once. *)
Lemma nec_f_in_firstn : forall (A : Type) k (l : list A) x, In x (firstn k l) -> In x l.
Proof.
  intros A k. induction k as [| k IH]; intros l x H; [destruct H |].
  destruct l as [| a l]; [destruct H |]. destruct H as [<- | H]; [left; reflexivity |].
  right. apply (IH l x H).
Qed.

(** For every m, k and c with m + k <= 2^c * m, a move of cost exactly c
    turns a list of exactly k no-states yes, beside exactly m yes-states, on a
    machine meeting every premise. With the squeeze bound, the least cost of
    such a move is the least c with m + k <= 2^c * m. *)
Theorem nec_f_squeeze_tight_every_k :
  forall m k c,
    m + k <= 2 ^ c * m ->
    exists F,
      NoDup F /\ length F = k /\
      (forall s, In s F ->
         nec_f_grid_cert m c s = false /\ nec_f_grid_cert m c (nec_f_grid_step m c s tt) = true) /\
      finite_states (nec_f_grid_all m c) /\
      permanent (nec_f_grid_step m c) (nec_f_grid_cert m c) /\
      compression_priced (nec_f_grid_step m c) (nec_f_grid_cost c) (nec_f_grid_eq_dec m c) /\
      nec_f_grid_cost c tt = c /\
      length (certified_states _ (nec_f_grid_cert m c) (nec_f_grid_all m c)) = m.
Proof.
  intros m k c Hk.
  destruct (nec_f_squeeze_tight m c) as [Hfin [Hperm [Hpr [Hc [Hnd [Hfl [Hm Hcount]]]]]]].
  exists (firstn k (nec_f_grid_flips m c)).
  split.
  - apply NoDup_app_remove_r with (l' := skipn k (nec_f_grid_flips m c)).
    rewrite firstn_skipn. exact Hnd.
  - split; [rewrite firstn_length; lia |].
    split; [intros s Hs; apply Hfl; apply (nec_f_in_firstn _ k _ s Hs) |].
    split; [exact Hfin | split; [exact Hperm | split; [exact Hpr | split; [exact Hc | exact Hm]]]].
Qed.

(** And no cost meeting the halving price is below the least such c, on this
    or any machine meeting the premises: that is the squeeze bound itself.
    On the grid, every halving-priced cost of the move is at least c when the
    move turns all (2^c - 1) * m no-states yes and m >= 1. *)
Theorem nec_f_grid_cost_least :
  forall m c (cost : unit -> nat),
    0 < m ->
    compression_priced (nec_f_grid_step m c) cost (nec_f_grid_eq_dec m c) ->
    c <= cost tt.
Proof.
  intros m c cost Hm Hp.
  destruct (nec_f_squeeze_tight m c) as [Hfin [Hperm [_ [_ [Hnd [Hfl [Hy Hcount]]]]]]].
  pose proof (permanent_flips_compression_bound _ _ _ _ cost (nec_f_grid_eq_dec m c)
                (nec_f_grid_all m c) tt (nec_f_grid_flips m c) Hfin Hperm Hp Hnd Hfl) as Hb.
  rewrite Hy in Hb.
  destruct (le_lt_dec c (cost tt)) as [Hle | Hlt]; [exact Hle | exfalso].
  assert (Hpow : 2 ^ cost tt * m < 2 ^ c * m).
  { apply Nat.mul_lt_mono_pos_r; [exact Hm | apply Nat.pow_lt_mono_r; lia]. }
  lia.
Qed.

(** * Each premise of the squeeze is needed *)

(** An injective move meets the halving price at cost zero. *)
Lemma nec_f_injective_halving_free :
  forall (S I : Type) (step : S -> I -> S) (eq_dec : forall a b : S, {a = b} + {a <> b}),
    (forall i, step_injective step i) -> compression_priced step (fun _ => 0) eq_dec.
Proof.
  intros S I step eq_dec Hinj i D HD. unfold image_size. simpl.
  rewrite nodup_fixed_point.
  - rewrite map_length. lia.
  - apply Injective_map_NoDup; [intros a b H; exact (Hinj i a b H) | exact HD].
Qed.

(** Without finiteness: the history machine, at cost zero. With the list of
    "all" states empty the bound reads 1 <= 0. *)
Theorem nec_f_squeeze_needs_finite :
  permanent history_step history_cert /\
  compression_priced history_step (fun _ : unit => 0) (list_eq_dec bool_dec) /\
  NoDup [@nil bool] /\
  (forall s, In s [@nil bool] -> history_cert s = false /\ history_cert (history_step s tt) = true) /\
  ~ (length [@nil bool] + length (certified_states _ history_cert [])
       <= 2 ^ 0 * length (certified_states _ history_cert [])).
Proof.
  destruct unbounded_history_escapes as [Hinj [Hperm [H0 H1]]].
  split; [exact Hperm |].
  split; [apply nec_f_injective_halving_free; intros []; exact Hinj |].
  split; [repeat constructor; intros [] |].
  split; [intros s [<- | []]; split; [exact H0 | exact H1] |].
  simpl. lia.
Qed.

(** Without permanence: negation on one bit, at cost zero. *)
Theorem nec_f_squeeze_needs_permanent :
  finite_states [false; true] /\
  compression_priced flip_step (fun _ : unit => 0) bool_dec /\
  NoDup [false] /\
  (forall s, In s [false] -> s = false /\ flip_step s tt = true) /\
  ~ (length [false] + length (certified_states _ (fun b : bool => b) [false; true])
       <= 2 ^ 0 * length (certified_states _ (fun b : bool => b) [false; true])).
Proof.
  destruct revocable_certificate_escapes as [Hinj [H1 H2]].
  split; [split; [repeat constructor; simpl; intuition discriminate | intros []; simpl; tauto] |].
  split; [apply nec_f_injective_halving_free; intros []; exact Hinj |].
  split; [repeat constructor; intros [] |].
  split; [intros s [<- | []]; split; reflexivity |].
  simpl. lia.
Qed.

Definition nec_f_sheet_eq_dec : forall a b : Sheet, {a = b} + {a <> b}.
Proof. decide equality. Defined.

(** Without the halving price: the stamp at cost zero. *)
Theorem nec_f_squeeze_needs_halving :
  finite_states [Blank; Stamped] /\ permanent stamp_step stamped /\
  ~ compression_priced stamp_step (fun _ : unit => 0) nec_f_sheet_eq_dec /\
  ~ (length [Blank] + length (certified_states _ stamped [Blank; Stamped])
       <= 2 ^ 0 * length (certified_states _ stamped [Blank; Stamped])).
Proof.
  split; [exact sheets_finite | split; [exact stamp_is_permanent | split]].
  - intro H. specialize (H tt [Blank; Stamped]).
    assert (Hnd : NoDup [Blank; Stamped]) by (repeat constructor; simpl; intuition discriminate).
    specialize (H Hnd). vm_compute in H. lia.
  - simpl. lia.
Qed.

(** The rounded-logarithm form in the repo is strictly weaker than the
    integer form: with m = 3 and k = 1 it allows cost 0, the integer form
    does not. *)
Theorem nec_f_rounded_log_form_weaker :
  Nat.log2_up (3 + 1) <= 0 + Nat.log2_up 3 /\ ~ (3 + 1 <= 2 ^ 0 * 3).
Proof. split; [vm_compute; lia | simpl; lia]. Qed.

Print Assumptions nec_f_squeeze_tight.
Print Assumptions nec_f_squeeze_tight_every_k.
Print Assumptions nec_f_grid_cost_least.
Print Assumptions nec_f_injective_halving_free.
Print Assumptions nec_f_squeeze_needs_finite.
Print Assumptions nec_f_squeeze_needs_permanent.
Print Assumptions nec_f_squeeze_needs_halving.
Print Assumptions nec_f_rounded_log_form_weaker.

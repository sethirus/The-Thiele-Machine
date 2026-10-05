(** PresentedDemo.v: an explicit computably presented Thiele machine, run
    on the one fixed universal host U_P.

    The machine demo: states are natural numbers, there is one move
    (unit), the move adds 1 to the state and costs 3, and the reading is
    yes exactly when the state is at least 3. The driver always takes the
    move, so the machine never halts. Every state is its own code and the
    one move has code 0.

    Its presentation pu_demo_pc gives four mu-recursive algorithms, written
    directly as terms of the vendored recalg type with their relational
    meaning ra_rel proved here:

      driver   the constant 1 (take the move of code 0);
      step     the successor of the state code;
      cost     the constant 3;
      reading  sg (pred (pred v)), with pred and sg (0 at 0, 1 above)
               each one primitive recursion: 1 exactly when v >= 3.

    So the definition of a computably presented machine is not empty
    (pu_demo_computably_presented), and the main theorem applies to it
    (pu_demo_universal). From the start state 0 the reading first turns
    yes after 3 moves; the first raising move costs 3, so the surcharge is
    0: at every matching point the host ledger is exactly 3 per move
    (pu_demo_exact), the host never halts (pu_demo_never_halts), and its
    flag rises (pu_demo_flag_rises), with the host's own earned chain on
    the claim URun r (pu_demo_earned).

    Dependencies: as PresentedUniversal.v, plus the vendored MuRec files
    MuRec.v and recalg.v. No axioms, no Admitted.                           *)

From Coq Require Import Arith Lia Bool.
From Undecidability.Shared.Libs.DLW Require Import utils pos vec.
From Undecidability.MuRec.Util Require Import recalg.
From Undecidability.FRACTRAN.Util Require Import prime_seq.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Minimal.Presentation.
Require Import Minimal.UniversalPCodes Minimal.UniversalPBridge Minimal.UniversalPLayout
  Minimal.UniversalPRun.
Require Import Minimal.CompilerCodes Minimal.CompilerChecker Minimal.CompilerGuest
  Minimal.CompilerGuestRun Minimal.PresentedUniversal.
Module T := Minimal.ThieleComplete.

(* ================================================================= *)
(* The machine.                                                       *)
(* ================================================================= *)

Lemma pu_demo_toll : forall (s : nat) (i : unit),
  Nat.leb 3 s = false -> Nat.leb 3 (S s) = true -> 3 >= 1.
Proof. intros. lia. Qed.

Definition pu_demo_sys : T.CertificationSystem :=
  T.mk_cert_system nat unit (fun s _ => S s) (fun _ => 3) (fun s => Nat.leb 3 s) pu_demo_toll.

Lemma pu_demo_idec : forall i : unit, Some tt = Some i.
Proof. intros []. reflexivity. Qed.

Definition pu_demo : presented_machine :=
  mk_presented pu_demo_sys (fun _ => Some tt) (fun s => s) (fun v => Some v)
    (fun _ => 0) (fun _ => Some tt) (fun s => eq_refl) pu_demo_idec.

(* ================================================================= *)
(* Relational meaning of the algorithms.                              *)
(* ================================================================= *)

Lemma pu_ra_comp : forall k i (f : recalg k) (gj : vec (recalg i) k) v x w,
  ra_rel f w x -> (forall p, ra_rel (vec_pos gj p) v (vec_pos w p)) ->
  ra_rel (ra_comp f gj) v x.
Proof.
  intros k i f gj v x w Hf Hg. rewrite ra_rel_fix_comp. exists w. split; [exact Hf |].
  intro p. rewrite vec_pos_map. apply Hg.
Qed.

Lemma pu_ra_rec1 : forall (f : recalg 0) (g : recalg 2) n y (s : nat -> nat),
  ra_rel f vec_nil (s 0) -> s n = y ->
  (forall i, i < n -> ra_rel g (i ## s i ## vec_nil) (s (S i))) ->
  ra_rel (ra_rec f g) (n ## vec_nil) y.
Proof.
  intros f g n y s H0 Hn Hs. rewrite ra_rel_fix_rec. apply s_rec_eq.
  exists s. simpl. auto.
Qed.

Lemma pu_ra_cst1 : forall i (v : vec nat i) c,
  ra_rel (ra_comp (ra_cst c) vec_nil) v c.
Proof.
  intros i v c. apply (pu_ra_comp _ _ _ _ _ _ vec_nil).
  - rewrite ra_rel_fix_cst. reflexivity.
  - intro p. pos_inv p.
Qed.

Lemma pu_ra_proj0 : forall n (v : vec nat (S n)), ra_rel (ra_proj pos0) v (vec_pos v pos0).
Proof. intros n v. rewrite ra_rel_fix_proj. reflexivity. Qed.

(* pred: 0 at 0, n at S n. *)
Definition pu_ra_pred : recalg 1 := ra_rec (ra_cst 0) (ra_proj pos0).

Lemma pu_ra_pred_spec : forall n, ra_rel pu_ra_pred (n ## vec_nil) (n - 1).
Proof.
  intro n. apply (pu_ra_rec1 _ _ n (n - 1) (fun i => i - 1)).
  - rewrite ra_rel_fix_cst. reflexivity.
  - reflexivity.
  - intros i _. rewrite ra_rel_fix_proj. simpl. lia.
Qed.

(* sg: 0 at 0, 1 above. *)
Definition pu_ra_sg : recalg 1 := ra_rec (ra_cst 0) (ra_comp (ra_cst 1) vec_nil).

Lemma pu_ra_sg_spec : forall n, ra_rel pu_ra_sg (n ## vec_nil) (if Nat.eqb n 0 then 0 else 1).
Proof.
  intro n. apply (pu_ra_rec1 _ _ n _ (fun i => if Nat.eqb i 0 then 0 else 1)).
  - rewrite ra_rel_fix_cst. reflexivity.
  - reflexivity.
  - intros i _. apply pu_ra_cst1.
Qed.

(* The four algorithms. *)
Definition pu_demo_next_ra : recalg 1 := ra_comp (ra_cst 1) vec_nil.
Definition pu_demo_step_ra : recalg 2 := ra_comp ra_succ (ra_proj pos0 ## vec_nil).
Definition pu_demo_cost_ra : recalg 1 := ra_comp (ra_cst 3) vec_nil.
Definition pu_demo_read_ra : recalg 1 :=
  ra_comp pu_ra_sg
    (ra_comp pu_ra_pred (ra_comp pu_ra_pred (ra_proj pos0 ## vec_nil) ## vec_nil) ## vec_nil).

Lemma pu_demo_read_val : forall v, cg_read_val pu_demo v = if Nat.leb 3 v then 1 else 0.
Proof. intro v. unfold cg_read_val. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma pu_demo_read_spec : forall v,
  ra_rel pu_demo_read_ra (v ## vec_nil) (cg_read_val pu_demo v).
Proof.
  intro v. rewrite pu_demo_read_val.
  apply (pu_ra_comp _ _ _ _ _ _ (v - 1 - 1 ## vec_nil)).
  - replace (if Nat.leb 3 v then 1 else 0) with (if Nat.eqb (v - 1 - 1) 0 then 0 else 1).
    + apply pu_ra_sg_spec.
    + destruct (Nat.leb_spec 3 v) as [H | H]; destruct (Nat.eqb_spec (v - 1 - 1) 0); lia.
  - intro p. analyse pos p.
    apply (pu_ra_comp _ _ _ _ _ _ (v - 1 ## vec_nil)); [apply pu_ra_pred_spec |].
    intro p. analyse pos p.
    apply (pu_ra_comp _ _ _ _ _ _ (v ## vec_nil)); [apply pu_ra_pred_spec |].
    intro p. analyse pos p. apply (pu_ra_proj0 0 (v ## vec_nil)).
Qed.

Definition pu_demo_pc : cg_presentation pu_demo.
Proof.
  refine (cg_mk_presentation pu_demo pu_demo_next_ra pu_demo_step_ra pu_demo_cost_ra
            pu_demo_read_ra _ _ _ pu_demo_read_spec).
  - intro s. apply pu_ra_cst1.
  - intros s i. apply (pu_ra_comp _ _ _ _ _ _ (s ## vec_nil)).
    + rewrite ra_rel_fix_succ. reflexivity.
    + intro p. analyse pos p. apply (pu_ra_proj0 1 (s ## 0 ## vec_nil)).
  - intro i. apply pu_ra_cst1.
Defined.

(* The definition of a computably presented machine is not empty. *)
Theorem pu_demo_computably_presented : cg_computably_presented pu_demo.
Proof. exact (inhabits pu_demo_pc). Qed.

(* ================================================================= *)
(* The main theorem on the demo.                                      *)
(* ================================================================= *)

Local Notation rd := (T.cs_cert (pm_sys pu_demo)).

Lemma pu_demo_run : forall s0 n, presented_run pu_demo s0 n = s0 + n.
Proof.
  intros s0 n. revert s0. induction n as [| n IH]; intro s0; [simpl; lia |].
  simpl. rewrite IH. lia.
Qed.

Lemma pu_demo_ledger : forall s0 n, mledger pu_demo s0 n = 3 * n.
Proof.
  intros s0 n. revert s0. induction n as [| n IH]; intro s0; [reflexivity |].
  simpl. rewrite IH. lia.
Qed.

Lemma pu_demo_running : forall s0 m, pm_next pu_demo (presented_run pu_demo s0 m) <> None.
Proof. intros. discriminate. Qed.

Lemma pu_demo_first_raise : forall n i, first_raise pu_demo 0 n = Some i ->
  T.cs_cost (pm_sys pu_demo) i >= 3.
Proof. intros n i _. simpl. lia. Qed.

(* The main theorem, instantiated: its statement is the statement of
   presented_universal at demo and pu_demo_pc. *)
Corollary pu_demo_universal :
  ltac:(let t := type of (presented_universal pu_demo pu_demo_pc) in exact t).
Proof. exact (presented_universal pu_demo pu_demo_pc). Qed.

(* From state 0 the host never halts: the machine never halts. *)
Theorem pu_demo_never_halts : forall t,
  ~ M.pu_halted U_P (M.core_of (pu_host_at pu_demo pu_demo_pc 0 t)).
Proof.
  intros t Ht. destruct (proj1 (presented_universal_halting pu_demo pu_demo_pc 0)
                          (ex_intro _ t Ht)) as [n Hn].
  unfold mhalted in Hn. discriminate Hn.
Qed.

(* The host flag rises: the reading is yes after 3 moves. *)
Theorem pu_demo_flag_rises : exists t, M.cert (pu_host_at pu_demo pu_demo_pc 0 t) = true.
Proof.
  apply (presented_universal_flag_iff pu_demo pu_demo_pc 0). exists 3.
  rewrite pu_demo_run. reflexivity.
Qed.

(* The surcharge is 0: at every matching point the host has paid exactly
   3 per move, its counter B decodes to the state n, and its flag is the
   latch. *)
Theorem pu_demo_exact : forall n, exists t,
  pu_decode pu_demo (hv (pu_host_at pu_demo pu_demo_pc 0 t) pu_RB) = Some n /\
  M.mu (pu_host_at pu_demo pu_demo_pc 0 t) = 3 * n /\
  M.cert (pu_host_at pu_demo pu_demo_pc 0 t) = Nat.leb 3 n.
Proof.
  intro n.
  destruct (presented_universal_exact pu_demo pu_demo_pc 0 eq_refl pu_demo_first_raise n
              (fun m _ => pu_demo_running 0 m)) as [_ (t & Hd & Hm & Hc)].
  exists t. rewrite pu_demo_run in Hd. rewrite pu_demo_ledger in Hm.
  split; [exact Hd |]. split; [exact Hm |]. rewrite Hc.
  destruct (mlatch pu_demo 0 n) eqn:Hl.
  - apply presented_mlatch_iff in Hl as [m [Hm' Hr]]. rewrite pu_demo_run in Hr.
    change (Nat.leb 3 (0 + m) = true) in Hr. apply Nat.leb_le in Hr.
    symmetry. apply Nat.leb_le. lia.
  - symmetry. apply Nat.leb_gt. destruct (Nat.leb_spec 3 n) as [H | H]; [| exact H].
    exfalso. assert (Hy : mlatch pu_demo 0 n = true).
    { apply presented_mlatch_iff. exists n. split; [lia |]. rewrite pu_demo_run.
      apply Nat.leb_le. exact H. }
    congruence.
Qed.

(* Whenever the host flag is up, the host's own run holds its earned chain
   on a slot of bank B carrying the claim URun r, and the checked value
   decodes to a state of at least 3. *)
Theorem pu_demo_earned : forall t,
  M.cert (pu_host_at pu_demo pu_demo_pc 0 t) = true ->
  exists k v m pre1 mid1 mid2 post,
    k < 16 /\
    M.pu_trace_of pu_hprop_eqb pu_heval t U_P (pu_host_start pu_demo pu_demo_pc 0) =
      app pre1 (M.CHECK PSlot (pu_SLOT E.CB k) :: app mid1
        (M.COMMIT PSlot (pu_SLOT E.CB k) :: app mid2 (M.CERTIFY :: post))) /\
    hv (M.pu_run pu_hprop_eqb pu_heval pre1 (pu_host_start pu_demo pu_demo_pc 0))
      (pu_SLOT E.CB k) = pu_pair (pu_pcode (URun (cg_r pu_demo pu_demo_pc))) v /\
    cg_ueval (URun (cg_r pu_demo pu_demo_pc)) v = true /\
    pu_decode pu_demo v = Some m /\ 3 <= m.
Proof.
  intros t Hc.
  destruct (presented_universal_earned pu_demo pu_demo_pc 0 t Hc)
    as (k & v & m & pre1 & mid1 & mid2 & post & Hk & Hl & _ & _ & _ & _ & _ & Hv & He & Hd & Hr).
  rewrite pu_demo_run in Hd, Hr. change (Nat.leb 3 (0 + m) = true) in Hr.
  apply Nat.leb_le in Hr. change (pu_decode pu_demo v = Some (0 + m)) in Hd.
  rewrite Nat.add_0_l in Hd, Hr.
  exists k, v, m, pre1, mid1, mid2, post.
  split; [exact Hk |]. split; [exact Hl |]. split; [exact Hv |]. split; [exact He |].
  split; [exact Hd | exact Hr].
Qed.

(* ================================================================= *)
(* Assumption audit.                                                  *)
(* ================================================================= *)

Print Assumptions pu_demo_read_spec.
Print Assumptions pu_demo_computably_presented.
Print Assumptions pu_demo_universal.
Print Assumptions pu_demo_never_halts.
Print Assumptions pu_demo_flag_rises.
Print Assumptions pu_demo_exact.
Print Assumptions pu_demo_earned.

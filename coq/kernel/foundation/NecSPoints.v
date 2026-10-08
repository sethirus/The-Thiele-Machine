(** NecSPoints.v: the matching points of "One host runs every computably
    presented Thiele machine" need no "M has not stopped before move n".

    presented_universal_points assumes that M is still running at every
    move before n. That hypothesis can be dropped: for EVERY n there is a
    host time at which counter B decodes to M's state after n moves, the
    host ledger is M's ledger after n moves plus the surcharge, and the
    host flag is M's latch after n moves. After M stops, its state, ledger,
    latch and surcharge stay where they were, and the host halts at a point
    matching the stop. The same holds for "within two".                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Minimal.ThieleComplete.
Require Import Minimal.Presented Kernel.Presentation.
Require Import Kernel.UniversalPCodes Kernel.UniversalPBridge Kernel.UniversalPBlocks
  Kernel.UniversalPLayout Kernel.UniversalPPhases Kernel.UniversalPSim Kernel.UniversalPRun.
Require Import Kernel.PresentedUniversal.
Module T := Minimal.ThieleComplete.

Section Points.

Variable Mp : presented_machine.
Variable pc : cg_presentation Mp.

Local Notation st := (T.cs_state (pm_sys Mp)).

(* Either M runs at every move before n, or it first stops at some m < n. *)
Lemma nec_s_first_stop : forall (s0 : st) n,
  (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) \/
  (exists m, m < n /\ pm_next Mp (presented_run Mp s0 m) = None /\
             forall k, k < m -> pm_next Mp (presented_run Mp s0 k) <> None).
Proof.
  intros s0 n. induction n as [| n IH].
  - left. intros m Hm. lia.
  - destruct IH as [H | [m [Hm [Hs Hk]]]].
    + destruct (pm_next Mp (presented_run Mp s0 n)) eqn:E.
      * left. intros m Hm. destruct (Nat.eq_dec m n) as [-> | Hne].
        -- rewrite E. discriminate.
        -- apply H. lia.
      * right. exists n. split; [lia |]. split; [exact E | exact H].
    + right. exists m. split; [lia |]. split; [exact Hs | exact Hk].
Qed.

Lemma nec_s_after_stop : forall (s0 : st) m n,
  pm_next Mp (presented_run Mp s0 m) = None -> m <= n ->
  presented_run Mp s0 n = presented_run Mp s0 m /\
  mledger Mp s0 n = mledger Mp s0 m /\
  mlatch Mp s0 n = mlatch Mp s0 m /\
  surcharge Mp s0 n = surcharge Mp s0 m.
Proof.
  intros s0 m n Hs Hle.
  destruct (presented_halted_stable Mp s0 m n Hs Hle) as [Hr Hl].
  assert (Hlat : mlatch Mp s0 n = mlatch Mp s0 m).
  { destruct (mlatch Mp s0 m) eqn:Hm.
    - exact (presented_mlatch_mono Mp s0 m n Hle Hm).
    - destruct (mlatch Mp s0 n) eqn:Hn; [| reflexivity].
      apply presented_mlatch_iff in Hn as [k [Hk Hrd]].
      assert (Hrk : T.cs_cert (pm_sys Mp) (presented_run Mp s0 (Nat.min k m)) = true).
      { destruct (le_lt_dec k m) as [H | H].
        - rewrite Nat.min_l by exact H. exact Hrd.
        - rewrite Nat.min_r by lia.
          destruct (presented_halted_stable Mp s0 m k Hs ltac:(lia)) as [Hk' _].
          rewrite <- Hk'. exact Hrd. }
      assert (Hy : mlatch Mp s0 m = true).
      { apply presented_mlatch_iff. exists (Nat.min k m). split; [lia | exact Hrk]. }
      congruence. }
  split; [exact Hr |]. split; [exact Hl |]. split; [exact Hlat |].
  destruct (mlatch Mp s0 m) eqn:Hm.
  - exact (presented_surcharge_stable Mp s0 m n Hle Hm).
  - unfold surcharge. rewrite Hlat, Hm. reflexivity.
Qed.

Theorem nec_s_presented_points_every_n : forall (s0 : st) n,
  exists t,
    pu_decode Mp (hv (pu_host_at Mp pc s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    M.mu (pu_host_at Mp pc s0 t) = mledger Mp s0 n + surcharge Mp s0 n /\
    M.cert (pu_host_at Mp pc s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 n. destruct (nec_s_first_stop s0 n) as [H | [m [Hm [Hs Hk]]]].
  - exact (presented_universal_points Mp pc s0 n H).
  - destruct (presented_universal_halt_point Mp pc s0 m Hk Hs) as (t & _ & Hd & Hmu & Hc).
    destruct (nec_s_after_stop s0 m n Hs ltac:(lia)) as [Hr [Hl [Hlat Hsur]]].
    exists t. rewrite Hr, Hl, Hlat, Hsur. auto.
Qed.

Theorem nec_s_presented_within_two_every_n : forall (s0 : st) n,
  T.cs_cert (pm_sys Mp) s0 = false ->
  exists t,
    pu_decode Mp (hv (pu_host_at Mp pc s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    mledger Mp s0 n <= M.mu (pu_host_at Mp pc s0 t) <= mledger Mp s0 n + 2 /\
    M.cert (pu_host_at Mp pc s0 t) = mlatch Mp s0 n.
Proof.
  intros s0 n H0. destruct (nec_s_presented_points_every_n s0 n) as (t & Hd & Hm & Hc).
  pose proof (presented_surcharge_le_two Mp s0 n H0).
  exists t. split; [exact Hd |]. split; [lia | exact Hc].
Qed.

End Points.

Print Assumptions nec_s_presented_points_every_n.
Print Assumptions nec_s_presented_within_two_every_n.

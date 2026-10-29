(** NeutralHost.v: U_P as a host for neutral-complete guests.
    A neutral-complete machine obeys the toll (nc_is_weak), so with a
    driver, codes and a mu-recursive presentation it is a computably
    presented machine and PresentedUniversal.v applies to it unchanged.
    Here: its raising moves cost exactly 1, so once its record is up the
    surcharge is EXACTLY 2 (= 3 - 1), and U_P's ledger is the guest's plus 2. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.Presented.
Require Import Minimal.NeutralComplete.

(* Raising moves of a neutral-complete machine cost exactly 1. *)
Theorem nc_raise_costs_one : forall M (J : neutral_interface M),
  neutral_complete_with J ->
  forall s m, m_record M s = false -> m_record M (m_step M s m) = true -> m_cost M m = 1.
Proof.
  intros M J [[_ [Hb _]] [_ [[Hc _] _]]] s m H0 H1. rewrite Hc. unfold n_price.
  rewrite (nc_raise_is_mark M J Hb s m H0 H1). reflexivity.
Qed.

(* For any presented machine whose raising moves cost exactly 1 (every
   neutral-complete guest), the surcharge after the raise is exactly 2. *)
Theorem unit_raise_surcharge_two : forall (Mp : presented_machine) s0 n,
  (forall s i, T.cs_cert (pm_sys Mp) s = false ->
     T.cs_cert (pm_sys Mp) (T.cs_step (pm_sys Mp) s i) = true -> T.cs_cost (pm_sys Mp) i = 1) ->
  T.cs_cert (pm_sys Mp) s0 = false -> mlatch Mp s0 n = true -> surcharge Mp s0 n = 2.
Proof.
  intros Mp s0 n H1 H0 Hl. unfold surcharge. rewrite Hl.
  destruct (presented_first_raise_spec Mp n s0 H0 Hl) as [m [i [_ [_ [Hall [Hup Hf]]]]]].
  unfold raise_cost. rewrite Hf. rewrite (H1 _ i (Hall m (le_n m)) Hup). reflexivity.
Qed.

Print Assumptions nc_raise_costs_one.
Print Assumptions unit_raise_surcharge_two.

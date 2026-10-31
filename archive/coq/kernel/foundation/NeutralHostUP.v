(** NeutralHostUP.v: U_P runs every computably presented
    neutral-complete guest, with the guest's record as its flag and its
    ledger plus exactly 2 once the record is up. *)
From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.ThieleComplete.
Require Import Minimal.Presented.
Require Import Minimal.NeutralComplete.
Require Import Minimal.NeutralHost.
Require Import Kernel.UniversalPBridge.
Require Import Kernel.UniversalPLayout.
Require Import Kernel.PresentedUniversal.
Require Import Kernel.Presentation.
Require Minimal.EarnedMultiPriced.

Theorem up_hosts_unit_raise_guest : forall (Mp : presented_machine) (pc : cg_presentation Mp) s0 n,
  (forall s i, T.cs_cert (pm_sys Mp) s = false ->
     T.cs_cert (pm_sys Mp) (T.cs_step (pm_sys Mp) s i) = true -> T.cs_cost (pm_sys Mp) i = 1) ->
  T.cs_cert (pm_sys Mp) s0 = false ->
  (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  exists t,
    pu_decode Mp (hv (pu_host_at Mp pc s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    Minimal.EarnedMultiPriced.mu (pu_host_at Mp pc s0 t) =
      mledger Mp s0 n + (if mlatch Mp s0 n then 2 else 0) /\
    Minimal.EarnedMultiPriced.cert (pu_host_at Mp pc s0 t) = mlatch Mp s0 n.
Proof.
  intros Mp pc s0 n H1 H0 Hn.
  destruct (presented_universal_points Mp pc s0 n Hn) as (t & Hd & Hm & Hc).
  exists t. split; [exact Hd |]. split; [| exact Hc].
  rewrite Hm. destruct (mlatch Mp s0 n) eqn:Hl.
  - rewrite (unit_raise_surcharge_two Mp s0 n H1 H0 Hl). reflexivity.
  - unfold surcharge. rewrite Hl. reflexivity.
Qed.

Lemma nc_unit_raise : forall M, neutral_complete M ->
  forall s i, m_record M s = false -> m_record M (m_step M s i) = true -> m_cost M i = 1.
Proof. intros M [J HJ] s i Hd Hu. exact (nc_raise_costs_one M J HJ s i Hd Hu). Qed.

(* Instantiated: a neutral-complete machine with a driver and codes. *)
Theorem up_hosts_nc_guest : forall (M : machine) (H : neutral_complete M)
  (next : m_state M -> option (m_move M))
  (scode : m_state M -> nat) (sdec : nat -> option (m_state M))
  (icode : m_move M -> nat) (idec : nat -> option (m_move M))
  (Hs : forall s, sdec (scode s) = Some s) (Hi : forall i, idec (icode i) = Some i),
  let Mp := mk_presented (nc_cert_system M H) next scode sdec icode idec Hs Hi in
  forall (pc : cg_presentation Mp) s0 n,
  m_record M s0 = false ->
  (forall m, m < n -> pm_next Mp (presented_run Mp s0 m) <> None) ->
  exists t,
    pu_decode Mp (hv (pu_host_at Mp pc s0 t) pu_RB) = Some (presented_run Mp s0 n) /\
    Minimal.EarnedMultiPriced.mu (pu_host_at Mp pc s0 t) =
      mledger Mp s0 n + (if mlatch Mp s0 n then 2 else 0) /\
    Minimal.EarnedMultiPriced.cert (pu_host_at Mp pc s0 t) = mlatch Mp s0 n.
Proof.
  intros M H next scode sdec icode idec Hs Hi Mp pc s0 n H0 Hn.
  apply up_hosts_unit_raise_guest; [| exact H0 | exact Hn].
  intros s i Hd Hu. exact (nc_unit_raise M H s i Hd Hu).
Qed.

Print Assumptions up_hosts_unit_raise_guest.
Print Assumptions up_hosts_nc_guest.

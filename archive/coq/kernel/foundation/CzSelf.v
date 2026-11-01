(** CzSelf: the class of Thiele-complete machines is closed under the
    composition operations, and every level of a tower of nested runs is the
    same Thiele-complete host.

      cmpz_closed_prod, cmpz_closed_seq   the product, and the sequential
                          composite, of Thiele-complete machines are
                          Thiele-complete;
      cmpz_tower_self_similar
                          under the hypotheses of the exact tower, every
                          level above the first is a run of the one fixed
                          host machine of the repository, which is
                          Thiele-complete, and the tower of k + 1 levels adds
                          exactly the first level's surcharge plus 2 per
                          further level. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
From Kernel Require Import AxCore.
From Kernel Require Import AxLatch.
From Kernel Require Import AxComplete.
From Kernel Require Import CzProd CzProdTC CzLoad CzSeq CzTower.
From Minimal Require Import CzLink.
Require Import Kernel.UniversalPCodes Kernel.UniversalPRun Kernel.PresentedUniversal.
Require Import Minimal.Presented Kernel.Presentation.
Require Minimal.ThieleComplete.
Module T := Minimal.ThieleComplete.

Theorem cmpz_closed_prod : forall {A B P Q} (M : amachine A P) (N : amachine B Q),
  ax_thiele_complete M -> ax_thiele_complete N -> ax_thiele_complete (cmpz_prod M N).
Proof. intros. exact (cmpz_prod_thiele_complete M N H H0). Qed.

Theorem cmpz_closed_seq : forall {A B P Q} {M : amachine A P} {N : amachine B Q}
    (I1 : ax_interface M) (I2 : ax_interface N),
  ax_tc_with I1 -> ax_tc_with I2 -> ax_thiele_complete (cmpz_seq (M := M) I2).
Proof.
  intros A B P Q M N I1 I2 H1 H2. exists (cmpz_seq_iface I1 I2). exact (cmpz_seq_tc I1 I2 H1 H2).
Qed.

Theorem cmpz_tower_self_similar :
  forall (Mp : nat -> presented_machine) (pc : forall i, cg_presentation (Mp i))
    (s0 : forall i, T.cs_state (pm_sys (Mp i)))
    (f : forall i, ds_state cmpz_ds_host -> ds_state (cmpz_ds_pres (Mp (S i)))) lo0 hi0,
  (forall i, cmpz_presents_by (Mp (S i)) (s0 (S i)) cmpz_ds_host
               (pu_host_start (Mp i) (pc i) (s0 i)) (f i)) ->
  (forall n, mlatch (Mp 0) (s0 0) n = true ->
     lo0 <= surcharge (Mp 0) (s0 0) n /\ surcharge (Mp 0) (s0 0) n <= hi0) ->
  T.thiele_complete pu_host_machine /\
  forall k, cmpz_link (cmpz_ds_pres (Mp 0)) (cmpz_ds_pres (Mp (S k)))
    (cmpz_pres_start (Mp 0) (s0 0)) (cmpz_pres_start (Mp (S k)) (s0 (S k)))
    (lo0 + 2 * k) (hi0 + 2 * k)
    (cmpz_tower_rel (fun i => cmpz_ds_pres (Mp i))
       (fun i => cmpz_rel_comp (cmpz_rel_host (Mp i) (pc i)) (fun h x => f i h = x)) (S k)).
Proof.
  intros Mp pc s0 f lo0 hi0 Hp H0. split.
  - exact pu_universal_thiele_complete.
  - intro k. exact (cmpz_tower_presented_exact Mp pc s0 f lo0 hi0 Hp H0 k).
Qed.

Print Assumptions cmpz_closed_prod.
Print Assumptions cmpz_closed_seq.
Print Assumptions cmpz_tower_self_similar.

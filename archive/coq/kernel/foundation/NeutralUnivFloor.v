(** NeutralUnivFloor.v: the surcharge, host by host.

      tc_host_floor     on a host that is Thiele-complete through an interface
                        for which the load is clean, every program run that
                        ends with the record up has ledger at least 3;
      tc_surcharge      so at a matching point where the guest's record is up
                        the surcharge is at least 3 minus the guest's ledger;
      tc_cdown_two      no Thiele-complete host with clean loads is a universal
                        machine (even in the weak, order-free sense) for the
                        countdown class Cdown with surcharge bound below 2;
      down_universal    (NeutralUnivCanon.v) the neutral host CNH is one with bound 0.

    So the "surcharge exactly 2" of U_P on a neutral guest is the price of
    certification (the floor of 3 against a raise that costs the guest 1),
    not of universality.                                                  *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Kernel.UMachDef.
Require Import Kernel.NeutralUnivBase.
Require Import Kernel.NeutralUnivDef.
Require Import Kernel.NeutralUnivCanon.
Require Import Kernel.NeutralUnivCert.
Require Import Minimal.ThieleComplete.
Require Import Minimal.NeutralComplete.

Section Floor.
Variable H : host.

Lemma hl_trace : forall P n h, hl P h n = tc_cost_sum (M:=hmach H) (htrace H P h n).
Proof.
  intros P n. induction n as [| n IH]; intros h; [reflexivity |].
  simpl. destruct (hnext H P h); simpl; [rewrite IH; reflexivity | reflexivity].
Qed.

Theorem tc_host_floor : forall (I : thiele_interface (hmach H)), thiele_complete_with I ->
  forall P h0, ti_clean I h0 -> forall n, hflag H (hr P h0 n) = true -> hl P h0 n >= 3.
Proof.
  intros I HI P h0 Hc n Hup. rewrite (hr_trace H) in Hup.
  destruct (certificate_costs_three (hmach H) I HI h0 _ Hc Hup) as [H3 _].
  pose proof HI as (_ & _ & [Hcost _] & _).
  rewrite (record_moves_cost (hmach H) I Hcost) in H3. rewrite hl_trace. exact H3.
Qed.

Corollary tc_surcharge : forall (I : thiele_interface (hmach H)), thiele_complete_with I ->
  forall (C : gclass) (i : gi C) P h0 n m s, ti_clean I h0 ->
  hflag H (hr P h0 n) = glat i m -> glat i m = true -> hl P h0 n = gledger i m + s ->
  s >= 3 - gledger i m.
Proof.
  intros I HI C i P h0 n m s Hc Hf Hg Hl.
  apply (surcharge_floor C H P h0 i 3 n m s); auto.
  intros t Ht. exact (tc_host_floor I HI P h0 Hc t Ht).
Qed.

End Floor.

(* The countdown guest from x = 0 raises its record at step 2 with ledger 1. *)
Lemma cdown0 : live_before (C:=Cdown) 0 2 /\ glat (C:=Cdown) 0 2 = true /\ gledger (C:=Cdown) 0 2 = 1.
Proof.
  split; [intros k Hk; destruct k as [| [|]]; try lia; discriminate |]. split; reflexivity.
Qed.

Theorem tc_cdown_two : forall (H : host) (I : thiele_interface (hmach H)) (K : nat) P (R : reg_host H)
  (tpl : (nat -> nat) -> hS H) (code : nat -> nat -> nat) (dec : (nat -> nat) -> nat * nat),
  thiele_complete_with I -> (forall rho, ti_clean I (tpl rho)) ->
  (forall m, live_before (C:=Cdown) 0 m -> exists n,
     match_at Cdown H (fun _ => (nat * nat)%type) dobs K P (tpl (code 0)) 0 (fun h => dec (b_reg R h)) n m) ->
  K >= 2.
Proof.
  intros H I K P R tpl code dec HI Hcl Hm.
  destruct cdown0 as (L2 & G2 & Led2).
  destruct (Hm 2 L2) as (n & _ & F & s & Hs & Hl).
  pose proof (tc_surcharge H I HI Cdown 0 P (tpl (code 0)) n 2 s (Hcl _) F G2 Hl) as X.
  rewrite Led2 in X. lia.
Qed.

Print Assumptions tc_host_floor.
Print Assumptions tc_surcharge.
Print Assumptions tc_cdown_two.

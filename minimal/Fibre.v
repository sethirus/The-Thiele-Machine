(* SCOPE NOTE: standalone proof scope.
   Applies the abstract finite holding theorem within a fixed observation fibre.
   The stated interface supplies the hypotheses; no concrete native-machine
   implementation is assumed. *)

From Coq Require Import List Bool.
From Minimal Require Import CompleteHost.
Import ListNotations.

Theorem permanent_check_in_finite_fibre_merges
 {State Base:Type} (eq_dec:forall a b:State,{a=b}+{a<>b})
 (check:State->State) (observe:State->Base) (verdict:State->bool)
 (b:Base) (u:State) (held:list State) :
 observe u=b -> verdict u=false -> verdict(check u)=true ->
 (forall s,observe s=b -> observe(check s)=b) ->
 (forall s,observe s=b -> verdict s=true -> verdict(check s)=true) ->
 NoDup held ->
 (forall s,In s held <-> observe s=b /\ verdict s=true) ->
 exists s t,observe s=b /\ observe t=b /\ s<>t /\ check s=check t.
Proof.
 intros Hub Huv Hraise Hbase Hperm Hnd Hheld.
 assert(Hout:~(observe u=b /\ verdict u=true)) by (intros [_ Hv]; congruence).
 assert(Hin:observe(check u)=b /\ verdict(check u)=true) by auto.
 assert(Hclosed:forall s,observe s=b /\ verdict s=true ->
   observe(check s)=b /\ verdict(check s)=true).
 { intros s [Hb Hv]; split; auto. }
 destruct (@finite_hold_collision State check
   (fun s=>observe s=b /\ verdict s=true) u Hout Hin Hclosed eq_dec held Hnd Hheld)
   as [s [t [Hs [Ht [Hneq He]]]]].
 exists s,t; assert(Hbs:observe s=b).
 { destruct Hs as [<-|Hs]; [exact Hub|apply Hheld in Hs; tauto]. }
 assert(Hbt:observe t=b).
 { destruct Ht as [<-|Ht]; [exact Hub|apply Hheld in Ht; tauto]. }
 auto.
Qed.

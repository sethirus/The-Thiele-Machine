(** NecSChain.v: "A raised flag was checked, then committed, then
    certified" needs each of the three conjuncts of a clean start.

    A trace that splits as pre1, CHECK, mid1, COMMIT, mid2, CERTIFY, post
    costs at least 3. Each of the three partly clean starts of NecSClean.v
    certifies with a trace of cost 0, 1 or 2, so no such split exists for
    it: the earned chain fails without the flag down, without the empty
    channel, and without the empty table.                                 *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.
Require Import Minimal.EarnedCore.
From Minimal Require Import NecSClean.

Lemma nec_s_chain_costs_three : forall tr pre1 p c mid1 mid2 post,
  tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post ->
  total_cost tr >= 3.
Proof.
  intros tr pre1 p c mid1 mid2 post ->.
  rewrite total_cost_app. simpl. rewrite total_cost_app. simpl.
  rewrite total_cost_app. simpl. lia.
Qed.

Definition nec_s_has_chain (tr : list instr) : Prop :=
  exists pre1 p c mid1 mid2 post,
    tr = pre1 ++ CHECK p c :: mid1 ++ COMMIT p c :: mid2 ++ CERTIFY :: post.

Theorem nec_s_cert_provenance_needs_clean :
  (cert (run [] nec_s_flag_up) = true /\ ~ nec_s_has_chain []) /\
  (cert (run [CERTIFY] nec_s_chan_set) = true /\ ~ nec_s_has_chain [CERTIFY]) /\
  (cert (run [COMMIT PZero CA; CERTIFY] nec_s_fact_set) = true /\
   ~ nec_s_has_chain [COMMIT PZero CA; CERTIFY]).
Proof.
  destruct nec_s_clean_conjuncts_each_buy_one as [[_ [_ [H1 _]]] [[_ [_ [H2 _]]] [_ [_ [H3 _]]]]].
  split; [split; [exact H1 |] | split; [split; [exact H2 |] | split; [exact H3 |]]];
    intros (pre1 & p & c & mid1 & mid2 & post & E);
    pose proof (nec_s_chain_costs_three _ _ _ _ _ _ _ E) as Hc; simpl in Hc; lia.
Qed.

Print Assumptions nec_s_chain_costs_three.
Print Assumptions nec_s_cert_provenance_needs_clean.

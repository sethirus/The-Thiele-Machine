(** MorphTensorGap.v: the kernel's tensor product never succeeds on a graph
    reconstructed from a hardware snapshot. Every reconstructed module region
    is a prefix [seq 0 (S n)], so any two regions share address 0 and fail the
    disjointness test of [graph_tensor_morphisms]. *)
From Coq Require Import List Arith Lia String.
Import ListNotations.
Require Import Kernel.VMState.
From KamiHW Require Import Abstraction.
Local Open Scope nat_scope.

Definition prefix_region (m : ModuleState) : Prop :=
  exists n, module_region m = seq 0 (S n).

Lemma lookup_modules_prefix : forall l mid m,
  Forall (fun p => prefix_region (snd p)) l ->
  graph_lookup_modules l mid = Some m -> prefix_region m.
Proof.
  induction l as [|[id m'] l IH]; intros mid m HF H; cbn in H; [discriminate|].
  inversion HF as [|? ? Hh Ht]; subst.
  destruct (Nat.eqb id mid); [inversion H; subst; exact Hh|].
  exact (IH mid m Ht H).
Qed.

Lemma filtermap_prefix : forall (sizes : nat -> nat) l,
  Forall (fun p => prefix_region (snd p))
    (filtermap (fun i => if Nat.eqb (sizes i) 0 then None
       else Some (i, {| module_region := seq 0 (sizes i);
                        module_axioms := [];
                        module_mu_tensor := module_mu_tensor_default |})) l).
Proof.
  intros sizes l. induction l as [|i l IH]; cbn [filtermap]; [constructor|].
  destruct (Nat.eqb (sizes i) 0) eqn:E; [exact IH|].
  constructor; [|exact IH].
  cbn [snd module_region]. exists (pred (sizes i)). apply Nat.eqb_neq in E. rewrite Nat.succ_pred by exact E. reflexivity.
Qed.

Lemma snap_full_graph_prefix : forall s mid m,
  graph_lookup (snap_full_graph s) mid = Some m -> prefix_region m.
Proof.
  intros s mid m H. unfold graph_lookup, snap_full_graph in H. cbn [pg_modules] in H.
  eapply lookup_modules_prefix; [|exact H].
  apply Forall_map.
  unfold snap_pt_to_graph. cbn [pg_modules].
  eapply Forall_impl; [|exact (filtermap_prefix (snap_pt_sizes s) (rev (seq 0 (snap_pt_next_id s))))].
  intros [id m'] Hm. exact Hm.
Qed.

(** Two modules of a reconstructed graph always share address 0, so the
    kernel's tensor product never succeeds on a snapshot graph. *)
Theorem snap_graph_tensor_none : forall s f g,
  graph_tensor_morphisms (snap_full_graph s) f g = None.
Proof.
  intros s f g. unfold graph_tensor_morphisms.
  destruct (graph_lookup_morphism _ f) as [mf|]; [|reflexivity].
  destruct (graph_lookup_morphism _ g) as [mg|]; [|reflexivity].
  destruct (graph_lookup _ (morph_source mf)) as [a|] eqn:Ea; [|reflexivity].
  destruct (graph_lookup _ (morph_target mf)) as [bm|] eqn:Eb; [|reflexivity].
  destruct (graph_lookup _ (morph_source mg)) as [c|] eqn:Ec; [|reflexivity].
  destruct (graph_lookup _ (morph_target mg)) as [d|] eqn:Ed; [|reflexivity].
  destruct (snap_full_graph_prefix s _ _ Ea) as [na Ha].
  destruct (snap_full_graph_prefix s _ _ Ec) as [nc Hc].
  rewrite Ha, Hc. reflexivity.
Qed.

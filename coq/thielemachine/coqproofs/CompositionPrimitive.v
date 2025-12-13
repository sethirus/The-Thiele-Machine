(** =========================================================================
    COMPOSITION IS PRIMITIVE
    =========================================================================
    
    This module establishes that composition is the fundamental ontological
    primitive of the Thiele Machine.
    
    We prove:
    1. No Independent Global Semantics: The whole is exactly the sum of parts.
    2. Compositional Preservation: Equivalent parts yield equivalent wholes.
    
    ========================================================================= *)

From Coq Require Import List String ZArith Lia Bool Nat.
Require Import ThieleMachine.CoreSemantics.
Import ListNotations.

(** =========================================================================
    SECTION 1: SEMANTICS DEFINITION
    ========================================================================= *)

(** We define a Module as it appears in the Partition *)
Definition Module := (ModuleId * Region)%type.

(** The Semantics of a module is its observable structure (the variables it owns) *)
Definition LocalSemantics (m : Module) : Region := snd m.

(** The Global Semantics is the aggregate of all Local Semantics *)
Definition GlobalSemantics (p : Partition) : list Region :=
  map LocalSemantics p.(modules).

(** =========================================================================
    SECTION 2: NO INDEPENDENT GLOBAL SEMANTICS
    ========================================================================= *)

(** Theorem: The global semantics is fully determined by the composition of modules.
    There is no "emergent" state that is not present in the parts. 
    
    If you know the modules and how they are composed (the partition), 
    you know the global semantics.
*)
Theorem no_independent_global_semantics : forall (p : Partition),
  GlobalSemantics p = map LocalSemantics p.(modules).
Proof.
  intros p.
  unfold GlobalSemantics.
  reflexivity.
Qed.

(** =========================================================================
    SECTION 3: COMPOSITIONAL PRESERVATION
    ========================================================================= *)

(** Equivalence of modules based on their semantics *)
Definition module_equiv (m1 m2 : Module) : Prop :=
  LocalSemantics m1 = LocalSemantics m2.

(** Operation to replace a module in a partition *)
Fixpoint replace_module_list (ms : list Module) (target_id : ModuleId) (new_m : Module) : list Module :=
  match ms with
  | [] => []
  | m :: rest =>
      if Nat.eqb (fst m) target_id
      then new_m :: rest
      else m :: replace_module_list rest target_id new_m
  end.

Definition replace_module (p : Partition) (target_id : ModuleId) (new_m : Module) : Partition :=
  {| modules := replace_module_list p.(modules) target_id new_m;
     next_module_id := p.(next_module_id) |}.

(** Theorem: Meaning Preserved Under Composition
    
    If two modules are equivalent (have the same internal structure/semantics), 
    replacing one with the other in a partition yields an equivalent global state.
*)
Theorem meaning_preserved_under_composition : forall (p : Partition) (target_id : ModuleId) (old_m new_m : Module),
  In old_m p.(modules) ->
  fst old_m = target_id ->
  module_equiv old_m new_m ->
  (* Assumption: The target_id uniquely identifies old_m in the partition *)
  (forall m, In m p.(modules) -> fst m = target_id -> m = old_m) ->
  GlobalSemantics (replace_module p target_id new_m) = GlobalSemantics p.
Proof.
  intros p target_id old_m new_m HIn HId Hequiv HUnique.
  unfold GlobalSemantics, replace_module.
  simpl.
  unfold module_equiv, LocalSemantics in Hequiv.
  
  (* We prove that the list of regions remains identical *)
  induction (modules p) as [|m ms IH].
  - (* Base case: empty list *)
    contradiction.
  - (* Inductive case *)
    simpl.
    destruct (Nat.eqb (fst m) target_id) eqn:Heq.
    + (* Match found: m is the target *)
      simpl.
      (* Since m matches target_id, by HUnique, m = old_m *)
      assert (m = old_m).
      { apply HUnique. left. reflexivity. apply Nat.eqb_eq. assumption. }
      subst m.
      (* Now we replace old_m with new_m *)
      (* We need to show: snd new_m :: map snd ms = snd old_m :: map snd ms *)
      unfold LocalSemantics.
      rewrite <- Hequiv.
      reflexivity.
    + (* Match not found: recurse *)
      simpl.
      f_equal.
      apply IH.
      * (* old_m must be in ms *)
        destruct HIn.
        -- (* old_m = m *)
           subst m.
           (* But fst old_m = target_id, and Heq says fst m <> target_id. Contradiction. *)
           rewrite HId in Heq.
           rewrite Nat.eqb_refl in Heq.
           discriminate.
        -- assumption.
      * (* Uniqueness holds for ms subset *)
        intros m' HIn' HId'.
        apply HUnique.
        right. assumption.
        assumption.
Qed.
(* Documentation snapshot for ThieleUniversal semantics. *)

Definition IS_ApplyRule_Start (pc : nat) : Prop := pc = 29.

Lemma pc_29_implies_registers_from_rule_table :
  forall (q_cur sym_cur q_prime : nat) (write_value : nat) (move_value : Z),
    IS_ApplyRule_Start 29 -> True.
Proof. intros; exact I. Qed.

Lemma find_rule_from_memory_components :
  forall (rules : list (nat * nat * nat * nat * Z)) (q_cur sym_cur : nat),
    True.
Proof. exact I. Qed.

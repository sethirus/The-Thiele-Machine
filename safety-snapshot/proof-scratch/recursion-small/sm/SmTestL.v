From Undecidability.L Require Import Tactics.LTactics Datatypes.LNat Datatypes.LOptions Datatypes.LProd Datatypes.Lists Datatypes.LBool.
From Undecidability.L.Tactics Require Import GenEncode.
Inductive ti : Type := TI (r : nat) | TD (r j : nat) | TH.
MetaCoq Run (tmGenEncode "enc_ti" ti).
#[export] Hint Resolve enc_ti_correct : Lrewrite.
Instance term_TI : computable TI. Proof. extract constructor. Qed.
Instance term_TD : computable TD. Proof. extract constructor. Qed.
Fixpoint dbl (n : nat) : nat := match n with 0 => 0 | S k => S (S (dbl k)) end.
Instance term_dbl : computable dbl. Proof. extract. Qed.
Definition f (i : ti) (x : nat) : nat := match i with TI r => r + x | TD r j => dbl j | TH => x end.
Instance term_f : computable f. Proof. extract. Qed.

Add LoadPath "." as Top.
Require Import Top.thielemachine.coqproofs.GoldenVectors.
Require Import Top.thielemachine.coqproofs.Hash256.

(* Force computation and print *)
Eval compute in golden1_encoding.
Eval compute in Hash256.fold_mix golden1_encoding 0.

Eval compute in golden2_encoding.
Eval compute in Hash256.fold_mix golden2_encoding 0.

Eval compute in golden3_encoding.
Eval compute in Hash256.fold_mix golden3_encoding 0.

Eval compute in golden4_encoding.
Eval compute in Hash256.fold_mix golden4_encoding 0.

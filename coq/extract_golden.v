Require Import thielemachine.coqproofs.GoldenVectors.
Require Import thielemachine.coqproofs.Hash256.

(* Compute encodings *)
Compute ("GOLDEN1_ENCODING", golden1_encoding).
Compute ("GOLDEN1_HASH_INT", Hash256.fold_mix golden1_encoding 0).

Compute ("GOLDEN2_ENCODING", golden2_encoding).
Compute ("GOLDEN2_HASH_INT", Hash256.fold_mix golden2_encoding 0).

Compute ("GOLDEN3_ENCODING", golden3_encoding).
Compute ("GOLDEN3_HASH_INT", Hash256.fold_mix golden3_encoding 0).

Compute ("GOLDEN4_ENCODING", golden4_encoding).
Compute ("GOLDEN4_HASH_INT", Hash256.fold_mix golden4_encoding 0).

p='UniversalPLayout.v'
s=open(p,encoding='utf-8').read()
def rep(old,new,cnt=1):
    global s
    assert s.count(old)>=1, old
    s=s.replace(old,new) if cnt==0 else s.replace(old,new,cnt)
rep("Definition pu_HEAD_len : nat := pu_FETCH_len + 1 + UNPACK_len + 3 * 6 + JMP_len.",
    "Definition pu_HEAD_len : nat := pu_FETCH_len + 1 + UNPACK_len + 3 * 7 + JMP_len.")
rep("Definition pu_CERTH_len : nat := 2 + JMP_len.",
    "Definition pu_CERTH_len : nat := 2 + JMP_len.\nDefinition pu_PAYH_len : nat := 2 + JMP_len.")
rep("Definition pu_U_len : nat := pu_L_CERT + pu_CERTH_len - 1.",
    "Definition pu_L_PAY : nat := pu_L_CERT + pu_CERTH_len.\nDefinition pu_U_len : nat := pu_L_PAY + pu_PAYH_len - 1.")
rep("  | E.CHECK _ _ => 3 | E.COMMIT _ _ => 4 | E.CERTIFY => 5",
    "  | E.CHECK _ _ => 3 | E.COMMIT _ _ => 4 | E.CERTIFY => 5 | E.PAY => 6")
rep("  | E.CERTIFY => 0\n", "  | E.CERTIFY => 0\n  | E.PAY => 0\n")
rep("Definition pu_handlers : list nat := [pu_L_INC; pu_L_DEC; pu_L_HALT; pu_L_CHECK; pu_L_COMMIT; pu_L_CERT].",
    "Definition pu_handlers : list nat :=\n  [pu_L_INC; pu_L_DEC; pu_L_HALT; pu_L_CHECK; pu_L_COMMIT; pu_L_CERT; pu_L_PAY].")
rep("  pu_hJMP pu_T4 pu_L_HALT (3 * 6 + 1 + pu_FETCH_len + UNPACK_len + o).",
    "  pu_hJMP pu_T4 pu_L_HALT (3 * 7 + 1 + pu_FETCH_len + UNPACK_len + o).")
i=s.index("Definition pu_hCERTH (o : nat) : list hinstr :=")
j=s.index("\n\n",i)
s=s[:j]+"""

(* PAY: pay 1, INC GPC, back to HEAD. *)
Definition pu_hPAYH (o : nat) : list hinstr :=
  pu_hPAY o ++ pu_hINC pu_GPC (1 + o) ++ pu_hJMP pu_T4 pu_L_HEAD (2 + o)."""+s[j:]
rep("Lemma pu_hCERTH_length : forall o, length (pu_hCERTH o) = pu_CERTH_len.\nProof. reflexivity. Qed.",
    "Lemma pu_hCERTH_length : forall o, length (pu_hCERTH o) = pu_CERTH_len.\nProof. reflexivity. Qed.\nLemma pu_hPAYH_length : forall o, length (pu_hPAYH o) = pu_PAYH_len.\nProof. reflexivity. Qed.")
rep(r"""  pu_L_DEC = 221 /\ pu_L_DECH E.CA = 249 /\ pu_L_DECH E.CB = 309 /\ pu_L_CHECK = 369 /\
  pu_L_CKH E.CA = 397 /\ pu_L_CKH E.CB = 1419 /\ pu_L_COMMIT = 2441 /\ pu_L_CMH E.CA = 2469 /\
  pu_L_CMH E.CB = 3097 /\ pu_L_CERT = 3725 /\ pu_L_STOP = 108 /\ pu_U_len = 3728.""",
r"""  pu_L_DEC = 224 /\ pu_L_DECH E.CA = 252 /\ pu_L_DECH E.CB = 312 /\ pu_L_CHECK = 372 /\
  pu_L_CKH E.CA = 400 /\ pu_L_CKH E.CB = 1422 /\ pu_L_COMMIT = 2444 /\ pu_L_CMH E.CA = 2472 /\
  pu_L_CMH E.CB = 3100 /\ pu_L_CERT = 3728 /\ pu_L_PAY = 3732 /\ pu_L_STOP = 111 /\
  pu_U_len = 3735.""")
rep("pu_L_HEAD = 1 /\ pu_L_HALT = 98 /\ pu_L_INC = 109 /\ pu_L_INCH E.CA = 117 /\ pu_L_INCH E.CB = 169 /\\",
    "pu_L_HEAD = 1 /\ pu_L_HALT = 101 /\ pu_L_INC = 112 /\ pu_L_INCH E.CA = 120 /\ pu_L_INCH E.CB = 172 /\\")
rep(r"  pu_HEAD_len = 97 /\ pu_HALTB_len","  pu_HEAD_len = 100 /\ pu_HALTB_len")
rep(r"pu_CERTH_len = 4 /\ pu_EQR_len","pu_CERTH_len = 4 /\ pu_PAYH_len = 4 /\ pu_EQR_len")
rep("    pu_hCERTH pu_L_CERT ].","    pu_hCERTH pu_L_CERT;\n    pu_hPAYH pu_L_PAY ].")
i=s.index("Lemma pu_U_CERTH : subcode (pu_L_CERT, pu_hCERTH pu_L_CERT) (1, U_P).")
j=s.index("Qed.",i)+4
s=s[:j]+"\nLemma pu_U_PAYH : subcode (pu_L_PAY, pu_hPAYH pu_L_PAY) (1, U_P).\nProof. pu_place 15. Qed."+s[j:]
rep("pu_cm_paid E.CA ++ pu_cm_paid E.CB ++ [(pu_L_CERT, M.CERTIFY)].",
    "pu_cm_paid E.CA ++ pu_cm_paid E.CB ++\n  [(pu_L_CERT, M.CERTIFY); (pu_L_PAY, M.PAY)].")
rep("Lemma pu_paid_sites_length : length pu_paid_sites = 69.","Lemma pu_paid_sites_length : length pu_paid_sites = 70.")
rep("  | M.HALT | M.CERTIFY => None","  | M.HALT | M.CERTIFY | M.PAY => None")
rep("  intros [d | d j | | p d | p d |] r; simpl;","  intros [d | d j | | p d | p d | |] r; simpl;")
rep("Print Assumptions pu_U_CERTH.","Print Assumptions pu_U_CERTH.\nPrint Assumptions pu_U_PAYH.")
open(p,'w',encoding='utf-8',newline='\n').write(s)

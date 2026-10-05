p='UniversalPRun.v'
s=open(p,encoding='utf-8').read()
def rep(old,new):
    global s
    assert old in s, old
    s=s.replace(old,new,1)
rep(r'''Definition pu_host_kind (i : hinstr) : TC.kind (pu_hprop * nat) :=
  match i with
  | M.CHECK p r => TC.KCheck (p, r)
  | M.COMMIT p r => TC.KCommit (p, r)
  | M.CERTIFY => TC.KCertify
  | _ => TC.KBase
  end.

Definition pu_host_interface : TC.thiele_interface pu_host_machine :=
  TC.mk_ti pu_host_machine pu_host_base (pu_hprop * nat) pu_host_kind
    (fun pr s => pu_hholds (fst pr) (hv s (snd pr)))
    (fun s pr => M.check_ok pu_heval (M.core_of s) (fst pr) (snd pr))
    (fun pr s t => hver s (snd pr) = hver t (snd pr) /\ hv s (snd pr) = hv t (snd pr))
    M.clean_start (@M.mu pu_hprop).''',
r'''(* Claims: Some (p, r) is "p holds of register r"; None is the empty
   claim of PAY, which means nothing, is never checked true, and is kept
   by every change. PAY reads as a check of the empty claim, as in
   PricedComplete.v: it costs 1 like a record move, and it can never start
   an earned chain. *)
Definition pu_host_kind (i : hinstr) : TC.kind (option (pu_hprop * nat)) :=
  match i with
  | M.CHECK p r => TC.KCheck (Some (p, r))
  | M.COMMIT p r => TC.KCommit (Some (p, r))
  | M.CERTIFY => TC.KCertify
  | M.PAY => TC.KCheck None
  | _ => TC.KBase
  end.

Definition pu_host_meaning (c : option (pu_hprop * nat)) (s : hstate) : Prop :=
  match c with Some pr => pu_hholds (fst pr) (hv s (snd pr)) | None => False end.

Definition pu_host_check (s : hstate) (c : option (pu_hprop * nat)) : bool :=
  match c with
  | Some pr => M.check_ok pu_heval (M.core_of s) (fst pr) (snd pr)
  | None => false
  end.

Definition pu_host_same (c : option (pu_hprop * nat)) (s t : hstate) : Prop :=
  match c with
  | Some pr => hver s (snd pr) = hver t (snd pr) /\ hv s (snd pr) = hv t (snd pr)
  | None => True
  end.

Definition pu_host_interface : TC.thiele_interface pu_host_machine :=
  TC.mk_ti pu_host_machine pu_host_base (option (pu_hprop * nat)) pu_host_kind
    pu_host_meaning pu_host_check pu_host_same M.clean_start (@M.mu pu_hprop).''')
rep(r'''  exists pre1, (p, c), (M.CHECK p c), mid1, (M.COMMIT p c), mid2, M.CERTIFY, post.''',
    r'''  exists pre1, (Some (p, c)), (M.CHECK p c), mid1, (M.COMMIT p c), mid2, M.CERTIFY, post.''')
rep(r'''      * intros s [p r] H. simpl in *. unfold M.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply pu_heval_iff, H.
      * intros [p r] s t [_ Hsame] H. simpl in *. rewrite <- Hsame. exact H.''',
r'''      * intros s [[p r] |] H; simpl in *; [| discriminate H]. unfold M.check_ok in H.
        apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [_ H].
        apply pu_heval_iff, H.
      * intros [[p r] |] s t Hs H; simpl in *; [| contradiction H].
        destruct Hs as [_ Hsame]. rewrite <- Hsame. exact H.''')
rep(r'''  - exists (PSlot, 0), (M.CHECK PSlot 0), (M.COMMIT PSlot 0), M.CERTIFY.''',
    r'''  - exists (Some (PSlot, 0)), (M.CHECK PSlot 0), (M.COMMIT PSlot 0), M.CERTIFY.''')
open(p,'w',encoding='utf-8',newline='\n').write(s)


(* PAY: one paid step that moves to the next address and changes nothing
   else. It never traps on a live machine. *)
Definition pu_hPAY (o : nat) : list hinstr := [M.PAY].

Lemma pu_hPAY_step : forall o Ph s,
  subcode (o, pu_hPAY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = hexec s M.PAY /\ htrace 1 Ph s = [M.PAY].
Proof.
  intros o Ph s Hsc Hpc He. split.
  - apply (pu_host_step_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
  - apply (pu_host_trace_at pu_hprop_eqb pu_heval Ph s o); auto. discriminate.
Qed.

Theorem pu_hPAY_pass : forall o Ph s,
  subcode (o, pu_hPAY o) (1, Ph) -> hpc s = o -> herr s = false ->
  hrun_prog 1 Ph s = M.mkst (M.goto (M.core_of s) (S o)) (M.mu s + 1) (M.cert s).
Proof.
  intros o Ph s Hsc Hpc He.
  destruct (pu_hPAY_step o Ph s Hsc Hpc He) as [E _]. rewrite E.
  rewrite (M.pu_multi_exec_pay pu_hprop_eqb pu_heval s He), Hpc. reflexivity.
Qed.

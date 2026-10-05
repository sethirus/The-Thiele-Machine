p='UniversalPSim.v'
s=open(p,encoding='utf-8').read()
pay=r'''(* PAY: the guest and the host each pay 1 and move on; nothing else moves. *)
Lemma pu_ustep_pay : E.fetch P (E.pc k) = Some E.PAY -> pu_step_result P sg g h.
Proof.
  intros Hf. pose proof (pu_rw_err _ _ _ _ _ R) as He.
  assert (Hs : E.step P g = E.mkst (E.goto k (S (E.pc k))) (E.mu g + 1) (E.cert g)).
  { rewrite (pu_gstep_exec P g E.PAY He Hf) by discriminate.
    rewrite pu_gexec_noerr by exact He. unfold E.cexec. rewrite He. simpl.
    rewrite orb_false_r. reflexivity. }
  rewrite <- pu_R_fetch in Hf.
  pose proof (pu_rw_head _ _ _ _ _ R) as AH0.
  destruct (pu_phase_pay P h AH0 Hf)
    as [h' [Hr [AH [Hgpc [HF [HC [HM [HR [Hoth Hver]]]]]]]]].
  apply pu_hreach_step in Hr.
  2:{ intro E. rewrite E in HM. lia. }
  destruct Hr as [n Hn]. exists n, h'. split; [exact Hn |]. left.
  exists sg, rho. split; [| intros r' Hin'; left; exact Hin'].
  rewrite Hs. apply pu_rel_keep; simpl.
  + exact AH.
  + exact He.
  + exact Hoth.
  + exact Hver.
  + intro d. apply pu_gkeep_goto.
  + rewrite Hgpc, (pu_rw_gpc _ _ _ _ _ R). reflexivity.
  + reflexivity.
  + exact HF.
  + exact (pu_rw_gchan _ _ _ _ _ R).
  + rewrite HC. exact (pu_rw_hchan _ _ _ _ _ R).
  + exact (pu_rw_rho _ _ _ _ _ R).
  + rewrite HM, (pu_rw_mu _ _ _ _ _ R). reflexivity.
  + rewrite HR. exact (pu_rw_cert _ _ _ _ _ R).
Qed.

End Step.'''
assert s.count('\nEnd Step.')==1
s=s.replace('\nEnd Step.','\n'+pay,1)
old='''  - destruct i as [c | c j | | p c | p c |].'''
assert old in s
s=s.replace(old,'''  - destruct i as [c | c j | | p c | p c | |].''')
old='''      exact (pu_ustep_certify P sg rho g h R Hf).
  - left.'''
assert old in s
s=s.replace(old,'''      exact (pu_ustep_certify P sg rho g h R Hf).
    + right. split; [apply (pu_gnot_halted P g E.PAY); auto; discriminate |].
      exact (pu_ustep_pay P sg rho g h R Hf).
  - left.''')
s=s.replace('Print Assumptions pu_ustep_certify.','Print Assumptions pu_ustep_certify.\nPrint Assumptions pu_ustep_pay.')
open(p,'w',encoding='utf-8',newline='\n').write(s)

import re
files=['Bridge','Blocks','Layout','Phases','Sim','Run']
scope_new=r'''(* SCOPE NOTE: foundation connectivity gap suppressed, on purpose: this
   file is one step of the universal interpreter U_P of UniversalPRun.v and
   imports only the Coq standard library, the vendored coq-undecidability
   library and files under minimal/. Its link to the abstract record (the
   host machine meeting thiele_complete of ThieleComplete.v, and every
   computably presented machine run on U_P) lives in UniversalPRun.v and
   PresentedUniversal.v. *)'''
for f in files:
    p='UniversalP%s.v'%f
    s=open(p,encoding='utf-8').read()
    i=s.index('(* SCOPE NOTE')
    j=s.index('*)',i)+2
    head=s[:i]; rest=s[j:]
    # file name in the first line
    head=head.replace('(** Universal%s.v:'%f,'(** UniversalP%s.v:'%f,1)
    for g in ['Codes','Bridge','Blocks','Layout','Phases','Sim','Run']:
        head=head.replace('Universal%s.v'%g,'UniversalP%s.v'%g)
    head=head.replace('EarnedCore.v, EarnedGeneric.v, EarnedMulti.v,','EarnedGeneric.v, EarnedPriced.v, EarnedMultiPriced.v, CompilerChecker.v,')
    head=head.replace('EarnedCore.v, EarnedGeneric.v,\n    EarnedMulti.v,','EarnedGeneric.v, EarnedPriced.v,\n    EarnedMultiPriced.v, CompilerChecker.v,')
    head=head.replace('EarnedMulti.v','EarnedMultiPriced.v')
    head=head.replace('EarnedMultiPricedPriced','EarnedMultiPriced')
    note=('\n    This file is the priced counterpart of Universal%s.v: the host is the\n'
          '    machine of EarnedMultiPriced.v (with PAY), the guest is the priced\n'
          '    machine of EarnedPriced.v over the universal property language\n'
          '    cg_uprop (UniversalPCodes.v), every name carries the prefix pu_, and\n'
          '    the host program is U_P.\n' % f)
    k=head.index('\n\n')
    head=head[:k]+'\n'+note+head[k:]
    s=head+scope_new+rest
    open(p,'w',encoding='utf-8',newline='\n').write(s)

def rep(p,old,new):
    s=open(p,encoding='utf-8').read()
    assert old in s, (p,old)
    s=s.replace(old,new,1)
    open(p,'w',encoding='utf-8',newline='\n').write(s)

rep('UniversalPLayout.v','''      pu_L_CERT               CERTIFY, INC pu_GPC, back to pu_L_HEAD
''','''      pu_L_CERT               CERTIFY, INC pu_GPC, back to pu_L_HEAD
      pu_L_PAY                PAY, INC pu_GPC, back to pu_L_HEAD

    The opcode dispatch of pu_L_HEAD is 7-way: INC, DEC, HALT, CHECK,
    COMMIT, CERTIFY and PAY.
''')
rep('UniversalPLayout.v','CERTIFY sites, 69 of them)','CERTIFY sites and the one PAY site, 70 of them)')
rep('UniversalPPhases.v','''    The host ledger goes up by exactly 1 in the CHECK, COMMIT and CERTIFY
    phases (one paid instruction each, pass or fail) and by 0 in every
    other phase.''','''    The host ledger goes up by exactly 1 in the CHECK, COMMIT, CERTIFY and
    PAY phases (one paid instruction each, pass or fail) and by 0 in every
    other phase.''')
rep('UniversalPPhases.v','''      pu_phase_certify_fail  CERTIFY with an empty channel: the host traps
''','''      pu_phase_certify_fail  CERTIFY with an empty channel: the host traps
      pu_phase_pay           PAY: the host pays 1 at its own PAY, GPC goes up
                          by 1, nothing else moves
''')
rep('UniversalPSim.v','program of the small machine, one guest step at a time.','program of the priced machine over cg_uprop, one guest step at a time.')
rep('UniversalPSim.v','''                    records are current in the guest's next state
''','''                    records are current in the guest's next state; a
                    guest PAY is matched by the host's own PAY
''')
rep('UniversalPRun.v','For every guest program P of the small machine','For every priced guest program P over cg_uprop')
rep('UniversalPRun.v','''      pu_universal_thiele_complete  the host machine (EarnedMultiPriced with the
                               property PSlot), read with its INC/DEC moves as
                               the base and CHECK, COMMIT, CERTIFY as the
                               record moves, meets thiele_complete of
                               ThieleComplete.v''','''      pu_universal_thiele_complete  the host machine (EarnedMultiPriced with the
                               property PSlot), read with its INC/DEC moves as
                               the base, CHECK, COMMIT, CERTIFY as the record
                               moves and PAY as a check of the empty claim
                               (as in PricedComplete.v), meets
                               thiele_complete of ThieleComplete.v''')
rep('UniversalPBlocks.v','''      One-instruction lemmas for CHECK PSlot r, COMMIT PSlot r and CERTIFY:''','''      One-instruction lemmas for CHECK PSlot r, COMMIT PSlot r, CERTIFY and
      PAY (pu_hPAY, pu_hPAY_pass: pc + 1, ledger + 1, nothing else):''')

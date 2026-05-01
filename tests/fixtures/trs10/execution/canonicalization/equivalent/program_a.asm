FUEL 64
# canonicalization equivalence program A
start:
  INIT_PT 0 128
  INIT_ACTIVE_MODULE 0
  PNEW {0,128} 1
  LOAD_IMM r1 42 1
  MOV r2 r1
  ADD r3 r2 r1 1
  HALT 0

# all_opcodes_test.asm — exercises the Thiele Machine ISA on the
# synthesized RTL, which has 16 general-purpose registers and 128
# words of data memory.
#
# The Thiele Machine requires a partition before memory operations.
# Some opcodes also require the logic-accumulator guard (= 0xCAFEEACE).
# Expected result: halted=1, err=0, mu > 0
# Register verification (only registers r0..r15 are used):
#   r3  = 100  (ADD r1+r2 = 42+58)
#   r4  = 16   (SUB r2-r1)
#   r5  = 42   (XFER from r1)
#   r10 = 99   (LOAD from mem[0])
#   r8  = 88   (subroutine return value)
#   r12 = 42   (AND r1, r2)
#   r13 = 58   (OR  r1, r2)
#   r14 = 2    (SHL r6, r6)
#   r15 = 29   (SHR r2, r6)

FUEL 1000

# ---- Memory + state initialization (for cosim testbench) ----
INIT_MEM 0 99
INIT_MEM 1 200
INIT_PT 0 128                 # RTL: set ptTable[0] = 128 (mem region size)
INIT_ACTIVE_MODULE 0          # RTL: set active_module = 0
INIT_LOGIC_ACC 0xCAFEEACE     # RTL: enable PDISCOVER/CHSH_TRIAL/REVEAL guard

# ---- Partition setup (Coq/OCaml side) ----
PNEW {0,128} 1                # partition 0: covers mem[0..127]

# ---- Core compute opcodes ----
LOAD_IMM r1 42 1              # r1 = 42
LOAD_IMM r2 58 1              # r2 = 58
ADD r3 r1 r2 1                # r3 = r1 + r2 = 100
SUB r4 r2 r1 1                # r4 = r2 - r1 = 16
XFER r5 r1 1                  # r5 = r1 = 42

# ---- Memory opcodes (register-indirect addressing) ----
# Reuse r9 as a scratch address register (within RegCount=16).
LOAD_IMM r9 0 0               # r9 = address 0
LOAD r10 r9 1                 # r10 = mem[r9] = mem[0] = 99
LOAD_IMM r9 2 0               # r9 = address 2
STORE r9 r3 1                 # mem[r9] = mem[2] = r3 = 100

# ---- Heap opcodes (register-indirect addressing) ----
LOAD_IMM r9 1 0               # r9 = address 1
HEAP_STORE r9 r1 1            # heap[r9] = heap[1] = r1 = 42
LOAD_IMM r9 0 0               # r9 = address 0
HEAP_LOAD r11 r9 1            # r11 = heap[r9] = heap[0] = 99

# ---- Control flow ----
JUMP SKIP_NOP 0               # jump over the NOP
NOP                           # should be skipped
SKIP_NOP:
LOAD_IMM r6 1 1               # r6 = 1 (proves JUMP worked)
JNEZ r6 PAST_JNEZ 0           # r6 != 0, so jump
LOAD_IMM r7 255 0             # should be skipped
PAST_JNEZ:
LOAD_IMM r7 7 1               # r7 = 7 (proves JNEZ worked)

# ---- Subroutine ----
CALL SUBROUTINE 1             # call and return
JUMP AFTER_SUB 0
SUBROUTINE:
LOAD_IMM r8 88 1              # r8 = 88
RET 1
AFTER_SUB:

# ---- Bitwise and arithmetic opcodes ----
AND r12 r1 r2 1               # r12 = r1 & r2 = 42 & 58 = 42
OR  r13 r1 r2 1               # r13 = r1 | r2 = 42 | 58 = 58
SHL r14 r6 r6 1               # r14 = r6 << r6 = 1 << 1 = 2
SHR r15 r2 r6 1               # r15 = r2 >> r6 = 58 >> 1 = 29

# ---- XOR opcodes ----
XOR_LOAD r1 0 1               # load into XOR accumulator
XOR_ADD  r2 0 1               # XOR add
XOR_SWAP r1 r2 1              # XOR swap
XOR_RANK r1 0 1               # XOR rank (popcount)

# ---- Cost model ----
MDLACC 0 0 1                  # model accumulate

# ---- Certificate opcode ----
CERTIFY 0 0 1                 # set certification flag

# ---- I/O opcodes ----
READ_PORT  0 0 1              # read port (NOP in hardware)
WRITE_PORT 0 0 1              # write port (NOP in hardware)

# ---- Partition opcodes (require logic_acc = 0xCAFEEACE) ----
PNEW {0,10} 2                 # create another partition
PDISCOVER 0 0 1               # discover partition (needs logic-acc guard)

# ---- CHSH trial (requires logic_acc = 0xCAFEEACE) ----
CHSH_TRIAL 0 0 0 0 1          # classical trial: x=0, y=0, a=0, b=0

# ---- Checkpoint ----
CHECKPOINT 0 0 1              # checkpoint (NOP in hardware)

# ---- Information opcodes (can cause halt, placed last) ----
EMIT 0 0 1                    # emit (charges mu; may halt on info threshold)

# ---- Done ----
HALT 0

# stack_demo.asm
# Manual stack using STORE/LOAD with fixed literal addresses.
# The ISA uses direct (literal) addressing, so the stack is emulated via
# explicit memory locations.  Addresses 0-2 serve as 3-slot stack storage.
#
# Push order: r1=10, r2=20, r3=30 → addresses 0,1,2
# Pop  order (LIFO): read addr 2,1,0 → r10=30, r11=20, r12=10

LOAD_IMM r1 10 1
LOAD_IMM r2 20 1
LOAD_IMM r3 30 1

# Push (write in push order to sequential addresses)
STORE 0 r1 1        # stack[0] = 10
STORE 1 r2 1        # stack[1] = 20
STORE 2 r3 1        # stack[2] = 30

# Pop in LIFO order (read backwards)
LOAD r10 2 1        # r10 = 30
LOAD r11 1 1        # r11 = 20
LOAD r12 0 1        # r12 = 10

HALT 0

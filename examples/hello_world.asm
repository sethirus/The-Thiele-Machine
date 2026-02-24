# hello_world.asm
# Print "hello" via EMIT and halt.
# EMIT module_id=0 payload_byte=0 cost=1 (payload address field)
# Each EMIT charges mu by 1 and records the emission in the host.

LOAD_IMM r1 72 1    # r1 = 'H' (0x48)
EMIT 0 0 1          # emit module 0, cost 1
LOAD_IMM r1 101 1   # r1 = 'e'
EMIT 0 0 1
LOAD_IMM r1 108 1   # r1 = 'l'
EMIT 0 0 1
EMIT 0 0 1          # second 'l'
LOAD_IMM r1 111 1   # r1 = 'o'
EMIT 0 0 1
HALT 0

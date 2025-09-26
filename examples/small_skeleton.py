import hashlib

c1 = placeholder(domain=list('0123456789'))
c2 = placeholder(domain=list('0123456789'))

secret = c1 + c2

TARGET_HASH_PREFIX = "0"
h = hashlib.sha256(secret.encode('utf-8')).hexdigest()

assert h.startswith(TARGET_HASH_PREFIX)
# skeleton_key.py - Fully Realized Thiele Machine Demonstration
# 10-character symbolic solving with partition logic and composite witnesses

# Partition 1: First 5 characters (module 1)
c1 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c2 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c3 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c4 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c5 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))

# Partition 2: Last 5 characters (module 2)
c6 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c7 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c8 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c9 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))
c10 = placeholder(domain=list('abcdefghijklmnopqrstuvwxyz'))

# Construct the full secret from both partitions
secret = c1+c2+c3+c4+c5+c6+c7+c8+c9+c10

# Local constraints for each partition (module-level witnesses)
# Module 1: First 5 chars form "abcde"
module1_secret = c1+c2+c3+c4+c5
assert module1_secret == "abcde"

# Module 2: Last 5 chars form "fghij"
module2_secret = c6+c7+c8+c9+c10
assert module2_secret == "fghij"

# Composite witness: Global constraint combining both modules
assert secret == "abcdefghij"

print(f"Partitioned Skeleton Key Found: {secret}")
print(f"Module 1: {module1_secret}")
print(f"Module 2: {module2_secret}")
print("Composite witness verified!")
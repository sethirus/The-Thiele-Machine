
import math
n = 13727042326592415851
max_trial = int(math.sqrt(n)) + 1
for i in range(2, max_trial):
    if n % i == 0:
        p, q = i, n // i
        break
else:
    raise ValueError('No factors found')
print(f'Found factors: p={p}, q={q}')
# Return the factors as a tuple for VM to detect
(p, q)

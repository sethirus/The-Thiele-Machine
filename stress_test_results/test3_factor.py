
n = 15
for i in range(2, n):
    if n % i == 0:
        p = i
        q = n // i
        break
__result__ = (p, q)

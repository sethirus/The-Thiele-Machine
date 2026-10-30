"""Checks of the board claims in chapter thirteen of the book."""
fails = []
# bare board: STAMP takes NO->YES from anywhere and costs 1; CHECK never moves the coin
def run(prog, check_cost, guarded):
    box, tally, passed = 'NO', 0, False
    for op in prog:
        if op == 'CHECK': tally += check_cost; passed = True
        elif op == 'WORK': pass
        elif op == 'STAMP':
            tally += 1
            if not guarded or passed: box = 'YES'
    return box, tally
for cost in [0, 1, 2]:
    a = run(['STAMP'], cost, False); b = run(['CHECK', 'STAMP'], cost, False)
    if a[0] != b[0] or b[1] - a[1] != cost: fails.append(('bare', cost))
    # guarded board: stamp without check is refused, stamp after check succeeds
    if run(['STAMP'], cost, True)[0] != 'NO' or run(['CHECK', 'STAMP'], cost, True)[0] != 'YES':
        fails.append(('guarded', cost))
# the price of a raise doesn't depend on what YES shows: toll floor uses only the box before and after
print('failures:', len(fails))

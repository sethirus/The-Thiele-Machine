
import json
import math
series = [math.log(1 + i * 0.5) for i in range(1, 33)]
mean = sum(series) / len(series)
variance = sum((value - mean) ** 2 for value in series) / len(series)
vm_write_text('turbulence_stats.json', json.dumps({'mean': mean, 'variance': variance}, indent=2))
print('turbulence-mean', mean)

 
from basics import *
#from pysat.formula import IDPool, CNF

cnf = readcnf(argv[1])
proof = readproof(argv[2])

stats = {}
with open(argv[3],"w") as inccnf:
	inccnf.write("p inccnf\n")

	for c in cnf:
		inccnf.write(" ".join(str(x) for x in c)+" 0\n")

	for c in proof:
		l = len(c)
		if l == 2:
			inccnf.write("a "+" ".join(str(-x) for x in c)+" 0\n")

		if l not in stats: stats[l] = 0
		stats[l] += 1

print("stats",{i:stats[i] for i in sorted(stats)})

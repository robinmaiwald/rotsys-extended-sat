from basics import *
from ast import literal_eval

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("cnf",type=str,help="cnf input file")
parser.add_argument("proof",type=str,help="proof input file")
parser.add_argument("merge",type=str,help="merge output file")
parser.add_argument("--var",type=str,help="variables input file")
parser.add_argument("--debug","-d",type=int,default=0,help="debug level")

args = parser.parse_args()
print("args",args)


print(f"read cnf from {args.cnf}")
cnf = readcnf(args.cnf)

print(f"read proof from {args.proof}")
proof = readproof(args.proof)

if args.var:
	print(f"read variables from {args.var}")
	var = literal_eval(open(args.var).readline())
else:
	var = {}

def var_lookup(x):
	s = '+' if x > 0 else '-'
	a = abs(x)
	if a in var:
		return s+var[a]
	else:
		return s+'unnamed'+str(a)

print(f"write verification inccnf to {args.merge}")
print("for each clause a cube is created.")
print("cadical should return 'UNSAT' for all cubes (i.e. learned clauses are correct)")

stats = {}
with open(args.merge,"w") as inccnf:
	inccnf.write("p inccnf\n")

	for c in cnf:
		inccnf.write(" ".join(str(x) for x in c)+" 0\n")

	for c in proof:
		if args.debug >= 2: 
			c_text = [var_lookup(x) for x in c]
			print(f"learned clause: {c} {c_text}")

		l = len(c)
		if l == 2:
			inccnf.write("a "+" ".join(str(-x) for x in c)+" 0\n")


		if l not in stats: stats[l] = 0
		stats[l] += 1



if args.debug: 
	print("stats",{i:stats[i] for i in sorted(stats)})

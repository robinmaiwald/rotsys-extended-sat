from itertools import *
import random
from pysat.formula import IDPool

import argparse
parser = argparse.ArgumentParser()

parser.add_argument("n",type=int,help="number of points")

parser.add_argument("output", type=str,help="")
parser.add_argument("--depth","-d",type=int,default=None,help="depth of split")
parser.add_argument("--parts","-p", type=int, default=1, help="number of parts")

parser.add_argument("-cm","--cmonotone",action='store_true', help="assume circularly monotone")
parser.add_argument("-scm","--stronglycmonotone",action='store_true', help="assume strongly circularly monotone")

parser.add_argument("--shuffle", type=int, default=1, help="0=no shuffle, seed otherwise")
args = parser.parse_args()
print("args",args)



n = args.n
N = list(range(n))

N_without_last = list(range(n-1))
N_without = {i:list(range(i))+list(range(i+1,n)) for i in N}

if args.cmonotone or args.stronglycmonotone:
    # vertices 0 and 1 are used to ensure c-monotonicity
    all_vertices = list(range(n+2)) # use two auxiliary vertices for the encoding
else:
    all_vertices = N

all_vertices_without = {i:[j for j in all_vertices if j!=i] for i in all_vertices} 

vpool = IDPool()
        
var_a_sees_bcd_ = {}
def var_a_sees_bcd(*I): return var_a_sees_bcd_[I]
# b is the i-th vertex in cyclic order around vertex a
for a in all_vertices: # remark: using "all_vertices" instead of "N" because for cmonotone there are auxiliary vertices
    for b,c,d in combinations(all_vertices_without[a],3): 
        var_a_sees_bcd_[a,b,c,d] = var_a_sees_bcd_[a,c,d,b] = var_a_sees_bcd_[a,d,b,c] = vpool.id(f"S{a}{b}{c}{d}")
        var_a_sees_bcd_[a,b,d,c] = var_a_sees_bcd_[a,c,b,d] = var_a_sees_bcd_[a,d,c,b] = -var_a_sees_bcd_[a,b,c,d]
        


if 1:
	cubes = []
	for a in N[-1:]:
		others = N_without[a]
		if args.depth and len(others) > args.depth: 
			others = others[:args.depth]

		for pi in permutations(others):
			if pi[0] == others[0]:
				C = []
				for I in combinations(others,3):
					I_inv = [(x,y) for (x,y) in combinations(I,2) if pi.index(x)>pi.index(y)] # number of inversions in the triple I=(b,c,d)
					if len(I_inv)%2 == 0:
						C.append(+var_a_sees_bcd(a,*I))
					else:
						C.append(-var_a_sees_bcd(a,*I))	

				cubes.append(C)

print(f"computed {len(cubes)} cubes")


if args.shuffle:
	random.Random(args.shuffle).shuffle(cubes) # always use same seed

for p in range(args.parts):
	fp = args.output+("."+str(p+1) if args.parts > 1 else "")
	with open(fp,"w") as f:
		for C in cubes[p::args.parts]:
			f.write("a "+' '.join([str(x) for x in C])+" 0\n")

print(f"wrote to file {args.output}")

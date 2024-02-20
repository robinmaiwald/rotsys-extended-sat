


from pysat.formula import IDPool,CNF
from ast import *
import pycosat

from itertools import combinations, permutations
from ast import literal_eval
import datetime

import argparse
parser = argparse.ArgumentParser()
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")

parser.add_argument("-nat","--natural",action='store_false',help="remove assumption that first line needs not to be 2,3,...,n (enabled by default, use parameter to disable)")
parser.add_argument("-v4","--valid4tuples",action='store_false',help="remove assumption that 4-tuples are valid (enabled by default, use parameter to disable)")
parser.add_argument("-v5","--valid5tuples",action='store_false',help="remove assumption that 5-tuples are valid (enabled by default, use parameter to disable)")

parser.add_argument("-HC","--forbidHC",action='store_true', help="forbid plane Hamiltonian cycle")

parser.add_argument("-r2f","--rs2file", help="if specified, export rotation systems to this file")
parser.add_argument("-c2f","--cnf2file", help="if specified, export CNF to this file")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
parser.add_argument("--debug","-d",type=int,default=0,help="debug level")

args = parser.parse_args()
print("args",args)
 
time_start = datetime.datetime.now()

n = args.n
N = range(n)
N_without = {i:list(range(i))+list(range(i+1,n)) for i in N}
N_without_last = range(n-1)

vpool = IDPool()
constraints = []

# initialize variables
var_rotsys = {(a,i,b):vpool.id() for a in N for i in N_without_last for b in N_without[a]} 
var_a_sees_bcd = {(a,b,c,d):vpool.id() for a,b,c,d in permutations(N,4)} 
var_ab_cross_cd = {(a,b,c,d):vpool.id() for a,b,c,d in permutations(N,4)} 
var_ab_cross_cd_directed = {(a,b,c,d):vpool.id() for a,b,c,d in permutations(N,4)}


print ("(*) wlog: first column is 1,0,0,...,0")
constraints.append([var_rotsys[0,0,1]])
for a in N_without[0]:
    constraints.append([var_rotsys[a,0,0]])
        

if args.natural:
    print ("(*) wlog: first line is 1,2,3,4,...")
    for a in N_without_last:
        constraints.append([var_rotsys[0,a,a+1]])


print ("(*) assert permutations",len(constraints))
for a in N:
    for i in N_without_last:
        constraints.append([var_rotsys[a,i,b] for b in N_without[a]])
        for b1,b2 in combinations(N_without[a],2):
            constraints.append([-var_rotsys[a,i,b1],-var_rotsys[a,i,b2]])

    for b in N_without[a]:
        constraints.append([var_rotsys[a,i,b] for i in N_without_last])
        for i1,i2 in combinations(N_without_last,2):
            constraints.append([-var_rotsys[a,i1,b],-var_rotsys[a,i2,b]])


print ("(*) assert a_sees_bcd",len(constraints))
for a in N:
    for b,c,d in combinations(N_without[a],3):
        for x,y,z in permutations([b,c,d]):
            inversions = sum(+1 for u,v in combinations([x,y,z],2) if u>v)
            sign = (-1)**inversions
            constraints.append([-var_a_sees_bcd[a,b,c,d],+sign*var_a_sees_bcd[a,x,y,z]])
            constraints.append([+var_a_sees_bcd[a,b,c,d],-sign*var_a_sees_bcd[a,x,y,z]])


print ("(*) assert a_sees_bcd",len(constraints))
for a,b,c,d in permutations(N,4):
    for i,j,k in combinations(N_without_last,3):
        constraints.append([-var_rotsys[a,i,b],-var_rotsys[a,j,c],-var_rotsys[a,k,d],+var_a_sees_bcd[a,b,c,d]])


def forbid_subrs(subrs):
    k = len(subrs)
    constraints = []
    for I in permutations(N,k):
        for s in [+1,-1]: # forbid original and mirrored
            constraints.append([-s*var_a_sees_bcd[I[a],I[b],I[c],I[d]] for a in range(k) for b,c,d in combinations(subrs[a],3)])
    return constraints


if args.valid4tuples:
    print ("(*) assert valid 4-tuples",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3],[0,2,3],[0,1,3],[0,2,1]])

if args.valid5tuples:
    print ("(*) assert valid 5-tuples")
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,3,4],[0,3,1,4],[0,4,2,1],[0,3,1,2]]) # forbidden type I
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,4,3],[0,3,1,4],[0,4,2,1],[0,1,3,2]]) # forbidden type II

if 1:
	print ("(*) assert ab_cross_cd",len(constraints))
	for a,b,c,d in permutations(N,4):
	    constraints.append([
	        -var_a_sees_bcd[a,b,d,c],
	        -var_a_sees_bcd[b,a,c,d],
	        -var_a_sees_bcd[c,a,b,d],
	        -var_a_sees_bcd[d,a,c,b],+var_ab_cross_cd_directed[a,b,c,d]])
	    constraints.append([
	        +var_a_sees_bcd[a,b,d,c],-var_ab_cross_cd_directed[a,b,c,d]])
	    constraints.append([
	        +var_a_sees_bcd[b,a,c,d],-var_ab_cross_cd_directed[a,b,c,d]])
	    constraints.append([
	        +var_a_sees_bcd[c,a,b,d],-var_ab_cross_cd_directed[a,b,c,d]])
	    constraints.append([
	        +var_a_sees_bcd[d,a,c,b],-var_ab_cross_cd_directed[a,b,c,d]])

	    constraints.append([-var_ab_cross_cd_directed[a,b,c,d],+var_ab_cross_cd[a,b,c,d]])
	    constraints.append([-var_ab_cross_cd_directed[a,b,d,c],+var_ab_cross_cd[a,b,c,d]]) 
	    constraints.append([+var_ab_cross_cd_directed[a,b,c,d],+var_ab_cross_cd_directed[a,b,d,c],-var_ab_cross_cd[a,b,c,d]])




print ("Total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)
print ()


if args.cnf2file:
    print ("write cnf instance to file:",args.cnf2file)
    from pysat.formula import CNF
    cnf = CNF()
    for c in constraints: cnf.append(c)
    cnf.to_file(args.cnf2file)
    exit()


outfile = None
if args.rs2file:
    print ("write rotation systems to file:",args.rs2file)
    outfile = open(args.rs2file,"w")

ct = 0
found = []
fingerprints = []

if True:
    if args.solver == "cadical":
        print ("use pysat/Cadical")
        try:
            from pysat.solvers import Cadical153    
            solver = Cadical153()
        except ImportError:
            from pysat.solvers import Cadical # old pysat versions
            solver = Cadical()

        for c in constraints: solver.add_clause(c)
        solution_iterator = solver.enum_models()
    else:
        print ("use pycosat")
        import pycosat
        solution_iterator = pycosat.itersolve(constraints)


    print (datetime.datetime.now(),"start solving")
    for sol in solution_iterator:
        ct += 1
        sol = set(sol) # it's faster to lookup values in set than in list

        rs = []
        for a in N:
            order_a = []
            for i in N_without_last:
                for b in N_without[a]:
                    if var_rotsys[a,i,b] in sol:
                        order_a.append(b)

            rs.append(order_a)
        
        assert(rs not in found)        
        found.append(rs)
        if outfile: outfile.write(str(rs)+"\n")
        print (datetime.datetime.now(),"solution #",ct,"\t",rs)
        
        if not args.all: break





time_end = datetime.datetime.now()

if ct == 0:
    print (time_end,"no solution!?")
else:
    if args.all:
        print (time_end,"total count:",len(found))
    else:
        print("use parameter -a/--all to enumerate all solutions")


print("solving time :",time_end-time_before_solving)
print("total time   :",time_end-time_start)


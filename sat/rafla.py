


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
parser.add_argument("-HP","--forbidHP",action='store_true', help="forbid plane Hamiltonian path")

parser.add_argument("-or","--rs2file", help="if specified, export rotation systems to this file")
parser.add_argument("-oc","--cnf2file", help="if specified, export CNF to this file")
parser.add_argument("-ov","--var2file", help="if specified, export variables to this file")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")
parser.add_argument("--debug","-d",type=int,default=0,help="debug level")

parser.add_argument("--use_rs",action='store_true', help="use variables for encoding rotations system via permutations")

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
if args.use_rs: 
    var_rotsys = {(a,i,b):vpool.id(f"R{a}_{i}_{b}") for a in N for i in N_without_last for b in N_without[a]} 

var_a_sees_bcd = {}
for a in N:
    for b,c,d in combinations(N_without[a],3):
        var_a_sees_bcd[a,b,c,d] = var_a_sees_bcd[a,c,d,b] = var_a_sees_bcd[a,d,b,c] = vpool.id(f"S{a}_{b}_{c}_{d}")
        var_a_sees_bcd[a,b,d,c] = var_a_sees_bcd[a,c,b,d] = var_a_sees_bcd[a,d,c,b] = -var_a_sees_bcd[a,b,c,d]
        

#var_ab_cross_cd = {(a,b,c,d):vpool.id() for a,b,c,d in permutations(N,4)}

def cross(a,b,c,d):
    if a>b: return cross(b,a,c,d)
    if c>d: return cross(a,b,d,c)
    if a>c: return cross(c,d,a,b)
    return vpool.id(f"C{a}_{b}_{c}_{d}")


def dcross(a,b,c,d):
    a,b,c,d = min([(a,b,c,d),(c,d,b,a),(b,a,d,c),(d,c,a,b)])
    return vpool.id(f"D{a}_{b}_{c}_{d}")

var_ab_cross_cd = {(a,b,c,d):cross(a,b,c,d) for a,b,c,d in permutations(N,4)}
var_ab_cross_cd_directed = {(a,b,c,d):dcross(a,b,c,d) for a,b,c,d in permutations(N,4)}

var_plane_ab_I_path = {(I[0],I[-1],I[1:-1]): vpool.id() for k in range(3,n+1) for I in permutations(set(N),k)}

if 0:
    var_plane_0x_I_path_ordered = {(x,I): vpool.id() for x in set(N) - {0} #for k in range(2,n) 
                        for I in permutations(set(N)-{0,x},n//2-1)}

    var_plane_0x_I_path_unordered = {(x,I): vpool.id() for x in set(N) - {0} #for k in range(2,n) 
                        for I in combinations(set(N)-{0,x},n//2-1)}

# ensure both variables have the same value (logical XNOR)
def equality_clauses(a,b):
    return [[-a,+b],[+a,-b]]
    
# creates clauses to ensure exactly one of the given literals is true
def exactly_one_clauses(literals):
    return [literals]+[[-l1,-l2] for l1,l2 in combinations(literals,2)]
    
# creates clauses to ensure exactly one of the given literals is true
def at_most_one_clauses(literals):
    return [[-l1,-l2] for l1,l2 in combinations(literals,2)]
    
# if all if_literals are fulfilled, then all then_literals must be fulfilled
def if_then_clauses(if_literals,then_literals):
    return [[-i for i in if_literals]+[t] for t in then_literals]


# literal A is fulfilled if and only if at least one B are fulfilled 
def A_equals_disjunctionB_clauses(A_literal,B_literals):
    return [[-A_literal]+B_literals]+[[+A_literal,-b] for b in B_literals]

# literal A is fulfilled if and only if all B's are fulfilled 
def A_equals_conjunctionB_clauses(A_literal,B_literals):
    return [[-A_literal,+b] for b in B_literals]+[[+A_literal]+[-b for b in B_literals]]

if args.use_rs:
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
            constraints += exactly_one_clauses([var_rotsys[a,i,b] for b in N_without[a]])

        for b in N_without[a]:
            constraints += exactly_one_clauses([var_rotsys[a,i,b] for i in N_without_last])



 
    print ("(*) assert a_sees_bcd",len(constraints))
    for a in N:
        for b,c,d in combinations(N_without[a],3):
            for x,y,z in permutations([b,c,d]):
                inversions = sum(+1 for u,v in combinations([x,y,z],2) if u>v)
                sign = (-1)**inversions
                constraints += equality_clauses(+var_a_sees_bcd[a,b,c,d],+sign*var_a_sees_bcd[a,x,y,z])
                
    print ("(*) assert a_sees_bcd",len(constraints))
    for a,b,c,d in permutations(N,4):
        for i,j,k in combinations(N_without_last,3):
            constraints += if_then_clauses([+var_rotsys[a,i,b],+var_rotsys[a,j,c],+var_rotsys[a,k,d]],[+var_a_sees_bcd[a,b,c,d]])


if 0:
    print ("(*) assert a_sees_bcd",len(constraints))
    for x in N: # for every element we have a cyclic order which is encoded through forbidden patterns on 4-element subsets
        for a,b,c,d in combinations(N_without[x],4):
            #triples = list(J for J in combinations(I,3))
            for s1,s2,s3,s4 in [[+1,-1,+1,-1],[-1,+1,-1,+1],[+1,-1,-1,-1],[-1,+1,-1,-1],[-1,-1,+1,-1],[-1,-1,-1,+1],[-1,+1,+1,+1],[+1,-1,+1,+1],[+1,+1,-1,+1],[+1,+1,+1,-1]]:
                constraints.append([s1*var_a_sees_bcd[x,a,b,c],s2*var_a_sees_bcd[x,a,b,d],s3*var_a_sees_bcd[x,a,c,d],s4*var_a_sees_bcd[x,b,c,d]])
    

if 1:
    print ("(*) assert a_sees_bcd",len(constraints))
    for x in N: # for every element we have a cyclic order which is encoded through forbidden patterns on 4-element subsets
        for a,b,c,d in combinations(N_without[x],4):
            for s in [+1,-1]:
                constraints.append([+s*var_a_sees_bcd[x,a,b,c],-s*var_a_sees_bcd[x,a,b,d],+s*var_a_sees_bcd[x,a,c,d]]) # no 4=bcd
                constraints.append([+s*var_a_sees_bcd[x,a,b,d],-s*var_a_sees_bcd[x,a,c,d],+s*var_a_sees_bcd[x,b,c,d]]) # no 1=abc
                constraints.append([-s*var_a_sees_bcd[x,a,b,c],-s*var_a_sees_bcd[x,a,c,d],+s*var_a_sees_bcd[x,b,c,d]]) # no 2=abd
                constraints.append([+s*var_a_sees_bcd[x,a,b,c],-s*var_a_sees_bcd[x,a,b,d],-s*var_a_sees_bcd[x,b,c,d]]) # no 3=acd
            

if args.natural:
    for a,b,c in combinations(N_without[0],3):
        constraints.append([var_a_sees_bcd[0,a,b,c]])
    


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

        constraints += A_equals_conjunctionB_clauses(+var_ab_cross_cd_directed[a,b,c,d],[
            +var_a_sees_bcd[a,b,d,c],
            +var_a_sees_bcd[b,a,c,d],
            +var_a_sees_bcd[c,a,b,d],
            +var_a_sees_bcd[d,a,c,b]])

        constraints += A_equals_disjunctionB_clauses(+var_ab_cross_cd[a,b,c,d],[
            +var_ab_cross_cd_directed[a,b,c,d],
            +var_ab_cross_cd_directed[a,b,d,c]])
        
        constraints += at_most_one_clauses([+var_ab_cross_cd_directed[a,b,c,d],
            +var_ab_cross_cd_directed[a,b,d,c]])


        # clauses learned:
        #constraints += at_most_one_clauses([+var_ab_cross_cd_directed[a,b,c,d],+var_ab_cross_cd[a,c,b,d]])
        #constraints += at_most_one_clauses([+var_ab_cross_cd[a,b,c,d],+var_ab_cross_cd[a,c,b,d]])
        #constraints.append([-var_ab_cross_cd[a,b,c,d],+var_a_sees_bcd[d,a,b,c],+var_a_sees_bcd[b,a,c,d]])


def forbid_planar_subgraph(edges):
    return [[+var_ab_cross_cd[a,b,c,d] for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]]

def assert_planar_subgraph(edges):
    return [[-var_ab_cross_cd[a,b,c,d]] for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]

if 0: 
    print ("plane path from a to b using vertices I",len(constraints))
    for x in range(1,n):
        for I in permutations(set(N)-{0,x},n//2-1):
            path = (0,)+I+(x,)
            edges = [(path[i],path[i+1]) for i in range(len(path)-1)]
            constraints += A_equals_conjunctionB_clauses(var_plane_0x_I_path_ordered[x,I], 
                                                         [-var_ab_cross_cd[a,b,c,d] for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4])
        for I in combinations(set(N)-{0,x},n//2-1):
            constraints += A_equals_disjunctionB_clauses(var_plane_0x_I_path_unordered[x,I],
                                                         [var_plane_0x_I_path_ordered[x,J] for J in permutations(I)])

if 0: 
    print ("plane path from a to b using vertices I",len(constraints))
    for k in range(4,n+1):
        for I in permutations(N,k):
            edges = [(I[i],I[i+1]) for i in range(len(I)-1)]
            #constraints += A_equals_conjunctionB_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]], 
            #                                             [-var_ab_cross_cd[a,b,c,d] for (a,b),(c,d) in combinations(edges,2) 
            #                                              if len({a,b,c,d}) == 4])
            if 0:
                if k == 4: 
                    constraints += equality_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]],
                                                    -var_ab_cross_cd[I[0],I[1],I[2], I[3]])
                if k > 4:
                    constraints += A_equals_conjunctionB_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]], 
                                                            [var_plane_ab_I_path[I[0],I[-2],I[1:-2]]] +
                                                            [-var_ab_cross_cd[I[i], I[i+1],I[-2],I[-1]] for i in range(len(I)-3)])
                    constraints += A_equals_conjunctionB_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]], 
                                                            [var_plane_ab_I_path[I[1],I[-1],I[2:-1]]] +
                                                            [-var_ab_cross_cd[I[i], I[i+1],I[0],I[1]] for i in range(2,len(I)-1)])
                if 0:
                    for a in range(k):
                        for b in range(a+4,k):
                            J = I[a:b] # subpath
                            assert(len(J) >= 4) 
                            constraints.append([-var_plane_ab_I_path[I[0],I[-1],I[1:-1]],var_plane_ab_I_path[J[0],J[-1],J[1:-1]]])

            if 1:
                if k == 3: 
                    constraints += [var_plane_ab_I_path[I[0],I[-1],I[1:-1]]]
                if k > 3:
                    constraints += A_equals_conjunctionB_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]], 
                                                            [var_plane_ab_I_path[I[0],I[-2],I[1:-2]]] +
                                                            [-var_ab_cross_cd[I[i], I[i+1],I[-2],I[-1]] for i in range(len(I)-3)])
                    constraints += A_equals_conjunctionB_clauses(var_plane_ab_I_path[I[0],I[-1],I[1:-1]], 
                                                            [var_plane_ab_I_path[I[1],I[-1],I[2:-1]]] +
                                                            [-var_ab_cross_cd[I[i], I[i+1],I[0],I[1]] for i in range(2,len(I)-1)])
    

if args.forbidHC:
    print ("(HC) there is no plane Hamiltonian cycle",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in N])
            if 0:
                constraints.append([-var_plane_ab_I_path[perm[0],perm[-1],perm[1:-1]]] + [var_ab_cross_cd[perm[0],perm[-1],perm[i],perm[i+1]] for i in  range(1,n-2)])
            

if args.forbidHP:
    print ("(HP) there is no plane Hamiltonian path",len(constraints))
    for perm in permutations(N):
        if perm[0] < perm[-1]: # wlog
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in range(1,n)])
            
            
if 0:
    print ("(HC) there is no plane Hamiltonian cycle - but in a smart way",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            x = perm[n//2]
            I = tuple(sorted(perm[1:n//2]))
            J = tuple(sorted(set(N)-{0,x}-set(I)))
            for C in forbid_planar_subgraph([(perm[i-1],perm[i]) for i in N]):
                constraints.append([-var_plane_0x_I_path_unordered[x,I], 
                                    -var_plane_0x_I_path_unordered[x,J]]+C)

if 0:    
    for x in range(1,n):
        for I in combinations(set(N)-{0,x},n//2-1):
            J = tuple(sorted(set(N)-{0,x}-set(I)))
            constraints.append([-var_plane_0x_I_path_unordered[x,I], -var_plane_0x_I_path_unordered[x,J]])

print ("Total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)
print ()


if args.var2file == '_':
    args.var2file = args.cnf2file+".var"

if args.var2file:
    print ("write variables to file:",args.var2file)
    with open(args.var2file,"w") as f:
        f.write(str(vpool.id2obj)+"\n")
        f.close()

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
        if args.use_rs:
            for a in N:
                order_a = []
                for i in N_without_last:
                    for b in N_without[a]:
                        if var_rotsys[a,i,b] in sol:
                            order_a.append(b)

                rs.append(order_a)
        else:
            # read rotation system from triple orientations of cyclic orders
            for x in N:
                y = min(N_without[x])
                order_x = [y]
                remaining = set(N) - {x,y}
                while remaining:
                    next_found = False
                    for a in remaining:
                        a_is_next = True
                        for b in remaining - {a}:
                            if -var_a_sees_bcd[x,y,a,b] in sol:
                                a_is_next = False
                                break
                        if a_is_next: 
                            order_x.append(a)
                            remaining.remove(a)
                            next_found = True
                            break
                    #print("nextfound",x,y,remaining)
                    assert(next_found)
                rs.append(order_x)
        
        print (datetime.datetime.now(),"solution #",ct,"\t",rs)
        assert(rs not in found)        
        found.append(rs)
        if outfile: outfile.write(str(rs)+"\n")
        
        
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


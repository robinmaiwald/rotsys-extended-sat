""" An extension of Manfreds Scheuchers SAT framework, used in my Bachelor Thesis
    "Kreuzungszahlen von fast vollständigen Graphen"
"""


from itertools import combinations, permutations, product
from ast import literal_eval

import datetime
import math 

from pysat.formula import IDPool,CNF
from pysat.card import *



import argparse
parser = argparse.ArgumentParser()
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
parser.add_argument("-l",'-lex',"--lexmin",action='store_true', help="restrict to lexigraphic minima (symmetry breaking w.r.t. relabeling+mirroring)")
parser.add_argument("-c","--convex",action='store_true', help="restrict to convex")
parser.add_argument("-hc","--hconvex",action='store_true', help="restrict to h-convex")
parser.add_argument("-cm","--cmonotone",action='store_true', help="restrict to circularly monotone")
parser.add_argument("-scm","--stronglycmonotone",action='store_true', help="restrict to strongly circularly monotone")
parser.add_argument("-gt","--gtwisted",action='store_true', help="restrict to generalized twisted") 
parser.add_argument("-crmax","--crossingmaximal",action='store_true', help="force crossingmaximal drawing")


parser.add_argument("-nat","--natural",action='store_false',help="remove assumption that first line needs not to be 2,3,...,n (enabled by default, use parameter to disable)")
parser.add_argument("-v4","--valid4tuples",action='store_false',help="remove assumption that 4-tuples are valid (enabled by default, use parameter to disable)")
parser.add_argument("-v5","--valid5tuples",action='store_false',help="remove assumption that 5-tuples are valid (enabled by default, use parameter to disable)")

parser.add_argument("-HC","--forbidHC",action='store_true', help="forbid plane Hamiltonian cycle")
parser.add_argument("-HC+","--forbidHCplus",action='store_true', help="forbid plane Hamiltonian subgraphs oA ∨ B ∨ Cn 2n-3 edges")

parser.add_argument("-HT+","--HoffmannTothplus",type=int, help="check strengthened Hoffmann-Toth property")

parser.add_argument("--forbidAllPairsHP",action='store_true', help="assume that for a pair of vertices there is no plane Hamiltonian path")

parser.add_argument("-ec","--emptycycles",type=int,help="forbid empty cycles of specified size")


parser.add_argument("-aec","--alledgescrossed",action='store_true', help="assert that all edges are crossed")
parser.add_argument("-aecsub","--alledgescrossedsub",action='store_true', help="assert that all edges are crossed in subconfigurations")

parser.add_argument("-crf","--crossingfamily",type=int,help="forbid crossing family of given size")

parser.add_argument("-C","--forbidCk",type=int,default=None, help="forbid the perfect convex C_k")
parser.add_argument("-T","--forbidTk",type=int,default=None, help="forbid the perfect twisted T_k")
parser.add_argument("-X","--forbidcrmaxk",type=int,default=None, help="forbid crossingmaximal subdrawings of K_k")

parser.add_argument("-etlow",type=int,help="minimum number of empty triangles")
parser.add_argument("-etupp",type=int,help="maximum number of empty triangles")

parser.add_argument("-crlow",type=int,help="minimum number of crossings")
parser.add_argument("-crupp",type=int,help="maximum number of crossings")

parser.add_argument("-R","--use_rs_vars",action='store_true', help="use variables for encoding rotations system via permutations")

parser.add_argument("--checkATgraphs",action='store_true',help="assert that no two rotation systems yield the same pair of crossing edges (AT graph)")

parser.add_argument("-r2f","--rs2file", type=str, help="if specified, export rotation systems to this file")
parser.add_argument("-c2f","--cnf2file","-o", type=str,help="if specified, export CNF to this file")
parser.add_argument("-v2f","--var2file", type=str,help="if specified, export variables of CNF to this file")
parser.add_argument("-1","--one_to_one",action='store_true', help="one-to-one correspondence between CNF and rotation systems")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")

parser.add_argument("-D","--debug", action='store_true',help="debug mode")

parser.add_argument("-fixMLow",nargs="+",type=str,help="delets a fixed matching and sets Lower bound for crossingnumber. Usage: -fixMLow 'matching' bound ")
parser.add_argument("-fixMUp",nargs="+",type=str,help="delets a fixed matching and sets upper bound for crossingnumber. Usage: -fixMUp 'matching' bound ")
parser.add_argument("-twoColor",action='store_false',help="remove assumption that two Colow Crossings are forbidden (enabled by default, use parameter to disable)")

parser.add_argument("-octaFix", nargs='?',const=1,type=int,default=None,help="Ensure that at least one Octahedron induced by 3 deleted edges has exactly k crossings (default: 1)")
parser.add_argument("-goodOcta", nargs='?',const=1,type=int,default=None,help="Ensures that in all induced octahedrons, there exist atleast k crossings (default 2)")
parser.add_argument("-goodCross", type=int, default=None, help="Require exactly this many 'good' crossings (only with -fixMLow/Up and -octaFix combined)")


args = parser.parse_args()
print("args",args)



#vargs = vars(args)
#print("c\tactive args:",{x:vargs[x] for x in vargs if vargs[x] != None and vargs[x] != False})


if args.hconvex: args.convex = True

use_emptytriangle_variables = False
if args.etlow != None or args.etupp != None: use_emptytriangle_variables = True

if args.lexmin: args.use_rs_vars = True

time_start = datetime.datetime.now()

n = args.n
N = list(range(n))

N_without_last = list(range(n-1))
N_without = {i:[j for j in N if j!=i] for i in N}

if args.cmonotone or args.stronglycmonotone:
    # vertices 0 and 1 are used to ensure c-monotonicity
    all_vertices = list(range(n+2)) # use two auxiliary vertices for the encoding
else:
    all_vertices = N

all_vertices_without = {i:[j for j in all_vertices if j!=i] for i in all_vertices} 


vpool = IDPool()
constraints = []
        
var_a_sees_bcd_ = {}
def var_a_sees_bcd(*I): return var_a_sees_bcd_[I]
# b is the i-th vertex in cyclic order around vertex a
for a in all_vertices: # remark: using "all_vertices" instead of "N" because for cmonotone there are auxiliary vertices
    for b,c,d in combinations(all_vertices_without[a],3): 
        var_a_sees_bcd_[a,b,c,d] = var_a_sees_bcd_[a,c,d,b] = var_a_sees_bcd_[a,d,b,c] = vpool.id(f"S{a}_{b}_{c}_{d}")
        var_a_sees_bcd_[a,b,d,c] = var_a_sees_bcd_[a,c,b,d] = var_a_sees_bcd_[a,d,c,b] = -var_a_sees_bcd_[a,b,c,d]
        

# Remark: we declare all boolean variables to prevent the usage of faulty variables in the encoding
if args.use_rs_vars: 
    # around vertex a, we have b then c then d
    var_rotsys_ = {(a,i,b):vpool.id(f"R{a}_{i}_{b}") for a in N for i in N_without_last for b in N_without[a]} 
    def var_rotsys(*I): return var_rotsys_[I]

def cross(a,b,c,d):
    if a>b: return cross(b,a,c,d)
    if c>d: return cross(a,b,d,c)
    if a>c: return cross(c,d,a,b)
    return vpool.id(f"C{a}_{b}_{c}_{d}")

def dcross(a,b,c,d):
    a,b,c,d = min([(a,b,c,d),(c,d,b,a),(b,a,d,c),(d,c,a,b)])
    return vpool.id(f"D{a}_{b}_{c}_{d}")

def edge_exists(a,b):                               
    if a>b: return edge_exists(b,a)
    return vpool.id(f"E{a}_{b}")     

def mcross(a,b,c,d):
    if a>b: return mcross(b,a,c,d)
    if c>d: return mcross(a,b,d,c)
    if a>c: return mcross(c,d,a,b)
    return vpool.id(f"C'{a}_{b}_{c}_{d}")
   

def octahedron(a1,b1,a2,b2,a3,b3):
    if a1>b1: return octahedron(b1,a1,a2,b2,a3,b3)
    if a2>b2: return octahedron(a1,b1,b2,a2,a3,b3)
    if a3>b3: return octahedron(a1,b1,a2,b2,b3,a3)
    if a1>a2: return octahedron(a2,b2,a1,b1,a3,b3)
    if a2>a3: return octahedron(a1,b1,a3,b3,a2,b2)
    return vpool.id(f"Octa_{a1}_{b1}_{a2}_{b2}_{a3}_{b3}")


var_ab_cross_cd_ =          {(a,b,c,d):cross(a,b,c,d) for a,b,c,d in permutations(all_vertices,4)}
var_ab_cross_cd_directed_ = {(a,b,c,d):dcross(a,b,c,d) for a,b,c,d in permutations(all_vertices,4)}
all_edges_ =                {(a,b): edge_exists(a,b) for a,b in permutations(all_vertices,2)}
var_ab_cross_cd_masked_ =   {(a,b,c,d):mcross(a,b,c,d) for a,b,c,d in permutations(all_vertices,4)}
octahedrons_ =              {(a,b,c,d,e,f): octahedron(a,b,c,d,e,f) for a,b,c,d,e,f in permutations(all_vertices,6)}
deleted_perfect_matchings = []



def var_ab_cross_cd(*I): return var_ab_cross_cd_[I]
def var_ab_cross_cd_directed(*I): return var_ab_cross_cd_directed_[I]
def var_ab_cross_cd_masked(*I): return var_ab_cross_cd_masked_[I] 

def edgeCheck(*I): return all_edges_[I]
def octaCheck(*I): return octahedrons_[I]



if args.lexmin:
    # full symmetry breaking
    assert(args.use_rs_vars) # only implemented if rotsys variables are provided
    var_perm_ = {(x0,x1,a,b):vpool.id() for x0 in N for x1 in N_without[x0] for a in N for b in N}
    var_rotsys_perm_ = {(x0,x1,a,i,b,mir):vpool.id() for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]}
    var_rotsys_perm_eq_orig_ = {(x0,x1,a,i,b,mir):vpool.id() for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]}
    var_rotsys_perm_gt_orig_ = {(x0,x1,a,i,b,mir):vpool.id() for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]}
    var_rotsys_perm_lt_orig_ = {(x0,x1,a,i,b,mir):vpool.id() for x0 in N for x1 in N_without[x0] for a in N for i in N_without_last for b in N_without[a] for mir in [False,True]}
    
    def var_perm(*I): return var_perm_[I]
    def var_rotsys_perm(*I): return var_rotsys_perm_[I]
    def var_rotsys_perm_eq_orig(*I): return var_rotsys_perm_eq_orig_[I]
    def var_rotsys_perm_gt_orig(*I): return var_rotsys_perm_gt_orig_[I]
    def var_rotsys_perm_lt_orig(*I): return var_rotsys_perm_lt_orig_[I]

    
    
if use_emptytriangle_variables:
    var_abc_contains_d_ = {(a,b,c,d):vpool.id() for a,b,c,d in permutations(N,4)} 
    def var_abc_contains_d(*I): return var_abc_contains_d_[I]

    containment_types = [(1,1,1),(-1,1,1),(1,-1,1),(1,1,-1)]
    var_abc_contains_d_type_ = {(a,b,c,d,t):vpool.id() for a,b,c,d in permutations(N,4) for t in containment_types} 
    def var_abc_contains_d_type(*I): return var_abc_contains_d_type_[I]
    
    var_abc_empty_ = {(a,b,c):vpool.id() for a,b,c in permutations(N,3)}
    def var_abc_empty(*I): return var_abc_empty_[I]




## CONSTRAINTS

print ("(*) assert a_sees_bcd",len(constraints))
for x in all_vertices: # for every element we have a cyclic order which is encoded through forbidden patterns on 4-element subsets
    for a,b,c,d in combinations(all_vertices_without[x],4): # remark: using "all_vertices" instead of "N" because for cmonotone there are auxiliary vertices
        for s in [+1,-1]:
            constraints.append([+s*var_a_sees_bcd(x,a,b,c),-s*var_a_sees_bcd(x,a,b,d),+s*var_a_sees_bcd(x,a,c,d)]) # no 4=bcd
            constraints.append([+s*var_a_sees_bcd(x,a,b,d),-s*var_a_sees_bcd(x,a,c,d),+s*var_a_sees_bcd(x,b,c,d)]) # no 1=abc
            constraints.append([-s*var_a_sees_bcd(x,a,b,c),-s*var_a_sees_bcd(x,a,c,d),+s*var_a_sees_bcd(x,b,c,d)]) # no 2=abd
            constraints.append([+s*var_a_sees_bcd(x,a,b,c),-s*var_a_sees_bcd(x,a,b,d),-s*var_a_sees_bcd(x,b,c,d)]) # no 3=acd
            
if args.natural:
    print ("(*) assert natural",len(constraints))
    for a,b,c in combinations(N_without[0],3):
        constraints.append([var_a_sees_bcd(0,a,b,c)])


if args.use_rs_vars:
    print ("(*) wlog: first column is 1,0,0,...,0")
    constraints.append([var_rotsys(0,0,1)])
    for a in N_without[0]:
        constraints.append([var_rotsys(a,0,0)])

    if args.natural:
        print ("(*) wlog: first line is 1,2,3,4,...")
        for a in N_without_last:
            constraints.append([var_rotsys(0,a,a+1)])


    print ("(*) assert permutations",len(constraints))
    for a in N:
        for i in N_without_last:
            constraints.append([var_rotsys(a,i,b) for b in N_without[a]])
            for b1,b2 in combinations(N_without[a],2):
                constraints.append([-var_rotsys(a,i,b1),-var_rotsys(a,i,b2)])

        for b in N_without[a]:
            constraints.append([var_rotsys(a,i,b) for i in N_without_last])
            for i1,i2 in combinations(N_without_last,2):
                constraints.append([-var_rotsys(a,i1,b),-var_rotsys(a,i2,b)])

    print ("(*) assert a_sees_bcd",len(constraints))
    for a,b,c,d in permutations(N,4):
        for i,j,k in combinations(N_without_last,3):
            constraints.append([-var_rotsys(a,i,b),-var_rotsys(a,j,c),-var_rotsys(a,k,d),+var_a_sees_bcd(a,b,c,d)])
    


## FORBID NON-REALIZABLE PRE-RS
def forbid_subrs(subrs,vertex_set=N):
    k = len(subrs)
    constraints = []
    for I in permutations(vertex_set,k):
        for s in [+1,-1]: # forbid original and mirrored
            constraints.append([-s*var_a_sees_bcd(I[a],I[b],I[c],I[d]) for a in range(k) for b,c,d in combinations(subrs[a],3)])
    return constraints


if args.valid4tuples:
    print ("(*) assert valid 4-tuples",len(constraints)) # remark: also affects auxiliary vertices
    constraints += forbid_subrs(
        [[1,2,3],[0,2,3],[0,1,3],[0,2,1]],vertex_set=all_vertices)

if args.valid5tuples:
    print ("(*) assert valid 5-tuples") # remark: also affects auxiliary vertices
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,3,4],[0,3,1,4],[0,4,2,1],[0,3,1,2]],vertex_set=all_vertices) # forbidden type I
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,4,3],[0,3,1,4],[0,4,2,1],[0,1,3,2]],vertex_set=all_vertices) # forbidden type II



## SUBCLASSES

if args.convex:
    print ("(C) restrict to convex drawings",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,4,3],[0,1,3,4],[0,1,4,2],[0,3,1,2]]) # obstruction with 3 crossings
    constraints += forbid_subrs(
        [[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,4,2],[0,1,3,2]]) # T5, i.e., obstruction 5 crossings


if args.hconvex:
    assert(args.convex)
    print ("(H) restrict to h-convex drawings",len(constraints))
    constraints += forbid_subrs(
        [[1,2,3,4,5],[0,2,3,4,5],[0,1,5,3,4],[0,1,2,4,5],[0,1,2,3,5],[0,1,3,4,2]])


if args.gtwisted:
    print ("(GT) restrict to generalized twisted",len(constraints)) 
    if n >= 4:
        constraints += forbid_subrs([[1,2,3],[0,3,2],[0,1,3],[0,2,1]]) 
    if n == 6:
        constraints += forbid_subrs([[1,2,3,4,5],[0,2,3,4,5],[0,1,3,5,4],[0,4,1,5,2],[0,3,1,5,2],[0,1,3,2,4]]) 
    for subrs in [    
        [[1,2,3,4],[0,3,4,2],[0,1,4,3],[0,2,4,1],[0,3,2,1]],
        [[1,2,3,4],[0,2,3,4],[0,1,4,3],[0,1,2,4],[0,1,3,2]],
        [[1,2,3,4],[0,2,4,3],[0,1,3,4],[0,1,4,2],[0,3,1,2]],
        [[1,2,3,4],[0,2,3,4],[0,1,3,4],[0,1,2,4],[0,1,2,3]]]:
        constraints += forbid_subrs(subrs) 
        

if args.cmonotone or args.stronglycmonotone:
    assert(not args.one_to_one) # does not work due to auxiliary vertices
    print("(*) assume c-monotone")
    x = n # two auxiliary vertices to ensure (strong) c-monotonicity
    y = n+1
    assert(set(all_vertices) == set(N)|{x,y}) 
    for a,b in permutations(N,2):
        constraints.append([-var_ab_cross_cd(x,a,y,b)])

    # above constraint is sufficient for c-monotonicity, the one below is implied
    #for a,b,c in permutations(N,3):
    #    constraints.append([-var_ab_cross_cd(x,a,b,c),-var_ab_cross_cd(y,a,b,c)])


    if args.stronglycmonotone:
        print("(*) assume strongly c-monotone")        
        for a in N:
            rest = set(N)-{a}
            X = {b: vpool.id() for b in rest} # auxiliary variables to make sure the a-star does not wrap around 
            constraints.append([X[b] for b in rest])
            for b in rest:
                for c in rest-{b}:
                    constraints.append([-X[b],-var_ab_cross_cd(x,b,a,c)])
                    constraints.append([-X[b],-var_ab_cross_cd(y,b,a,c)])
                constraints.append([X[b]]+[var_ab_cross_cd(x,b,a,c) for c in rest-{b}]+[var_ab_cross_cd(y,b,a,c) for c in rest-{b}])


print ("(*) assert ab_cross_cd",len(constraints))
for a,b,c,d in permutations(all_vertices,4):
    constraints.append([
        -var_a_sees_bcd(a,b,d,c),
        -var_a_sees_bcd(b,a,c,d),
        -var_a_sees_bcd(c,a,b,d),
        -var_a_sees_bcd(d,a,c,b),+var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(a,b,d,c),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(b,a,c,d),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(c,a,b,d),-var_ab_cross_cd_directed(a,b,c,d)])
    constraints.append([
        +var_a_sees_bcd(d,a,c,b),-var_ab_cross_cd_directed(a,b,c,d)])

    constraints.append([-var_ab_cross_cd_directed(a,b,c,d),+var_ab_cross_cd(a,b,c,d)])
    constraints.append([-var_ab_cross_cd_directed(a,b,d,c),+var_ab_cross_cd(a,b,c,d)]) 
    constraints.append([+var_ab_cross_cd_directed(a,b,c,d),+var_ab_cross_cd_directed(a,b,d,c),-var_ab_cross_cd(a,b,c,d)])


if 1:
    print("(*) optimization for crossings")
    # among every 4 tuple there is at most one directed crossing
    # adding this fact slightly improves runtime of kissat 
    for I in combinations(all_vertices,4):
        dcross_vars_I = {var_ab_cross_cd_directed(*J) for J in permutations(I)}
        for a,b in combinations(dcross_vars_I,2):
            constraints.append([-a,-b])


if args.lexmin:
    assert(args.natural)
    print ("(*) assert permutations for lexmin / symmetry breaking",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for a in N:
                constraints.append([var_perm(x0,x1,a,b) for b in N])
                for b1,b2 in combinations(N,2):
                    constraints.append([-var_perm(x0,x1,a,b1),-var_perm(x0,x1,a,b2)])

            for b in N:
                constraints.append([var_perm(x0,x1,a,b) for a in N])
                for a1,a2 in combinations(N,2):
                    constraints.append([-var_perm(x0,x1,a1,b),-var_perm(x0,x1,a2,b)])

            constraints.append([+var_perm(x0,x1,x0,0)])
            constraints.append([+var_perm(x0,x1,x1,1)])
            
            for l in N_without_last: # l = position of x1 in row x0
                for i in N_without_last: # column 
                    for x in N_without[x0]: # x = entry in row x0 column l+i in original rotsys = pi^-1( entry (0,i) in new rot sys )
                        constraints.append([-var_rotsys(x0,l,x1),-var_rotsys(x0,(l+i)%(n-1),x),+var_perm(x0,x1,x,(1+i))])



    print ("(*) assert permuted+mirrored rotation systems",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for a in N:
                for mir in [False,True]:
                    for i in N_without_last:
                        constraints.append([var_rotsys_perm(x0,x1,a,i,b,mir) for b in N if b != a])
                        for b1,b2 in combinations(N_without[a],2):
                            constraints.append([-var_rotsys_perm(x0,x1,a,i,b1,mir),-var_rotsys_perm(x0,x1,a,i,b2,mir)])

                    for b in N_without[a]:
                        constraints.append([var_rotsys_perm(x0,x1,a,i,b,mir) for i in N_without_last])
                        for i1,i2 in combinations(N_without_last,2):
                            constraints.append([-var_rotsys_perm(x0,x1,a,i1,b,mir),-var_rotsys_perm(x0,x1,a,i2,b,mir)])



    print ("(*) synchronize permuted rotation systems",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            for k in N: # row
                for xk in N: # xk = pi^-1(k)
                    for l in N_without_last: # l = position of x0 in row xk
                        for i in N_without_last: # column
                            for x in N_without[xk]: # x = entry in row xk column l+i in original rotsys = pi^-1( entry (k,i) in new rot sys )
                                for pix in N_without[k]: # pix = pi(x) = entry (k,i) in new rot sys
                                    if xk == x0 and k == 0: # first row
                                        constraints.append([-var_perm(x0,x1,xk,k),-var_rotsys(xk,l,x1),-var_rotsys(xk,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,k,i,pix,False)])
                                        # this is equal to
                                        #constraints.append([-var_perm(x0,x1,x0,0),-var_rotsys(x0,l,x1),-var_rotsys(x0,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,0,i,pix)])
                                    if xk != x0 and k != 0: # other rows
                                        constraints.append([-var_perm(x0,x1,xk,k),-var_rotsys(xk,l,x0),-var_rotsys(xk,(l+i)%(n-1),x),-var_perm(x0,x1,x,pix),+var_rotsys_perm(x0,x1,k,i,pix,False)])



    print ("(*) synchronize mirrored rotation systems",len(constraints))
    mirrored_rows = [0,1]+list(reversed(range(2,n  ))) # permutation of elements/rows for mirroring
    mirrored_cols = [0]  +list(reversed(range(1,n-1))) # permutation of cols for mirroring
    for i in N:              assert(mirrored_rows[mirrored_rows[i]]==i) # involution
    for i in N_without_last: assert(mirrored_cols[mirrored_cols[i]]==i) # involution

    for x0 in N: 
        for x1 in N_without[x0]: 
            for a in N:
                for i in N_without_last:
                    for b in N_without[a]:
                        for mir in [False,True]:
                            constraints.append([-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm(x0,x1,mirrored_rows[a],mirrored_cols[i],mirrored_rows[b],not mir)])
                    


    print ("(*) compare permuted rotation systems for symmetry breaking",len(constraints))
    for x0 in N: # x0 = pi^-1(0)
        for x1 in N_without[x0]: # x1 = pi^-1(1)
            prev_a = None
            prev_i = None
            prev_b = None
            for a in N:
                for i in N_without_last:
                    for b in N_without[a]:
                        for mir in [False,True]:
                            constraints.append([-var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)]) # permuted rotation systems should not be smaller
                            constraints.append([-var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir),-var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)]) # but equal or greater (not both) 

                            if prev_a == None:
                                constraints.append([-var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([+var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([+var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                            else:
                                constraints.append([-var_rotsys_perm_lt_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_gt_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),-var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),-var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_gt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys(a,i,b),-var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_lt_orig(x0,x1,a,i,b,mir)])
                                constraints.append([-var_rotsys_perm_eq_orig(x0,x1,prev_a,prev_i,prev_b,mir),+var_rotsys(a,i,b),+var_rotsys_perm(x0,x1,a,i,b,mir),+var_rotsys_perm_eq_orig(x0,x1,a,i,b,mir)])

                        prev_a = a
                        prev_i = i
                        prev_b = b



def forbid_planar_subgraph(edges):
    return [[+var_ab_cross_cd(a,b,c,d) for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]]

def assert_planar_subgraph(edges):
    return [[-var_ab_cross_cd(a,b,c,d)] for (a,b),(c,d) in combinations(edges,2) if len({a,b,c,d}) == 4]


if args.forbidHC:
    print ("(HC) there is no plane Hamiltonian cycle",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in N])


if args.forbidHCplus:
    print ("(HC+) there is no plane Hamiltonian subgraph on 2n-3 edges",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[1] < perm[-1]: # wlog
            HC_edges = [(perm[i-1],perm[i]) for i in N]
            remaining_edges = [(a,b) for (a,b) in combinations(N,2) if (a,b) not in HC_edges and (b,a) not in HC_edges]
            for E in combinations(remaining_edges,n-3):
                constraints += forbid_planar_subgraph(HC_edges+list(E))



if args.HoffmannTothplus:
    k = args.HoffmannTothplus
    assert(n >= 2*k) 
    print ("(HT+) test strengthened HoffmannToth property: for every plane matching of size",k,"there is a plane HC not crossing any of the edges")

    matching_edges = [(2*i,2*i+1) for i in range(k)]

    constraints += assert_planar_subgraph(matching_edges)

    for perm in permutations(N):
        if perm[0] == 0: # wlog
            HC_edges = [(perm[i-1],perm[i]) for i in N]
            constraints += forbid_planar_subgraph(HC_edges + matching_edges)
    
    if k > 1: assert(not args.natural) 
    # the following assumptions are w.l.o.g. to break symmetries;
    # those assumptions are a generalization of the assumptions for natural labelings (for k=1 they coincide)
    remaining_vertices = range(2*k,n)
    for a,b in matching_edges[1:]:
        constraints.append([+var_a_sees_bcd(0,1,a,b)])
    for (a,b),(c,d) in combinations(matching_edges[1:],2):
        constraints.append([+var_a_sees_bcd(0,1,a,c)])
    for a,c in combinations(remaining_vertices,2):
        constraints.append([+var_a_sees_bcd(0,1,a,c)])



if args.forbidAllPairsHP:
    assert(not args.lexmin)
    print ("(HPj) assume that for a pair of vertices there is no plane Hamiltonian path; wlog for uv=01",len(constraints))
    for perm in permutations(N):
        if perm[0] == 0 and perm[-1] == 1:
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in range(1,n)])


if args.emptycycles:
    # the selected pq must be intersected or cycle is non-planar
    k = args.emptycycles
    var_empty_cycle_violation_pq_ = {(I,p,q):vpool.id(f"W_{I}_{p}_{q}") for I in permutations(N,k) for p,q in combinations(set(N)-set(I),2)}
    def var_empty_cycle_violation_pq(*I): return var_empty_cycle_violation_pq_[I]
    for I in permutations(N,k):
        if I[0] == min(I) and I[1] > I[-1]: 
            # w.l.o.g. for cyclic permutation 
            PQ = list(combinations(set(N)-set(I),2))
            E_I = [(I[j-1],I[j]) for j in range(k)] # edges of cycle
            constraints.append(
                 [+var_ab_cross_cd(*e,*f) for e,f in combinations(E_I,2) if not set(e)&set(f)]
                +[+var_empty_cycle_violation_pq(I,p,q) for p,q in PQ])
            for p,q in PQ:
                for cross_indication in product([+1,-1],repeat=k):
                    # pq is witnessing that I not forms an empty k-cycle 
                    # if and only if the number of crossings of pq and E_I is odd
                    t = +1 if (cross_indication.count(+1) % 2) == 0 else -1 
                    if t == +1: # the inverse direction is not helpful
                        constraints.append(
                             [-t*var_empty_cycle_violation_pq(I,p,q)]
                            +[-s*var_ab_cross_cd(p,q,*e) for s,e in zip(cross_indication,E_I)])



if use_emptytriangle_variables:
    print ("(et) assert triangle containment and empty triangles",len(constraints))
    for a,b,c,d in permutations(N,4):
        for t in containment_types:
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[0]*var_a_sees_bcd(a,b,d,c)])
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[1]*var_a_sees_bcd(b,c,d,a)])
            constraints.append([-var_abc_contains_d_type(a,b,c,d,t)]+[+t[2]*var_a_sees_bcd(c,a,d,b)])
            constraints.append([+var_abc_contains_d_type(a,b,c,d,t),
                -t[0]*var_a_sees_bcd(a,b,d,c),
                -t[1]*var_a_sees_bcd(b,c,d,a),
                -t[2]*var_a_sees_bcd(c,a,d,b)])


    for a,b,c,d in permutations(N,4):
        constraints.append([-var_abc_contains_d(a,b,c,d)]+[+var_abc_contains_d_type(a,b,c,d,t) for t in containment_types])
        for t in containment_types:
            constraints.append([+var_abc_contains_d(a,b,c,d),-var_abc_contains_d_type(a,b,c,d,t)])

    for a,b,c in permutations(N,3):
        for d in set(N)-{a,b,c}:
            constraints.append([-var_abc_empty(a,b,c),-var_abc_contains_d(a,b,c,d)])
        constraints.append([+var_abc_empty(a,b,c)]+[+var_abc_contains_d(a,b,c,d) for d in set(N)-{a,b,c}])


# count empty triangles
if args.etlow != None or args.etupp != None:
    use_emptytriangle_variables_vars = [var_abc_empty(a,b,c) for (a,b,c) in permutations(N,3) if a == min(a,b,c)]

if args.etlow != None:
    print ("(etlow) minimum number of empty triangles:",args.etlow,len(constraints))
    constraints += list(CardEnc.atleast(lits=use_emptytriangle_variables_vars, bound=args.etlow, encoding=EncType.totalizer, vpool=vpool)) 

if args.etupp != None:
    print ("(etupp) maximum number of empty triangles:",args.etupp,len(constraints))
    constraints += list(CardEnc.atmost(lits=use_emptytriangle_variables_vars, bound=args.etupp, encoding=EncType.totalizer, vpool=vpool))


# crossing number
    for a in all_vertices:
        for b in all_vertices:
            if a >= b: continue  # ordered pairs only, skip a == b and duplicates

            for c in all_vertices:
                if c == a: continue
                if c == b: continue
                for d in all_vertices:
                    if d >= c: continue 
                    if d == a: continue
                    if d == b: continue
                    if d == c: continue  # skip edges sharing a vertex (avoid self-crossing)

                    print(a,b,c,d)
                    var = var_ab_cross_cd(a,b,c,d)

                    print(var)

                    #print(var_ab_cross_cd_)
        
if args.crlow != None or args.crupp != None:
    crossing_vars = [var_ab_cross_cd(a,b,c,d) for (a,b,c,d) in permutations(N,4) if a<b and c<d and a<c]

if args.fixMLow != None or args.fixMUp != None:
    edge_vars = [edgeCheck(a,b) for (a,b) in permutations(N,2) if a<b]
    masked_crossing_vars = [var_ab_cross_cd_masked(a,b,c,d) for (a,b,c,d) in permutations(N,4) if a<b and c<d and a<c]

    if args.fixMLow != None:
        deleted_edges = set(literal_eval(args.fixMLow[0]))
    
    if args.fixMUp != None:
        deleted_edges = set(literal_eval(args.fixMUp[0]))

    deleted_edges = set((min(a, b), max(a, b)) for a, b in deleted_edges)
    remaining_edges = set([(a,b) for a,b in combinations(N,2) if a<b and (a,b) not in deleted_edges])
    all_edges = remaining_edges | deleted_edges 



if args.crlow != None:
    print ("(crlow) minimum number of crossings:",args.crlow,len(constraints))
    constraints += list(CardEnc.atleast(lits=crossing_vars, bound=args.crlow, encoding=EncType.totalizer, vpool=vpool)) 

if args.crupp != None:
    print ("(crupp) maximum number of crossings:",args.crupp,len(constraints))
    constraints += list(CardEnc.atmost(lits=crossing_vars, bound=args.crupp, encoding=EncType.totalizer, vpool=vpool))    

# crossing families
if args.crossingfamily:
    k = args.crossingfamily
    print ("(crf) forbid crossing family of size",k,len(constraints))
    for I in combinations(N,2*k):
        for A in combinations(I,k):
            for B in permutations(set(I)-set(A),k):
                edges = [ (A[i],B[i]) for i in range(k) if A[i]<B[i] ] 
                if len(edges) == k: # wlog
                    constraints.append([-var_ab_cross_cd(u,v,w,x) for (u,v),(w,x) in combinations(edges,2)])

        for A in combinations(I,k):
            for B in permutations(set(I)-set(A),k):
                edges = [ (A[i],B[i]) for i in range(k) if A[i]<B[i] ] 
                if len(edges) == k: # wlog
                    constraints.append([-var_ab_cross_cd(u,v,w,x) for (u,v),(w,x) in combinations(edges,2)])


# search examples with no uncrossed edges
if args.alledgescrossed:
    print ("(*) assert that all edges are crossed",len(constraints))
    for a,b in combinations(N,2):
        constraints.append([var_ab_cross_cd(a,b,c,d) for c,d in combinations(set(N)-{a,b},2)])


if args.alledgescrossedsub:
    k0 = 11 if args.convex else 8 # smallest examples where all edges are crossed
    print ("(*) assert that all edges are crossed in subconfigurations of size >=",k0,len(constraints))
    for k in range(k0,n+1):
        for a,b in combinations(range(k),2):
            constraints.append([var_ab_cross_cd(a,b,c,d) for c,d in combinations(set(range(k))-{a,b},2)])


# Ramsey type 
def perfect_convex(n): return [list(range(k))+list(range(k+1,n)) for k in range(n)]
def perfect_twisted(n): return [list(range(k))+list(reversed(range(k+1,n))) for k in range(n)]

if args.forbidCk: 
    k = args.forbidCk
    print (f"(forbidCk) forbid C{k}")
    constraints += forbid_subrs(perfect_convex(k))

if args.forbidTk: 
    k = args.forbidTk
    print (f"(forbidTk) forbid T{k}")
    constraints += forbid_subrs(perfect_twisted(k))


if args.forbidcrmaxk or args.crossingmaximal:
    var_crossing_ = {I:vpool.id() for I in combinations(N,4)}
    def var_crossing(*I): return var_crossing_[I]

    for a,b,c,d in combinations(N,4):
        constraints.append([-var_crossing(a,b,c,d),+var_ab_cross_cd(a,b,c,d),+var_ab_cross_cd(a,c,b,d),+var_ab_cross_cd(a,d,b,c)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,b,c,d)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,c,b,d)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,d,b,c)])

if args.forbidcrmaxk: 
    k = args.forbidcrmaxk
    print (f"(forbidcrmaxk) forbid crossingmaximal subdrawings of K_{k}")

    for I in combinations(N,k):
        constraints.append([-var_crossing(*J) for J in combinations(I,4)])

if args.crossingmaximal:
    print (f"(crmax) force crossingmaximal drawing")
    for I in combinations(N,4):
        constraints.append([var_crossing(*I)])

if 0:
    print("fix sub-rotation system")
    RS =  [[1,2,3,4,5,6,7,8,9,10,11,12,13,14],[0,4,5,2,3,6,7,8,9,10,13,14,11,12],[0,5,1,3,4,6,7,8,9,10,13,14,11,12],[0,1,2,4,5,6,7,8,9,10,13,14,11,12],[0,2,3,5,1,6,7,8,9,10,13,14,11,12],[0,3,4,1,2,6,7,8,9,10,13,14,11,12],[0,1,2,3,4,5,9,10,7,8,13,14,11,12],[0,1,2,3,4,5,10,6,8,9,13,14,11,12],[0,1,2,3,4,5,6,7,9,10,13,14,11,12],[0,1,2,3,4,5,7,8,10,6,13,14,11,12],[0,1,2,3,4,5,8,9,6,7,13,14,11,12],[0,1,2,3,4,5,6,7,8,9,10,13,14,12],[0,13,1,2,3,4,5,6,7,8,9,10,14,11],[0,14,11,1,2,3,4,5,6,7,8,9,10,12],[0,13,11,12,1,2,3,4,5,6,7,8,9,10]]
    assert(len(RS) <= n)
    for a in range(len(RS)):
        assert(set(RS[a])|{a} == set(range(len(RS))))
        for I in combinations(RS[a],3):
            constraints.append([+var_a_sees_bcd(a,*I)])


if 0:
    print("fix cube")
    cube = [449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,-464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,-479,480,481,482,483,484,485,486,487,488,-489,490,491,492,493,494,-495,496,497,498,499,500,-501,-502,503,504]
    for x in cube: constraints.append([x])


if args.fixMLow or args.fixMUp:

    for (u,v) in remaining_edges:
        edge_var = edgeCheck(u,v)
        constraints.append([edge_var])

    for (u,v) in deleted_edges:
        edge_var = edgeCheck(u,v)
        constraints.append([-edge_var])

    if args.fixMLow:
        if len(args.fixMLow) == 2:
            lower_crossing_bound = int(args.fixMLow[1])
        else:
            lower_crossing_bound = 6 * math.comb(int(n/2), 4)

    if args.fixMUp:
        if len(args.fixMUp) == 2:
            upper_crossing_bound = int(args.fixMUp[1])
        else:
            upper_crossing_bound = 6 * math.comb(int(n/2), 4)

    if args.fixMLow:
        print(f"(fixMLow) deleting fixed matching: {deleted_edges} of size: {len(deleted_edges)}")
        print(f"(fixMLow) lower bound for crossings in Kn-I: {lower_crossing_bound}")

    if args.fixMUp:
        print(f"(fixMUp) deleting fixed matching: {deleted_edges} of size: {len(deleted_edges)}")
        print(f"(fixMUp) upper bound for crossings in Kn-I: {upper_crossing_bound}")


    for (a, b), (c, d) in combinations(all_edges, 2):
        if len({a, b, c, d}) < 4: continue

        cross_var = var_ab_cross_cd(a, b, c, d)
        edge_ab = edgeCheck(a, b)
        edge_cd = edgeCheck(c, d)
        masked_var = var_ab_cross_cd_masked(a, b, c, d)

        constraints.append([-masked_var, cross_var])                
        constraints.append([-masked_var, edge_ab])                 
        constraints.append([-masked_var, edge_cd])                 
        constraints.append([-cross_var, -edge_ab, -edge_cd, masked_var])  

    if args.fixMLow:
        constraints += list(CardEnc.atleast(lits=masked_crossing_vars,bound=lower_crossing_bound,encoding=EncType.totalizer,vpool=vpool,))

    if args.fixMUp:
        constraints += list(CardEnc.atmost(lits=masked_crossing_vars,bound=upper_crossing_bound,encoding=EncType.totalizer,vpool=vpool,))
    
    
    # Forbids 2-Color-Crossings
    if args.twoColor is True:
        for (a, b), (c, d) in combinations(deleted_edges, 2):
            constraints.append([-var_ab_cross_cd(a, c, b, d)])
            constraints.append([-var_ab_cross_cd(a, d, b, c)])
        print(f"(twoColor) two color crossings are forbidden")
    else:
        print(f"(twoColor) two color crossings are allowed")


if args.goodOcta is not None:

    octa_cross_bound = args.goodOcta
    print("(goodOcta) enforcing atleast {octa_cross_bound} in all octahedrons combined")
    octa_Fix_crossing_vars = []          

    for (a1, b1), (a2, b2), (a3, b3) in combinations(deleted_edges, 3):
        octahedron_vertices = {a1, b1, a2, b2, a3, b3}
        if len(octahedron_vertices) < 6: continue

        octahedron_edges = [(u, v) for u, v in combinations(octahedron_vertices, 2)
                            if (u, v) not in [(a1, b1), (a2, b2), (a3, b3)]
                            and (v, u) not in [(a1, b1), (a2, b2), (a3, b3)] and u<v]

        for (u1, v1), (u2, v2) in combinations(octahedron_edges, 2):
            if len({u1, v1, u2, v2}) < 4: continue  
            octa_Fix_crossing_vars.append(var_ab_cross_cd(u1, v1, u2, v2))

    if octa_Fix_crossing_vars:
        constraints += list(CardEnc.atleast(lits=octa_Fix_crossing_vars,bound=octa_cross_bound,encoding=EncType.totalizer,vpool=vpool))


if args.octaFix is not None:
    octa_cross_bound = args.octaFix
    print(f"(octaFix) enforcing that at least one octahedron (from deleted edges) has exactly {octa_cross_bound} crossings.")

    satisfying_octa_vars = []

    for (a1, b1), (a2, b2), (a3, b3) in combinations(deleted_edges, 3):
        octa_vertices = (a1, b1, a2, b2, a3, b3)
        if len(octa_vertices) < 6: continue  

        exact_k_var = octaCheck(*octa_vertices)
        satisfying_octa_vars.append(exact_k_var)

        fixed_edges = {(a1, b1), (a2, b2), (a3, b3)}
        octa_edges = [(u, v) for u, v in combinations(octa_vertices, 2) if (u, v) not in fixed_edges and (v,u) not in fixed_edges]

        octa_crossing_vars = []
        for (u1, v1), (u2, v2) in combinations(octa_edges, 2):
            if len({u1, v1, u2, v2}) < 4: continue 
            octa_crossing_vars.append(var_ab_cross_cd(u1, v1, u2, v2))

        if not octa_crossing_vars: continue  

        # Create guarded cardinality encoding: "if exact_k_var → exactly k crossings"
        card = CardEnc.equals(lits=octa_crossing_vars,bound=octa_cross_bound,encoding=EncType.totalizer,vpool=vpool)

        for clause in card.clauses:
            constraints.append(clause + [-exact_k_var])

    if satisfying_octa_vars:
        constraints.append(satisfying_octa_vars)  
    else:
        print("Warning: no valid octahedrons could be constructed from deleted edges.")




if args.goodCross is not None and (args.fixMUp is not None or args.fixMLow is not None) and args.octaFix is not None:

    matching_edges = list(deleted_edges)
    all_matching_vertices = set(v for e in deleted_edges for v in e)
    apex_vertex = [v for v in all_vertices if v not in all_matching_vertices][0]


    good_cross_vars = []

    for v_apex in [apex_vertex]:
        e1 = matching_edges[0]
        e2 = matching_edges[1]
        e3 = matching_edges[2]

        for a in e1:
            for b in e2:
                for c in e3:
                    var1 = var_ab_cross_cd_masked(v_apex, a, b, c)  
                    var2 = var_ab_cross_cd_masked(v_apex, b, a, c) 
                    var3 = var_ab_cross_cd_masked(v_apex, c, a, b)  
                    good_cross_vars += [var1, var2, var3]

    print(f"(goodCross) total good crossing candidates: {len(good_cross_vars)}")

    if good_cross_vars:
        print(f"(goodCross) enforcing exactly {args.goodCross} good crossings")
        constraints += list(CardEnc.equals(lits=good_cross_vars,bound=args.goodCross,encoding=EncType.totalizer,vpool=vpool))


print ("Total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)


if args.var2file:
    print ("write variables to file:",args.var2file)
    with open(args.var2file,"w") as f:
        #f.write(str(vpool.id2obj)+"\n")
        for k,v in vpool.id2obj.items(): f.write(f"{k} -> {v}\n")
        f.close()

if args.cnf2file:
    if 0:
        # filter duplicates
        constraints2 = []
        constraints2set = set()
        for c in constraints:
            c = tuple(sorted(c))
            if c not in constraints2set:
                constraints2.append(c)
                constraints2set.add(c)
        constraints = constraints2


    # CNF(from_clauses=constraints).to_file(args.cnf2file) # command does not work for inccnf
    with open(args.cnf2file,"w") as f:
        if args.cnf2file.split(".")[-1] == "inccnf":
            print ("write inccnf to file:",args.cnf2file)
            f.write("p inccnf\n")
        else:
            print ("write cnf to file:",args.cnf2file)
            f.write("p cnf "+str(vpool.top)+" "+str(len(constraints))+"\n")

        for i,c in enumerate(constraints):
            if args.debug:
                if not [abs(x) for x in c if abs(x) not in vpool.id2obj]: # all variables have names
                    f.write("c")
                    for x in c:
                        if x > 0: f.write(" +"+vpool.id2obj[x])
                        if x < 0: f.write(" -"+vpool.id2obj[-x])
                    f.write("\n")

            f.write(" ".join(str(x) for x in c)+" 0\n")

else:
    outfile = None
    if args.rs2file:
        print ("write rotation systems to file:",args.rs2file)
        outfile = open(args.rs2file,"w")

    ct = 0
    found = []

    if args.checkATgraphs: 
        foundATgraphs = []

    if args.solver == "cadical":
        try:
            from pysat.solvers import Cadical153    
            solver = Cadical153(bootstrap_with=constraints)
        except ImportError:
            from pysat.solvers import Cadical # old pysat versions
            solver = Cadical(bootstrap_with=constraints)

    else:
        import pycosat

    print (datetime.datetime.now(),"start solving")

    while True:
        if args.solver == "cadical":
            if not solver.solve(): break
            sol = solver.get_model()
        else:
            sol = pycosat.solve(constraints)
            if sol == "UNSAT": break
            
        ct += 1
        sol = set(sol) # it's faster to lookup values in set than in list
        

        if args.fixMUp != None or args.fixMLow != None:

            deleted_edges = set()
            for (a, b), var in all_edges_.items():
                if -var in sol:  # Edge is disabled
                    if a < b:
                        deleted_edges.add((a, b))
            if deleted_edges not in deleted_perfect_matchings:
                deleted_perfect_matchings.append(deleted_edges)
            
            remaining_crossings = []
            deleted_crossings = []


            for (a, b, c, d), var in var_ab_cross_cd_.items():
                if var in sol:  # This crossing is active in the solution
                    # Normalize both edges
                    e1 = (min(a, b), max(a, b))
                    e2 = (min(c, d), max(c, d))
                    crossing = vpool.id2obj.get(cross(a,b,c,d))

                    if e1 in deleted_edges or e2 in deleted_edges:
                        if crossing not in deleted_crossings:
                            deleted_crossings.append(vpool.id2obj.get(cross(a,b,c,d)))
                    else:
                        if crossing not in remaining_crossings:
                            remaining_crossings.append(vpool.id2obj.get(cross(a,b,c,d)))

            # Output results
            print(f"{len(remaining_crossings)} Active crossings: {remaining_crossings}")
            print(f"{len(deleted_crossings)} Deleted crossings: {deleted_crossings}")


        rs = []
    
        if args.use_rs_vars:
            for a in N:
                order_a = []
                for i in N_without_last:
                    for b in N_without[a]:
                        if var_rotsys(a,i,b) in sol:
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
                            if -var_a_sees_bcd(x,y,a,b) in sol:
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
        


        if 0:
            rs_full = []
            for x in all_vertices: 
                y = min(all_vertices_without[x]) 

                order_x = [y]
                remaining = set(all_vertices)-{x,y}
                while remaining:
                    next_found = False
                    for a in remaining:
                        a_is_next = True
                        for b in remaining - {a}:
                            if -var_a_sees_bcd(x,y,a,b) in sol:
                                a_is_next = False
                                break
                        if a_is_next: 
                            order_x.append(a)
                            remaining.remove(a)
                            next_found = True
                            break
                    #print("nextfound",x,y,remaining)
                    assert(next_found)
                rs_full.append(order_x)
            print("rs",rs)
            print("rs_full",rs_full)
            exit()


        assert(rs not in found)   
        found.append(rs)
        if outfile: outfile.write(str(rs)+"\n")
        print (datetime.datetime.now(),"solution #",ct,"\t",rs)    


        if args.checkATgraphs:
            assert(args.valid4tuples)
            N2 = combinations(N,2)
            crossing_pairs = [(e,f) for e,f in combinations(N2,2) if not set(e)&set(f) and var_ab_cross_cd(*e,*f) in sol]
            if rs[0][1] < rs[0][-1]: # wlog, otherwise reflection 
                assert(crossing_pairs not in foundATgraphs) # make sure there is no duplicate
                foundATgraphs.append(crossing_pairs)
            print("found new AT-graph graph:",crossing_pairs)


        if not args.all: 
            break
        else:
            # clause to prevent solutions
            if args.one_to_one:
                C = [-x for x in sol]
            else:
                C = [-var_a_sees_bcd(a,rs[a][0],rs[a][i],rs[a][i+1]) for a in N for i in range(1,n-2)]
                     
            if args.solver == "cadical":
                solver.add_clause(C)
            else:
                constraints.append(C)


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

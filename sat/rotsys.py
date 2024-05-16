"""
	A SAT framework for topological drawings
    (c) 2022 Manfred Scheucher <scheucher@math.tu-berlin.de>
             Helena Bergold <helena.bergold@fu-berlin.de>
             Meghana M. Reddy <meghana.mreddy@inf.ethz.ch>
"""


from itertools import combinations, permutations, product
from ast import literal_eval
import datetime

from pysat.formula import IDPool,CNF
from pysat.card import *



import argparse
parser = argparse.ArgumentParser()
parser.add_argument("n",type=int,help="number of elements")
parser.add_argument("-a","--all",action='store_true', help="enumerate all configurations")
parser.add_argument("-l",'-lex',"--lexmin",action='store_true', help="restrict to lexigraphic minima (symmetry breaking w.r.t. relabeling+mirroring)")
parser.add_argument("-c","--convex",action='store_true', help="restrict to convex")
parser.add_argument("-hc","--hconvex",action='store_true', help="restrict to h-convex")
parser.add_argument("-cm","--cmonotone",action='store_true', help="assume circularly monotone")
parser.add_argument("-scm","--stronglycmonotone",action='store_true', help="assume strongly circularly monotone")
parser.add_argument("-gt","--gtwisted",action='store_true', help="restrict to generalized twisted") 

parser.add_argument("-nat","--natural",action='store_false',help="remove assumption that first line needs not to be 2,3,...,n (enabled by default, use parameter to disable)")
parser.add_argument("-v4","--valid4tuples",action='store_false',help="remove assumption that 4-tuples are valid (enabled by default, use parameter to disable)")
parser.add_argument("-v5","--valid5tuples",action='store_false',help="remove assumption that 5-tuples are valid (enabled by default, use parameter to disable)")

parser.add_argument("-HC","--forbidHC",action='store_true', help="forbid plane Hamiltonian cycle")
parser.add_argument("-HC+","--forbidHCplus",action='store_true', help="forbid plane Hamiltonian subgraphs on 2n-3 edges")
parser.add_argument("-HC++","--forbidHCplusplus",action='store_true', help="assume that not every plane Hamiltonian cycle can be extended to a plane Hamiltonian subgraph on 2n-3 edges")

parser.add_argument("-HPe","--forbidHPedge",action='store_true', help="assume that for one edge there is no plane Hamiltonian path")

parser.add_argument("-HT+","--HoffmannTothplus",type=int, help="check strengthened Hoffmann-Toth property")

parser.add_argument("--forbidAllPairsHP",action='store_true', help="assume that for a pair of vertices there is no plane Hamiltonian path")

parser.add_argument("--emptycycles",type=int,help="forbid empty cycles of specified size")


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


parser.add_argument("--use_rs_vars","-R",action='store_true', help="use variables for encoding rotations system via permutations")

parser.add_argument("-r2f","--rs2file", type=str, help="if specified, export rotation systems to this file")
parser.add_argument("-c2f","--cnf2file","-o", type=str,help="if specified, export CNF to this file")
parser.add_argument("-1","--one_to_one",action='store_true', help="one-to-one correspondence between CNF and rotation systems")
parser.add_argument("--solver", choices=['cadical', 'pycosat'], default='cadical', help="SAT solver")



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

var_ab_cross_cd_ = {(a,b,c,d):cross(a,b,c,d) for a,b,c,d in permutations(all_vertices,4)}
var_ab_cross_cd_directed_ = {(a,b,c,d):dcross(a,b,c,d) for a,b,c,d in permutations(all_vertices,4)}

def var_ab_cross_cd(*I): return var_ab_cross_cd_[I]
def var_ab_cross_cd_directed(*I): return var_ab_cross_cd_directed_[I]




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
    for subrs in [    
        [[1, 2, 3, 4], [0, 3, 4, 2], [0, 1, 4, 3], [0, 2, 4, 1], [0, 3, 2, 1]],
        [[1, 2, 3, 4], [0, 2, 3, 4], [0, 1, 4, 3], [0, 1, 2, 4], [0, 1, 3, 2]],
        [[1, 2, 3, 4], [0, 2, 4, 3], [0, 1, 3, 4], [0, 1, 4, 2], [0, 3, 1, 2]],
        [[1, 2, 3, 4], [0, 2, 3, 4], [0, 1, 3, 4], [0, 1, 2, 4], [0, 1, 2, 3]]]:
        constraints += forbid_subrs(subrs) 
        

if args.cmonotone or args.stronglycmonotone:
    assert(not args.one_to_one) # does not work due to auxiliary vertices
    print("(*) assume c-monotone")
    x = n # two auxiliary vertices to ensure (strong) c-monotonicity
    y = n+1
    assert(set(all_vertices) == set(N)|{x,y}) # others are proper vertices
    for a,b in permutations(N,2):
        constraints.append([-var_ab_cross_cd(x,a,y,b)])
    for a,b,c in permutations(N,3):
        constraints.append([-var_ab_cross_cd(x,a,b,c),-var_ab_cross_cd(y,a,b,c)])


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


if args.forbidHCplusplus:
    assert(not args.natural) 
    print ("(HC++) Assume C is a Hamiltonian cycle through 1,2,3,...n ...",len(constraints))
    perm = N
    HC_edges = [(perm[i-1],perm[i]) for i in N]
    constraints += assert_planar_subgraph(HC_edges)

    print ("(HC++) ... which cannot be extended to a plane Hamiltonian subgraph on 2n-3 edges",len(constraints))
    remaining_edges = [(a,b) for (a,b) in combinations(N,2) if (a,b) not in HC_edges and (b,a) not in HC_edges]
    for E in combinations(remaining_edges,n-3):
        constraints += forbid_planar_subgraph(HC_edges+list(E))


if args.forbidHPedge:
    assert(not args.lexmin)
    print ("(HPe) for one edge there is no plane Hamiltonian path; wlog edge 01",len(constraints))
    for perm in permutations(N):
        if perm.index(1) == perm.index(0)+1:
            constraints += forbid_planar_subgraph([(perm[i-1],perm[i]) for i in range(1,n)])



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
    var_empty_cycle_select_pq_ = {(I,p,q):vpool.id() for I in permutations(N,k) for p,q in combinations(set(N)-set(I),2)}
    def var_empty_cycle_select_pq(*I): return var_empty_cycle_select_pq_[I]
    for I in permutations(N,k):
        PQ = list(combinations(set(N)-set(I),2))
        E_I = [(I[j-1],I[j]) for j in range(k)] # edges of cycle
        constraints.append(
             [+var_ab_cross_cd(*e,*f) for e,f in combinations(E_I,2) if not set(e)&set(f)]
            +[+var_empty_cycle_select_pq(I,p,q) for p,q in PQ])
        for p,q in PQ:
            for cross_indication in product([+1,-1],repeat=k):
                if (cross_indication.count(+1) % 2) == 0: 
                    # if pq is selected as witness for I not forming an empty k-cycle, 
                    # then the number of crossings of pq and E_I is odd
                    # (we forbid even counts)
                    constraints.append(
                         [-var_empty_cycle_select_pq(I,p,q)]
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
if args.crlow != None or args.crupp != None:
    crossing_vars = [var_ab_cross_cd(a,b,c,d) for (a,b,c,d) in permutations(N,4) if a<b and c<d and a<c]
    #print("crossing_vars",crossing_vars)

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

if args.forbidcrmaxk: 
    k = args.forbidcrmaxk
    print (f"(forbidcrmaxk) forbid crossingmaximal subdrawings of K_{k}")

    var_crossing_ = {I:vpool.id() for I in combinations(N,4)}
    def var_crossing(*I): return var_crossing_[I]

    for a,b,c,d in combinations(N,4):
        constraints.append([-var_crossing(a,b,c,d),+var_ab_cross_cd(a,b,c,d),+var_ab_cross_cd(a,c,b,d),+var_ab_cross_cd(a,d,b,c)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,b,c,d)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,c,b,d)])
        constraints.append([+var_crossing(a,b,c,d),-var_ab_cross_cd(a,d,b,c)])

    for I in combinations(N,k):
        constraints.append([-var_crossing(*J) for J in combinations(I,4)])


"""
if 0:
    constraints = []
    print("fix rotation system")
    RS = [[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],[0,10,11,12,13,14,9,15,7,2,3,5,4,6,8],[0,1,7,8,13,14,10,12,11,6,5,4,3,15,9],[0,1,12,7,8,13,11,10,2,14,6,5,15,4,9],[0,13,1,7,8,3,10,2,11,5,12,6,15,9,14],[0,4,1,14,3,2,7,8,10,11,12,15,9,6,13],[0,1,7,8,10,4,5,3,2,11,13,14,15,9,12],[0,5,2,3,4,6,1,10,12,11,13,14,15,9,8],[0,1,5,2,3,4,6,11,7,12,10,13,14,15,9],[0,2,3,4,6,5,8,7,15,1,10,11,12,14,13],[0,9,15,5,2,4,3,6,13,14,8,12,11,7,1],[0,9,15,6,5,4,2,10,3,13,14,7,12,8,1],[0,6,9,15,4,5,11,2,10,14,13,8,7,3,1],[0,5,9,15,12,14,6,11,10,2,3,8,7,1,4],[0,13,4,9,12,15,6,3,11,10,2,8,7,5,1],[0,10,11,14,12,13,9,2,4,3,6,5,8,7,1]]
    for a in N:
        assert(set(RS[a])|{a} == set(N))
        for I in combinations(RS[a],3):
            assert([-var_a_sees_bcd(a,*I)] not in constraints)
            constraints.append([+var_a_sees_bcd(a,*I)])
"""

print ("Total number of constraints:",len(constraints))
time_before_solving = datetime.datetime.now()
print("creating time:",time_before_solving-time_start)
print ()


if args.cnf2file:
    print ("write cnf instance to file:",args.cnf2file)

    cnf = CNF()
    for c in constraints: cnf.append(c)
    cnf.to_file(args.cnf2file)

else:

    outfile = None
    if args.rs2file:
        print ("write rotation systems to file:",args.rs2file)
        outfile = open(args.rs2file,"w")



    ct = 0
    found = []

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

    #for sol in solver.enum_models(): 
    # remark: since one-to-one correspondence between solutions of CNF and rotation systems does not work for cmonotone,
    # we decided to incrementally add clauses to prevent previous solutions
    while True:
        if args.solver == "cadical":
            if not solver.solve(): break
            sol = solver.get_model()
        else:
            sol = pycosat.solve(constraints)
            if sol == "UNSAT": break
            
        ct += 1
        sol = set(sol) # it's faster to lookup values in set than in list

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
        
        assert(rs not in found)   
        found.append(rs)
        if outfile: outfile.write(str(rs)+"\n")
        print (datetime.datetime.now(),"solution #",ct,"\t",rs)    

        if not args.all: 
            break
        else:
            # clause to prevent solutions
            if args.one_to_one:
                C = [-x for x in sol]
            else:
                C = []
                for a in N:
                    for b,c,d in combinations(N_without[a],3):
                        if b != N_without[a][0]: continue # this is sufficient  
                        v = var_a_sees_bcd(a,b,c,d)
                        C.append(v*(-1 if v in sol else +1))
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


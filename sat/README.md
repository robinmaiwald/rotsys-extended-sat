This repository contains supplemental material to the article 
"Investigating Simple Drawings of $K_n$ using SAT"


# Installation

To run the framework `pysat` needs to be installed, 
see https://pysathq.github.io/installation/

Optional: 

- `cadical`: https://github.com/arminbiere/cadical 

- `drat-trim`: https://github.com/marijnheule/drat-trim

- `SageMath`: https://www.sagemath.org/




#  Overall Description

The python program `rotsys.py` comes with a mandatory parameter `n` for the number of vertices and several optional parameters.
The program creates a SAT instance (CNF)
and then uses the Python interfaces `pycosat`  and  `PySAT` to run the
SAT solver `PicoSAT`, version 965, and `CaDiCaL`, version 1.5.3, respectively.
As default, we use the solver CaDiCaL because as it is more efficient.
The output of the program is then either a rotation system with the desired properties 
(which is obtained from parsing the variable assignment of a solution to the instance) 
or, if the instance is unsatisfiable, it prints that no solution exists.
In the case the instance has various solutions,
one can use `-a` to enumerate all solutions.

In the case the instance is unsatisfiable, 
we can ask the solver for a certificate and use the independent proof checking tool `DRAT-trim` to verify its correctness.
More specifically,
we can use the parameter `-o` to export the CNF to a specified file, which has the DIMACS file format.
By running

```
    cadical -q --unsat instance.cnf instance.proof
```
CaDiCaL exports a DRAT proof which certificates the unsatisfiability.
The correctness of the DRAT proof can then be verified with 

```
    drat-trim instance.cnf instance.proof -t 999999
```
Note that the parameter `-t` increases the time limit for DRAT-trim,
which is quite low by default.

In the following, 
we will only describe how to use the program `rotsys.py`
with its parameters. 




# Parameters 

- `n`: number of elements (mandatory)

- `-a` or `--all`: enumerate all configurations

- `-l`, `-lex` or `--lexmin`: symmetry breaking w.r.t. relabeling+mirroring

- `-c` or `--convex`: restrict to convex

- `-hc` or `--hconvex`: restrict to h-convex

- `-cm` or `--cmonotone`: restrict to circularly monotone

- `-scm` or `--stronglycmonotone`: restrict to strongly circularly monotone

- `-gt` or `--gtwisted`: restrict to generalized twisted

- `-crmax` or `--crossingmaximal`: force crossingmaximal drawing

- `-nat` or `--natural`: remove assumption that the rotation system is natural (enabled by default, use parameter to disable)

- `-v4` or `--valid4tuples`: remove assumption that 4-tuples are valid (enabled by default, use parameter to disable)

- `-v5` or `--valid5tuples`: remove assumption that 5-tuples are valid (enabled by default, use parameter to disable)

- `-HC` or `--forbidHC`: forbid plane Hamiltonian cycles (Ralfa's conjecture)

- `-HC+` or `--forbidHCplus`: forbid plane Hamiltonian subgraphs on 2n-3 edges

- `-HT+` or `--HoffmannTothplus`: check strengthened Hoffmann-Toth property, i.e. a matching which is not crossed by a Hamiltonian cycle

- `--forbidAllPairsHP`: assume that for a pair of vertices there is no plane Hamiltonian path

- `--emptycycles k`: forbid empty $k$-cycles 

- `-aec`: assert that all edges are crossed

- `-aecsub` or `--alledgescrossedsub`: assert that for every $k \le n$, all edges are crossed in the subdrawing induced by $1,\ldots,k$

- `-crf k` or `--crossingfamily k`:forbid crossing family of size $k$

- `-C k` or `--forbidCk k`: forbid the perfect convex $C_k$

- `-T k` or `--forbidTk k`: forbid the perfect twisted $T_k$

- `-X k` or `--forbidcrmaxk k`: forbid crossingmaximal subdrawings of $K_k$

- `-etlow k`: number of empty triangles is at least $k$

- `-etupp k`: number of empty triangles is at most $k$

- `-crlow k`: number of crossings is at least $k$

- `-crupp k`: number of crossings is at most $k$

- `-R` or `--use_rs_vars`: use variables for encoding rotations system via permutations

- `-o` or `--rs2file`: write rotation systems to this file

- `-c2f` or `--cnf2file` or `-o`: write CNF in DIMACS form to this file

- `--solver`: which SAT solver to use, default: cadical, alternative: pycosat

- `-1` or `--one_to_one`: most encodings come with a one-to-one correspondence between CNF and rotation systems, that is, all auxiliary variables are well-defined. this flag can be used to detect duplicates

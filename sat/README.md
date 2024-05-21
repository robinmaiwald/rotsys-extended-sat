This repository contains supplemental material to the article 
"Investigating Simple Drawings of $K_n$ using SAT"
by Helena Bergold and Manfred Scheucher



# Installation

To run the framework `pysat` needs to be installed, 
see https://pysathq.github.io/installation/

Optional: 
- `cadical` https://github.com/arminbiere/cadical 
- `drat-trim` https://github.com/marijnheule/drat-trim
- `SageMath` https://www.sagemath.org/



# Parameters 

- `-n`: number of elements

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

- `-HT+` or `--HoffmannTothplus`: check strengthened Hoffmann-Toth property

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

- `-1` or `--one_to_one`: most encodings come with a one-to-one correspondence between CNF and rotation systems. this flag can be used to detect duplicates





#  Overall Description

We provide the source code and many examples as supplemental data.

The python program `rotsys.py` comes with a mandatory parameter `n` for the number of vertices and several optional parameters.
The program creates a SAT instance
and then uses the Python interfaces `pycosat`  and  `PySAT` to run the
SAT solver `PicoSAT`, version 965, and `CaDiCaL`, version 1.5.3, respectively.
As default, we use the solver CaDiCaL because it is more efficient.
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
to show certain statements and
omit the explicit commands to certifying unsatisfiability.





# Characterization of Rotation Systems

To enumerate all $\obstructionFour$-free pre-rotation systems on 5 vertices
and test that any two
that are not obtained via reflection
have distinct pairs of crossing edges,
run the following command:
```
    python rotsys.py 5 -v5 -a -nat -cpc
```
Here the parameters have the following purposes:

- The first parameter specifies the number of vertices $n=5$.
    
- By default, the program excludes the three obstruction $\obstructionFour$, $\obstructionconvexFiveA$ and $\obstructionconvexFiveB$.
    The parameter `-v5` specifies that 
    the obstructions $\obstructionconvexFiveA$ and $\obstructionconvexFiveB$ are not excluded
    (only $\obstructionFour$ is excluded).
    Hence, the solutions are all $\obstructionFour$-free pre-rotation systems.
    
- The parameter `-a` specifies that 
    all solutions should be enumerated.
    
- By default, the program only searches for (pre-)rotation systems with natural labeling.
    The parameter `-nat` specifies that 
    we also search for solutions which are not naturally labeled.
    
- The parameter `-cpc` specifies that 
    the pairs of crossing edges should be checked:
    any two rotation systems (not obtained via reflection)
    have distinct crossing pairs. 






## Alternative proof of the proposition

The SAT frameworks from Section~\ref{sec:encoding}
and from Section~\ref{sec:drawing}
can be combined to verify the correctness of Proposition~\ref{proposition:rotsys_classification_n6},
which classifies drawable pre-rotation systems on 4, 5, and 6 vertices from Abrego et al.

As a first step, we use
the SAT framework to enumerate the
3 non-isomorphic pre-rotation systems on 4 elements:
```
    python rotsys.py -a -l -v4 4
```
Here the parameters are as follows:

- `-v4` do not exclude the obstruction $\obstructionFour$ as a subconfiguration;
- `-a` enumerate all solutions;
- `-l` only enumerate lexicographically minimal (pre-)rotation systems.

It is well known (a simple case distinction shows)
that $K_4$ has exactly two non-isomorphic drawings with 0 and 1 crossings, respectively,
which are illustrated in Figure~\ref{fig:rs_n4_valid}.
Therefore exactly the two corresponding rotation systems are realizable.
The third pre-rotation system, which is the obstruction~$\obstructionFour$ depicted in Figure~\ref{fig:rotsys_obstructions}, is not drawable.

Next, we use the framework to enumerate 
7 non-isomorphic pre-rotation systems on 5 elements,
which do not contain~$\obstructionFour$:
```
    python rotsys.py -a -l -v5 5 -o all5.json0
```
Here the parameter `-v5` is used to not exclude the obstructions $\obstructionFiveA$ and $\obstructionFiveB$ as subconfigurations,
and `-o` is used to export all solutions to the specified file. 
Then we use the drawing framework to verify 
that five of them are drawable (see Figure~\ref{fig:computer_vis_5})
and that the
two configurations to~$\obstructionFiveA$ and~$\obstructionFiveB$ (see Figure~\ref{fig:rotsys_obstructions}) are non-drawable:
```
    sage rotsys_draw.sage all5.json0
```
We ran the program `rotsys_draw.sage`
with SageMath version 9.4.
The first parameter specifies the input file,
where each line encodes a rotation system.
To visualize the computed planarizations 
%(as outlined in Section~\ref{sec:discussion}) % \manfred{das zeichenprogramm könnte man in full version erklären}
and create image files,
one can use the optional \verb|-v| parameter.

The case distinction needed to show that $\obstructionFiveA$
and~$\obstructionFiveB$ are non-drawable can also be done by hand.

Finally, 
we use the framework to enumerate 
102 non-isomorphic pre-rotation systems on 6 elements,
which do not contain~$\obstructionFour$, $\obstructionFiveA$, and~$\obstructionFiveB$:
\begin{verbatim}
    python rotsys.py -a -l 6 -o all6.json0
\end{verbatim}
Then we use the drawing framework to verify 
that all of them are drawable:
\begin{verbatim}
    sage rotsys_draw.sage all6.json0
\end{verbatim}
This completes the proof of Proposition~\ref{proposition:rotsys_classification_n6}.
%\end{proof}






\subsection{Plane Hamiltonian substructures}
\label{plane_substructures}

\paragraph{Rafla's conjecture (Conjecture~\ref{conjecture:rafla})}

To verify that Conjecture~\ref{conjecture:rafla} holds for $n \le 10$,  
we used the Python program with the following parameters:
\begin{verbatim}
    for n in {3..10}; do 
        python rotsys.py -HC $n
    done
\end{verbatim}
The parameter \verb| -HC| asserts that there exists no plane Hamiltonian cycle.
Using the solver CaDiCaL,
it took about 6 CPU days to show unsatisfiability.
Furthermore, we created DRAT certificates. 
The certificate for $n=10$ is about 78GB and 
the verification with DRAT-trim took about 6 CPU days.
The resources used for $n \le 9$ are negligible.


\paragraph{Plane Hamiltonian subdrawing of $2n-3$ edges (Conjecture~\ref{conjecture:rafla_2n_plus_3})}

To verify that Conjecture~\ref{conjecture:rafla_2n_plus_3} holds
for $n \le 8$, 
we ran
\begin{verbatim}
    for n in {3..10}; do 
        python rotsys.py -HC+ $n 
    done
\end{verbatim}
Here the parameter \verb| -HC+| asserts that there is no plane Hamiltonian subdrawing on $2n-3$ edges. 
In the so-created instance, solutions correspond to rotation systems on $[n]$ which do not contain any plane Hamiltonian subdrawing of $2n-3$ edges.
Using the solver CaDiCaL,
it took about 3 CPU days to show unsatisfiability.
Moreover, the verification with DRAT-trim took about 3 CPU days.


\paragraph{Extension of plane Hamiltonian cycles (Conjecture~\ref{conjecture:extend_HC_to_2n_3})}

To verify that Conjecture~\ref{conjecture:extend_HC_to_2n_3} holds for $n\le 10$,
run
\begin{verbatim}
    for n in {3..10}; do 
        python rotsys.py -HC++ -nat -c $n 
    done
\end{verbatim}
Here the parameter \verb| -HC++| asserts that there is a plane Hamiltonian cycle $C$
that cannot be extended to a plane Hamiltonian subdrawing on $2n-3$ edges. 
Note that, since we assume that $C$ traverses $1,2,\ldots,n$ in this order,
we cannot assume natural labeling. 
Therefore, we have to use the \verb|-nat| parameter 
which allows the framework to also consider rotation systems 
which are not natural.  
Using the solver CaDiCaL,
it took about 2 CPU days to show unsatisfiability.
Moreover, the verification with DRAT-trim took about 2 CPU days.



\paragraph{Hamiltonian cycles avoiding a matching (Conjecture~\ref{conjecture:hoffmanntoth_convex})}

To verify that Conjecture~\ref{conjecture:hoffmanntoth_convex} holds for $n \le 11$
run
\begin{verbatim}
    for n in {4..11}; do
        for (( k = 1; 2*k <= n; k++ )); do
            python rotsys.py $n -c -nat -HT+ $k
        done
    done
\end{verbatim}
With the parameter \verb|-HT+ k| we
assume towards a contradiction that there exists a convex drawing of $K_n$ 
which has a plane matching $M=\{1,2\},\ldots,\{2k-1,2k\}$
such that for every plane Hamiltonian cycle $C$ crosses edges of $M$,
that is, $C \cup M$ (not necessarily disjoint union) is non-plane.
Note that for $k \ge 2$ we cannot assume without loss of generality that the rotation system is natural, that is, $1$ sees $2,3,\ldots,n$ in this order.
To optimize the encoding and to speed up the computations, 
observe that
we can assume without loss of generality that 
\begin{itemize}
    \item
    $1$ sees $2,u,v$ for every edge $\{u,v\} \in M$ with $u<v$,
    \item $1$ sees $2,u,v'$ for every two edges  $\{u,v\},\{u',u'\} \in M$ with $u<v$, $u'<v'$ and $u<u'$,
    \item $1$ sees $2,x,y$ for every $x,y \in [n] \setminus V(M)$ with $x<y$. 
\end{itemize}

Using the solver CaDiCaL,
the computations for $n \le 11$ took about 12 CPU days. Moreover, the certification with DRAT-trim took about 12 CPU days.
%Also the case $n=12,k=1$ can be verified within 42 cpu days.



\subsection{Uncrossed edges}
\label{uncrossed}

To verify that every rotation system on $n=7$ contains an uncrossed edge, use the following command: 
\begin{verbatim}
    for n in {4,5,6,7}; do
        python rotsys.py -aec $n 
    done
\end{verbatim}

To find a rotation system on $n=8$ which does not contain an uncrossed edge, use the following command:
\begin{verbatim}
    python rotsys.py -aec 8 
\end{verbatim}

To restrict to convex (resp.\ $h$-convex) drawings one needs to add the additional parameter \verb| -c | (resp.\ \verb|-hc|).
We provide $h$-convex rotation systems that verify Conjecture~\ref{conjecture:hconvex_aec} for $n \le 21$ 
as supplemental files in the folder 
\verb|examples/all_edges_crossing/|.



\iffalse %\manfred{comment in for final version?}
\subsection{Quasiplanarity and crossing families}
\label{crossingfamily}

To verify that 
every drawing of $K_{11}$ contains a 3-crossing family, run
\begin{verbatim}
    python rotsys.py -crf 3 11
\end{verbatim}
The computations took about 3 CPU hours.
To find an $h$-convex drawings of $K_{10}$ without 3-crossing families, run
\begin{verbatim}
    python rotsys.py -crf 3 -hc 10
\end{verbatim}

To find an $h$-convex drawing of $K_{16}$ without 4-crossing families, run
\begin{verbatim}
    python rotsys.py -hc -crf 4 16
\end{verbatim}
Since this computation took about 1 CPU day,
we provide this example
as supplemental files in the folder \verb|examples/crossing_families/|.
\fi



\subsection{Empty triangles}
\label{emptytriangles}

To search for a drawing with at most $k$ empty triangles,
we used \linebreak \verb|pysat.card.CardEnc.atmost| 
from PySAT \cite{pysat}.
This method creates constraints for a CNF
that assert that among a given set of variables 
(here we use the $\triangle$ variables)
at most $k$ are $true$.

To verify that $2n-4$ is a tight lower bound on the number of triangles for $n \le 9$, use:
\begin{verbatim}
    for n in {4..9}; do 
        python rotsys.py -etupp $((2*$n-5)) $n
    done
\end{verbatim}
Here the parameter \verb|-etupp k| asserts that the number of empty triangles is at most~$k$. Since all instances are unsatisfiable for $k=2n-5$,
it follows $\triangle \ge 2n-4$.

We provide the examples as supplemental files in 
`examples/empty_triangles`.
































## Enumerating the settings

The following command performs the enumeration of all 
families $\mathcal{F}$ of rank 3 sign patterns on $[4]$
with $`\mathcal{F} \subseteq \{+-+-,+--+,+---,-+-+,-+--,--+-,---+,----\}`$
and writes all settings to the file `r3_settings.txt`.
Each line in the file encodes a setting.
```
    python enum_settings.py 3 > r3_settings.txt
```
Since among the $256 = 2^8$ subsets there are some symmetries,
our program filters out 144 that are lexicographically minimal
with respect to 

- inverting signs (i.e., changing $+$ to $-$ and vice versa) and
- reversing the elements $`\{1,\ldots,n\}`$ to $`\{n,\ldots,1\}`$.

Note that there might be other symmetries among the classes.

Similarly, one can enumerate all settings for rank 4 using
```
    python enum_settings.py 4 > r4_settings.txt
```
Note that this will take several cpu days.
The benchmark selection, however, can be enumerated almost instantly using 
```
    python enum_settings.py 4 --selection > r4_settings_selection.txt
```


## Duplicate checking

To check whether a file only contains non-isomorphic settings,
we provide a script `count_configurations.py`
which uses a model counting implementation from KCBox 
to count all configurations up to a certain number of elements $n$ for each setting.
To verify that the 41 settings in `r3_settings_hard.txt` are non-isomorphic, 
it is sufficient to use $n=6$ as all settings yield different numbers:
```
    python count_configurations.py r3_settings_hard.txt 3 6
```


## Testing completability

The script loads settings from an input file
and for each setting it searches gadgets for the reduction. 
If the script terminates unsuccessfully for a setting, 
then there are no gadget of the specified size.
If the script finds enough gadgets for a reduction, 
it creates a certificate in the `certificates_r{rank}_{algorithm}/` folder
which verifies that the setting NP-hard.
By re-running the script, an existing certificate will be reloaded and verified to save time.


For example, the following command searches gadgets of size 5 
for all rank 3 settings encoded in the file `r3_settings_all.txt`:
```
    python find_gadgets.py r3_settings_all.txt 3 5
```
As outlined in our paper, the computation only takes a few CPU minutes on a single CPU
to classify 31 of the 144 settings as hard.
To search all structures for gadgets of size 6 in the remaining settings, 
we used the computing cluster at TU Berlin.
Even though finding gadgets is a non-trivial task, 
pre-computed gadgets can be verified within a few seconds with by following command:
```
    python find_gadgets.py r3_settings_all.txt 3 6 --load -cp certificates_r3/ --verifyonly
```
Our certificates are provided in `certificates_r3.tar.gz` and `certificates_r4.tar.gz`.

To exclude errors from the SAT solver, one can also run
```
    python find_gadgets.py r3_settings_all.txt 3 6 --load -cp certificates_r3/ --verifyonly --verifydrat
```
This will check the correctness of a model in the case a CNF is satisfiable,
and otherwise, if the CNF is unsatisfiablitiy,
it will use cadidal to create a DRAT certificate and 
employ the independent proof-checking tool DRAT-trim to verify the certificate.



## Certificates

A certificate is text file which encodes a python dictionary with the following entries:

- `n` encodes the size of the gadget.

- `fpatterns` encodes the setting as a list of forbidden patterns, e.g., `['+-+-', '-+-+']`.

- `pgadgets` holds a sub-dictionary which encodes up to 4 propagator gadgets.
The keys are strings such as `'A or not B'` and encode
the Boolean formulas corresponding to the gadgets.

- `cgadgets` holds a sub-dictionary which encodes up to 8 clause gadgets. 
The keys are strings such as `'A or not B or C'` and encode
the Boolean formulas corresponding to the gadgets.


Each gadgets is encoded by the triple:

- Size of the gadgets as integer.
Note that, in our python code, 
sign mappings are on the elements $`\{0,\ldots,n-1\}`$.

- The sign mapping encoded as string. 
For example, `?+-?` encodes the mapping
$\sigma(013)=+,\sigma(023)=-$ on the elements $`\{0,1,2,3\}`$.

- The location of the variables in the gadget.
For example `(0, 1, 2), (1, 2, 3)` encodes that the first variable $A$ is encoded in the triple $(0, 1, 2)$ and the second variable $B$ is encoded in the triple $(1, 2, 3)$.


To give a concrete example:
the NP-hardness certificate for the setting of generalized signotopes (i.e., $`\mathcal{F} = \{+-+-,-+-+\}`$) looks as follows:
```
{
    'n': 5,
    'fpatterns': ['+-+-', '-+-+'], 
    `pgadgets`: {
        'A or B': (5, '??++-?+?+?', ((0, 1, 2), (2, 3, 4))), 
        'A or not B': (4, '?+-?', ((0, 1, 2), (1, 2, 3))), 
        'not A or B': (4, '?-+?', ((0, 1, 2), (1, 2, 3))), 
        'not A or not B': (5, '??-++?-?-?', ((0, 1, 2), (2, 3, 4)))
    }, 
    `cgadgets`: {
        'A or not B or C': (5, '??+--???+?', ((0, 1, 2), (1, 2, 3), (2, 3, 4)))
    }
}
```

python rafla.py -HC 7 --cnf2file test.cnf --var2file test.var
# create CNF and variables file

cadical test.cnf --no-binary test.proof -t 1 -q 
# create partial proof, "-t 1" termination after 1 second, "-q" for quiet mode

python satify/verify.py test.cnf test.proof test.inccnf --var test.var
# creates an incremental cnf by appending all learned clauses from the proof to the original cnf

cadical merge.inccnf -q
# verify learned clauses in the inccnf
# each clause is treated as cube
# and the cubes are all "UNSAT" if everything is fine
# (only invalid clauses/cubes would give "SAT")
# SATsolver
(Assignment for Course CS202: Logic for Computer Science under Prof Subhajit Roy)
Implementation of SAT solver using improvised semantic tableaux and Davis–Putnam–Logemann–Loveland (DPLL) algorithm.

Source Code Dependencies
------------------------
The code has a strict dependency on C++ 2017 standard. No other dependencies as such.

Input
------
The input file "sat.txt" should be placed in the same folder as the source code. The input file must be in DIMACS format without any comments. There shan't be any conflicting number of variables.

Output
-------
The output will consist of four parts:
1. SATISFIABLE or UNSAT
2. A model if the formulae is SATISFIABLE
3. Execution time in seconds

Heuristics
-------
We have applied the following heuristics:
1. Repeated Unit Propagation: Unit propagation is a procedure of automated theorem that can simplify a set of (usually propositional) clauses. We look out for unit clauses throughout the set of clauses. In our method, we follow repeated unit propagation i.e we follow the same process of eliminating unit clauses until we are left with no unit clauses. If the literal 'a' is present in any unit clause, we eliminate all the clauses containing 'a' and reduce the size of all the literals containing '-a' by eliminating '-a'. It is entirely based on the fact that a unit clause must be true in order to satisfy the formulae.
2. Pure Literals: They are the literals that for which their negation is not present in any of the clauses. They can be assumed to be true and then all the clauses containing 'a' can be deleted and all the clauses '-a' can be reduced by in size by eliminating '-a'.
3. Maximum Occurrence: We proceed in solving by removing a literal with maximum occurrence. It will be useful since will reduce the size of maximum number of clauses. In this way, maximum clauses got their sizes reduced. Therefore, we get to the satisfiable set of clauses more quickly by reducing sizes more quickly. This heuristic, though powerful comes at the cost of checking all clauses and does not receives a good feedback from sudoku encoding.
4. Removal of Tautologies: They are the clauses which contain literals of the form 'a' and '-a'. They have to be true due to binary nature of a proposition.
5. Elimination of singular clauses: They are the clauses with only one literal. Say, the literal present in the clause is 'a'. Then, 'a' would be asserted 'TRUE' and all the clauses containing 'a' would be eliminated. Now the literals '-a' are 'FALSE'. Therefore, they are eliminated from each and every clause.



Compile and Run
---------------
```bash
g++ -std=c++17 SatSolver.cpp
./a.out
```

Documentation references and Further Reading
------------------------
- https://en.wikipedia.org/wiki/Unit_propagation
- http://studentnet.cs.manchester.ac.uk/resources/library/3rd-year-projects/2015/rebecca.doran.pdf
- https://en.wikipedia.org/wiki/Boolean_satisfiability_algorithm_heuristics

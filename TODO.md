#TODO

------

### In progress
1. Luca -> UI with Jupyter.

### Not in progress
1. Save abstract synthesis problem in TLSF file rather than command line (with large enough predicate set or program the LTL formula may become too big for the command line).
2. Incorporate ranking functions.
3. More examples.
4. Interface for CVC5 interpolation (then try to choose `best' interpolant, e.g., if we get an interpolant that is equivalent to something we already have, ask CVC5 for the next one instead).
5. Make the predicate abstraction incremental.
   1. Use the incremental meaning_within
   2. See if we can find an SMT solver that can keep the SMT context (?) of each transition in the previous transition, so that then we just need to evaluate the new information against the old context, rather than creating a totally new instance of the problem.
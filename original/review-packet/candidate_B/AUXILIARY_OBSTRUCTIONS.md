# Candidate B: counterexample to a broader auxiliary claim



Let T_k f=(1+kx)f+x(1-x)f', and set

\[
h=(x+1)^{10},\quad F=T_{11}h,\quad G=T_{12}F,\quad H=T_{13}G.
\]

Although h is reciprocal and real-rooted, the boundary parameters b=4,c=11 give

\[
H+4G+11F=(x+1)^7S(x),
\]

where

\[
S=x^6+158x^5+3206x^4+13796x^3+5657x^2+686x+16.
\]

S is square-free. Its Sturm signs at -infinity are (+,-,+,-,+,-,-), with 5 variations; at +infinity they are (+,+,+,+,+,+,-), with 1 variation. Therefore S has exactly 4 real roots, and the degree-13 product has only 11 real roots with multiplicities. The full primitive integer Sturm chain is retained in `counterexample_search/one_step_counterexample.json`.

**This is a counterexample to an auxiliary preservation claim, not to the user's Eulerian conjecture.** Here F,G,H are not consecutive Eulerian polynomials.

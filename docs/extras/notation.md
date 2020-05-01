when deciding how to pretty-print an expression,
Lean looks up the notations associated to the head of the expression (e.g. `finset.sum`).
It tries them one by one, until it finds a notation that matches the expression,
then uses that to pretty-print.
The order in which they are tried is the order in which they are stored in the environment structure,
which in this case is the order in which they are defined.
Apparently the priority information is thrown away
(typically it would be highest-priority first, then by order of definition).
This is why the order matters.

A notation definition is associated to the head of the expression it expands to, so
```lean
notation ∑ binders ,  r:(scoped f, finset.sum finset.univ f) := r
```
is associated to the head of the expansion of `r`,
which is the head of `finset.sum finset.univ f`, which is `finset.sum`.
But `finset.univ.sum` doesn't get expanded to `finset.sum finset.univ` at that point,
so you have to write `finset.sum finset.univ` instead of `finset.univ.sum`.

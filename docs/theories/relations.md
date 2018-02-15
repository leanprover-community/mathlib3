# Maths in Lean : Relations on types

Right at the end of the file `init/logic.lean` in core lean, there are
definitions of the basic relations on types such as `reflexive`,
`irreflexive`, `symmetric`, `anti_symmetric`, `transitive`,
`equivalence`, and `total` (i.e. for all `x` and `y`,
`x R y` or `y R x`).
One key usage of equivalence relations is the construction of
equivalence classes; this is well documented in 
[Theorem Proving In Lean](https://leanprover.github.io/theorem_proving_in_lean/).

### Examples.

```lean
variable (X : Type*)

-- equality is symmetric
example : symmetric (λ x y : X, x=y) := 
λ x y, eq.symm

-- "less than" is transitive on the natural numbers.
example : transitive (λ a b : nat, a<b) := 
λ x y z : nat, lt_trans
```

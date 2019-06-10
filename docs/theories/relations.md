# Maths in Lean : Relations on types

Right at the end of the file `init/logic.lean` in core lean, there are
definitions of the basic relations on types such as `reflexive`,
`irreflexive`, `symmetric`, `anti_symmetric`, `transitive`,
`equivalence`, and `total` (i.e. for all `x` and `y`,
`x R y` or `y R x`).

### Examples.

```lean
variable (X : Type*)

-- equality is symmetric
example : symmetric (λ x y : X, x = y) := 
λ x y, eq.symm

-- "less than" is transitive on the natural numbers.
example : transitive (λ a b : ℕ, a < b) := 
λ x y z : ℕ, lt_trans
```

Transitivity of relations allows to use them in [calc environments](../extras/calc.md).

One key usage of equivalence relations is the construction of quotients.
A type with an equivalence relation on it is called a `setoid` in Lean.
Setoids are defined in `init/data/setoid.lean` and the quotient type
corresponding to the equivalence classes of the equivalence relation is
defined in `init/data/quot.lean` . The online document 
*Theorem Proving In Lean* has 
[quite a good section about setoids and quotients](https://leanprover.github.io/theorem_proving_in_lean/axioms_and_computation.html#quotients)

A nice mathematical example can be found in `linear_algebra/quotient_module`.

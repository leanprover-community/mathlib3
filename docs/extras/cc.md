# The congruence closure tactic

The congruence closure tactic  tries to solve the goal by chaining
equalities from context and applying congruence (ie if `a = b` then `f a = f b`). 
It is a finishing tactic, ie is meant to close
the current goal, not to make some inconclusive progress.
A mostly trivial example would be:

```lean
example (a b c : ℕ) (f : ℕ → ℕ) (h: a = b) (h' : b = c) : f a = f c := by cc
```

As an example requiring some thinking to do by hand, consider:

```lean
example (f : ℕ → ℕ) (x : ℕ)
  (H1 : f (f (f x)) = x) (H2 : f (f (f (f (f x)))) = x) :
  f x = x :=
by cc
```

The tactic works by building an equality matching graph. It's a graph where
the vertices are terms and they are linked by edges if they are known to
be equal. Once you've added all the equalities in your context, you take
the transitive closure of the graph and, for each connected component
(i.e. equivalence class) you can elect a term that will represent the
whole class and store proofs that the other elements are equal to it.
You then take the transitive closure of these equalities under the
congruence lemmas.

The `cc` implementation in Lean does a few more tricks: for example it
derives `a=b` from `nat.succ a = nat.succ b`, and `nat.succ a !=
nat.zero` for any `a`.

### References

* The starting point is Nelson, Oppen, [Fast decision procedures based on congruence closure](http://www.cs.colorado.edu/~bec/courses/csci5535-s09/reading/nelson-oppen-congruence.pdf), Journal of the ACM (1980) 

* The congruence lemmas for dependent type theory as used in Lean are described in [Congruence closure in intensional type theory](https://leanprover.github.io/papers/congr.pdf) (de Moura, Selsam IJCAR 2016).



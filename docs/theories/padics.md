# Maths in Lean : p-adic numbers

The construction of `ℝ` using Cauchy sequences of rationals can be generalized to any absolute
value on `ℚ`. For any prime p, the completion of `ℚ` with repsect to the p-adic norm creates a field
`ℚ_p` and a ring `ℤ_p`.

* `padic_norm.lean` defines the p-adic valuation `ℤ → ℕ`, extends it to `ℚ`, and defines
  `padic_norm {p} : prime p → ℚ → ℚ`. Note that this does not lead to a useful instance of
  `has_norm` since `p` cannot be inferred from the input, and it is not a norm for
  composite `p`. `padic_norm` is shown to be a non-archimedean absolute value.
* Fix `p` and `hp : prime p`. `padic_rationals.lean` defines `ℚ_[hp]` as the Cauchy completion of
  `ℚ` wrt `padic_norm hp` using the same mechanisms as `data/real/basic.lean`. It is immediately a
  field. The norm lifts to `padic_norm_e : ℚ_[hp] → ℚ`, which is cast to `ℝ` and gives us a
  `normed_field` instance. `ℚ_[hp]` is shown to be Cauchy complete.
* `padic_integers.lean` defines `ℤ_[hp]` as the subtype `{x : ℚ_[hp] \\ ∥x∥ ≤ 1}`. It instantiates
  `local_ring` and `normed_ring` and is Cauchy complete.
* `hensel.lean` proves Hensel's lemma over `ℤ_[hp]`, described by Gouvêa (1997) as the "most
  important algebraic property of the p-adic numbers." For `F : polynomial ℤ_[hp]` and `a : ℤ_[hp]`
  with `∥F.eval a∥ < ∥F.derivative.eval a∥^2`, then there exists a unique `z` such that
  `F.eval z = 0 ∧ ∥z - a∥ < ∥F.derivative.eval a∥`; furthermore,
  `∥F.derivative.eval z∥ = ∥F.derivative.eval a∥`. The proof is an adaptation of
  [a writeup by Keith Conrad](http://www.math.uconn.edu/~kconrad/blurbs/gradnumthy/hensel.pdf) and
  uses Newton's method to construct a sequence in `ℤ_[hp]` converging to the unique solution.
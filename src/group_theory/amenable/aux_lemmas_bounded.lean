/-
Copyright (c) 2022 Matthias Uschold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthias Uschold.
-/
import topology.continuous_function.bounded


/-!
# Some Lemma on boundedness

In this file, we prove that two notions of boundedness of functions (to ℝ)
are equivalent.

## Implementation Notes

TODO : These statements are probably already in the mathlib
(probably in some more general form). These lemmas may be
replaced by / moved to different parts of the mathlib.

## Tags

boundedness, bounded function


-/

lemma function_bounded_classical
  {X: Type*}
  {f: X → ℝ}
  : (∃ (C:ℝ), ∀ (x y: X), dist (f x) (f y) ≤ C )  -- The Lean definition
  ↔ (∃ (C:ℝ), ∀ (x:X), abs (f x) ≤ C )           --classical
:= begin
  split,
  {
    assume hC,
    by_cases (is_empty X),
    {
      use 0,
      assume x,
      exfalso,
      exact is_empty_iff.mp h x,
    },
    --choose an element
    let x0 : X := classical.choice (not_is_empty_iff.mp h),
    rcases hC with ⟨C, hC⟩,
    use C + |f x0|,
    assume x :X,
    calc |f x| = |(f x - f x0) + f x0|
                  : by simp
           ... ≤  |f x - f x0| + |f x0|
                  : abs_add (f x - f x0) (f x0)
           ... = dist (f x) (f x0) + |f x0|
                  : by congr'; exact real.dist_eq (f x) (f x0)
           ... ≤ C + |f x0|
                  : by linarith only [hC x x0],
  },
  {
    assume h,
    rcases h with ⟨C, hC⟩,
    use 2*C,
    assume x y :X,
    calc  dist (f x) (f y)
         = |f x - f y|
          : by exact real.dist_eq _ _
    ... ≤ |f x| + |f y|
          : abs_sub (f x) (f y)
    ... ≤ C + C
          : by linarith only [hC x, hC y]
    ... = 2 * C
          : by ring,
  }
end

lemma function_bounded_classical'
  {X: Type*}
  [topological_space X]
  (f: bounded_continuous_function X ℝ)
  : ∃ (C:ℝ), ∀ (x:X), abs (f x) ≤ C
:= function_bounded_classical.mp f.bounded

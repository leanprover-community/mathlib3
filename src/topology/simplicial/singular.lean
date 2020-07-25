/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.basic
import topology.category.Top
import topology.simplicial.pmf
import topology.simplicial.move_this

/-!
# The singular simplicial set of a topological space

## Implementation details

It may seem that there are off-by-one errors in the presentation below.
Instead of working with `n : ℕ`, we let `n` denote any
nonempty finite linearly ordered type (e.g., `fin (k+1)`).
As a consequence, objects like the singular standard simplices
are indexed by `n : NonemptyFinLinOrd` and are subspaces of `n → ℝ`,
so that what corresponds to the `k`-th standard simplex for `k : ℕ`,
is the one indexed by `fin (k+1)` and lives in `fin (k+1) → ℝ`, as it should.
-/

noncomputable theory

open category_theory

namespace Top

local attribute [instance] pmf.topological_space

/-- The functor that assigns to a nonempty finite linear order
the singular standard simplex on that order.

`singular_standard_simplex n` is the
subspace of `ℝ^n` consisting of vectors that sum to `1`
and all of whose entries are nonnegative. -/
@[simps]
def singular_standard_simplex : NonemptyFinLinOrd ⥤ Top :=
{ obj := λ n, Top.of (pmf n),
  map := λ m n α,
  { to_fun := pmf.map α,
    continuous_to_fun := pmf.map_continuous α },
  map_id' := by { intro n, ext1 x, exact pmf.map_id x, },
  map_comp' := by { intros _ _ _ f g, ext1 x, exact (pmf.map_comp x f g).symm, } }

/-- The singular simplicial type associated with a topological space `X`
has as `n`-simplices all continuous maps from `singular_standard_simplex n` to `X`. -/
def singular : Top ⥤ sType :=
yoneda ⋙ singular_standard_simplex.{0 0}.op.comp_left

end Top

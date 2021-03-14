/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.simplicial_complex
import algebra.homology.homology
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

universe variables u

open category_theory

namespace Top
open function opposite

local attribute [instance] pmf.topological_space

/-- The functor that assigns to a nonempty finite linear order
the singular standard simplex on that order.

`singular_standard_simplex n` is the
subspace of `ℝ^n` consisting of vectors that sum to `1`
and all of whose entries are nonnegative. -/
@[simps]
def singular_standard_simplex : NonemptyFinLinOrd.{u} ⥤ Top.{u} :=
{ obj := λ n, Top.of (pmf n),
  map := λ m n α,
  { to_fun := pmf.map α,
    continuous_to_fun := pmf.map_continuous α },
  map_id' := by { intro n, ext1 x, exact pmf.map_id x, },
  map_comp' := by { intros _ _ _ f g, ext1 x, exact (pmf.map_comp x f g).symm, } }

/-- The singular simplicial type associated with a topological space `X`
has as `n`-simplices all continuous maps from `singular_standard_simplex n` to `X`. -/
def singular : Top ⥤ sSet :=
yoneda ⋙ singular_standard_simplex.op.comp_left

lemma singular_map_injective (X Y : Top) :
  injective (@category_theory.functor.map _ _ _ _ singular X Y) :=
begin
  intros f g h,
  ext x,
  let v : pmf punit := ⟨_, by simpa using has_sum_fintype (λ x : punit, (1:nnreal))⟩,
  rw [nat_trans.ext_iff, funext_iff] at h,
  specialize h (op $ NonemptyFinLinOrd.of punit),
  dsimp [singular] at h,
  rw [funext_iff] at h,
  specialize h ⟨λ _, x, continuous_const⟩,
  dsimp at h,
  have H := congr_arg continuous_map.to_fun h,
  rw [funext_iff] at H,
  exact H v,
end

variables (R : Type u) [comm_ring R]

def singular_chain_complex : Top ⥤ chain_complex (Module R) :=
singular ⋙ sSet.free_simplicial_module R ⋙ (simplicial_module.simplicial_complex R)

-- def homology (i : ℤ) : Top ⥤ Module R :=
-- singular_chain_complex R ⋙ homological_complex.homology _ i

end Top

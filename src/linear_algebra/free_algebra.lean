/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.basis
import algebra.free_algebra
import linear_algebra.finsupp_vector_space
/-!
# Linear algebra properties of `free_algebra R X`

This file provides a `free_monoid X` basis on the `free_algebra R X`, and uses it to show the
dimension of the algebra is the cardinality of `list X`
-/

universe variables u v

namespace free_algebra

variables (R : Type u) (X : Type v) [comm_ring R]

/-- The `free_monoid X` basis on the `free_algebra R X`,
mapping `[x₁, x₂, ..., xₙ]` to the "monomial" `1 • x₁ * x₂ * ⋯ * xₙ` -/
@[simps]
noncomputable def basis_free_monoid:
  basis (free_monoid X) R (free_algebra R X) :=
finsupp.basis_single_one.map
  (equiv_monoid_algebra_free_monoid.symm.to_linear_equiv : _ ≃ₗ[R] free_algebra R X)

-- TODO: generalize to `X : Type v`
lemma dim_eq {K : Type u} {X : Type (max u v)} [field K] :
  module.rank K (free_algebra K X) = cardinal.mk (list X) :=
(cardinal.lift_inj.mp (basis_free_monoid K X).mk_eq_dim).symm


variables {R X}

/--
Separate an element of the free algebra into its ℕ-graded components.

This is defined as an `alg_hom` to `add_monoid_algebra` so that algebra operators can be moved
before and after the mapping.
-/
noncomputable
def grades : (free_algebra R X) →ₐ[R] add_monoid_algebra (free_algebra R X) ℕ :=
lift R $ finsupp.single 1 ∘ ι R

/-- Recombining the grades recovers the original element-/
lemma sum_id_grades :
  (add_monoid_algebra.sum_id R).comp grades = alg_hom.id R (free_algebra R X) :=
begin
  ext,
  simp [grades, add_monoid_algebra.sum_id_apply, finsupp.sum_single_index],
end

noncomputable
instance : has_coe (add_monoid_algebra (free_algebra R X) ℕ) (free_algebra R X) := ⟨
  (add_monoid_algebra.sum_id R : add_monoid_algebra (free_algebra R X) ℕ →ₐ[R] (free_algebra R X))
⟩

@[simp, norm_cast]
lemma coe_def (x : add_monoid_algebra (free_algebra R X) ℕ) : (x : free_algebra R X) = add_monoid_algebra.sum_id R x := rfl


/-- An element of `R` lifted with `algebra_map` has a single grade 0 element -/
lemma grades.map_algebra_map (r : R) :
  grades (algebra_map R (free_algebra R X) r) = finsupp.single 0 (algebra_map R _ r) :=
by simp

/-- An element of `X` lifted with the canonical `ι R` function has a single grade 1 element -/
lemma grades.map_ι (x : X) :
  grades (ι R x) = finsupp.single 1 (ι R x) :=
by simp [grades]

-- note this is true for any `zero_hom`, not just `grades`. Of course, then we need to repeat this
-- for `add_monoid_hom`, `add_equiv`, `linear_map`, `ring_hom`, `ring_equiv`, `alg_hom`, ...
private lemma map_single_apply (x : free_algebra R X) (i j : ℕ) :
  grades (finsupp.single i x j) = finsupp.single i (grades x) j :=
by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades, grades.map_zero]

/-- The grade-`i` part consists only of itself -/
@[simp]
lemma grades.map_grades (x : free_algebra R X) (i : ℕ) :
  grades (grades x i) = finsupp.single i (grades x i) :=
begin
  induction x using free_algebra.induction generalizing i,
  case h_grade0 : {
    rw [grades.map_algebra_map, map_single_apply, grades.map_algebra_map,
      finsupp.single_of_single_apply],
  },
  case h_grade1 : {
    rw [grades.map_ι, map_single_apply, grades.map_ι,
      finsupp.single_of_single_apply],
  },
  case h_add : x y hx hy {
    rw [grades.map_add, finsupp.add_apply, grades.map_add, finsupp.single_add, hx, hy],
  },
  case h_mul : f g hx hy {
    rw grades.map_mul,
    rw add_monoid_algebra.mul_def,
    simp_rw [finsupp.sum_apply],

    -- pull the sums to the outside
    have : finsupp.single i = finsupp.single_add_hom i := rfl,
    rw this,
    simp_rw alg_hom.map_finsupp_sum,
    simp_rw add_monoid_hom.map_finsupp_sum,
    simp_rw finsupp.sum,
    congr, ext1 fi,
    congr, ext1 gi,
    rw ←this,

    -- this proof now resembles the other three
    rw [map_single_apply, grades.map_mul,
      finsupp.single_of_single_apply],
    rw [hx, hy, add_monoid_algebra.single_mul_single],
  },
end

end free_algebra

/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import linear_algebra.basis
import algebra.free_algebra
import linear_algebra.finsupp_vector_space
import algebra.direct_sum.algebra
import algebra.algebra.operations

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


open_locale direct_sum

variables (R X)

/-- The submodule produced by weighted sums of single generators. -/
abbreviation ι_submodule (i : ℕ) : submodule R (free_algebra R X) :=
(submodule.span R (set.range $ ι R)) ^ i

variables {X}

lemma ι_mem_ι_submodule_one (x : X) : ι R x ∈ ι_submodule R X 1 :=
begin
  dunfold ι_submodule,
  rw pow_one,
  exact submodule.subset_span (set.mem_range_self x),
end

variables {R X}

/-- Assemble an element of the free algebra from its per-grade pieces. -/
def of_grades : (⨁ i : ℕ, ι_submodule R X i) →ₐ[R] free_algebra R X :=
direct_sum.to_algebra R _ (λ i, submodule.subtype _) rfl (λ _ _ _ _, rfl) (λ r, rfl)

@[simp]
lemma of_grades_of {i : ℕ} (x : ι_submodule R X i) :
  of_grades (direct_sum.of (λ i, ι_submodule R X i) i x) = x :=
direct_sum.to_add_monoid_of _ _ _

/--
Separate an element of the free algebra into its ℕ-graded components.

This is defined as an `alg_hom` to a direct sum of submodules so that algebra operators can be
moved before and after the mapping.
-/
def grades : free_algebra R X →ₐ[R] ⨁ i : ℕ, ι_submodule R X i :=
lift R $ λ x, direct_sum.of (λ i, ι_submodule R X i) 1 ⟨ι R x, ι_mem_ι_submodule_one R x⟩

@[simp] lemma grades_ι (x : X) :
  grades (ι R x) = direct_sum.of (λ i, ι_submodule R X i) 1 ⟨ι R x, ι_mem_ι_submodule_one R x⟩ :=
lift_ι_apply _ _

/-- `of_*` is the left-inverse of `to_*` -/
lemma of_grades_comp_grades : of_grades.comp grades = alg_hom.id R (free_algebra R X) :=
begin
  ext : 2,
  dsimp,
  rw [grades_ι, of_grades_of, subtype.coe_mk],
end

@[simp] lemma of_grades_grades (x : free_algebra R X) : of_grades (grades x) = x :=
alg_hom.congr_fun of_grades_comp_grades x

-- lemma ι_submodule.induction_on'
--   {p : ∀ i, ι_submodule R X i → Prop}
--   (hzero : ∀ i, p i (0 : ι_submodule R X i))
--   (hadd : ∀ i (a b : ι_submodule R X i), p _ a → p _ b → p _ (a + b))
--   {i : ℕ} (x : ι_submodule R X i) : p _ x :=
-- begin
--   let p_submonoid : add_submonoid (ι_submodule R X i) :=
--   { carrier := {x | p _ x},
--     add_mem' := hadd i,
--     zero_mem' := hzero i},
--   cases x with xv hxv,
--   suffices : xv ∈ p_submonoid.map (ι_submodule R X i).subtype.to_add_monoid_hom,
--   { obtain ⟨⟨a, ha⟩, pa, rfl⟩ := this,
--     exact pa, },
--   delta ι_submodule,
--   simp,
--   apply submodule.span_induction hxv,
--   rw ←finsupp.sum_single xv,
--   apply add_submonoid.finsupp_sum_mem,
--   intros d hd,
--   exact ⟨⟨_, is_homogeneous_monomial _ _ _ (hxv hd)⟩, hmonomial _ _ _ _, rfl⟩,
-- end

-- private lemma map_single_apply (x : ι_submodule R X i) (i j : ℕ) :
--   grades (finsupp.single i x j) = finsupp.single i (grades x) j :=
-- by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades, grades.map_zero]


private lemma map_single_apply' (i j : ℕ) (x : ι_submodule R X i) :
  grades ↑(direct_sum.of _ i x j) = _root_.pi.single i (grades (x : free_algebra R X)) j :=
by rw [finsupp.single_apply, finsupp.single_apply, apply_ite grades, grades.map_zero]

/-- The grade-`i` part consists only of itself -/
@[simp]
lemma grades.map_grades (x : free_algebra R X) (i : ℕ) :
  grades (of_grades $ direct_sum.of _ _ (grades x i)) = direct_sum.of _ i (grades x i) :=
begin
  induction x using free_algebra.induction generalizing i,
  case h_grade0 : {
    rw [grades.commutes, of_grades_of],
    dsimp only [algebra_map, direct_sum.algebra, ring_hom.coe_mk, add_monoid_hom.comp_apply,
      direct_sum.galgebra.of_submodules_to_fun_apply, direct_sum.of],
    cases eq_or_ne i 0 with h,
    { subst h,  apply grades.commutes, },
    classical,
    simp [dfinsupp.single_add_hom_apply, ne.symm h],
  },
  case h_grade1 : {
    rw [grades_ι, of_grades_of, map_single_apply, grades.map_ι,
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
@[simp]
lemma grades_coe {i : ℕ} (x : ι_submodule R X i) :
  grades ↑x = direct_sum.of (λ i, ι_submodule R X i) i x :=
begin
  cases x,
  dsimp,
  unfreezingI { delta ι_submodule at * },
  induction x_val using free_algebra.induction,
  case h_grade0 : {
    rw [grades.commutes],
    -- apply dfinsupp.single_eq_of_sigma_eq,
    -- refl,
    rw [map_single_apply, grades.map_algebra_map,
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

/-- `of_*` is the left-inverse of `to_*` -/
lemma grades_comp_of_grades : grades.comp of_grades = alg_hom.id R (⨁ i, ι_submodule R X i) :=
begin
  ext : 2,
  dsimp [direct_sum.lof_eq_of],
  rw [of_grades_of, grades_coe],
end

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

/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.ray
import linear_algebra.determinant

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `orientation` is a type synonym for `module.ray` for the case where the module is that of
alternating maps from a module to its underlying ring.  An orientation may be associated with an
alternating map or with a basis.

* `module.oriented` is a type class for a choice of orientation of a module that is considered
the positive orientation.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/

noncomputable theory

open_locale big_operators

section ordered_comm_semiring

variables (R : Type*) [ordered_comm_semiring R]
variables (M : Type*) [add_comm_monoid M] [module R M]
variables {N : Type*} [add_comm_monoid N] [module R N]
variables (ι : Type*) [decidable_eq ι]

local attribute [instance] ray_vector.same_ray_setoid

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbreviation orientation [nontrivial R] := module.ray R (alternating_map R M R ι)

/-- A type class fixing an orientation of a module. -/
class module.oriented [nontrivial R] :=
(positive_orientation : orientation R M ι)

variables {R M}

/-- An equivalence between modules implies an equivalence between orientations. -/
def orientation.map [nontrivial R] (e : M ≃ₗ[R] N) : orientation R M ι ≃ orientation R N ι :=
module.ray.map $ alternating_map.dom_lcongr R R ι R e

@[simp] lemma orientation.map_apply [nontrivial R] (e : M ≃ₗ[R] N) (v : alternating_map R M R ι)
  (hv : v ≠ 0) :
  orientation.map ι e (ray_of_ne_zero _ v hv) = ray_of_ne_zero _ (v.comp_linear_map e.symm)
      (mt (v.comp_linear_equiv_eq_zero_iff e.symm).mp hv) := rfl

@[simp] lemma orientation.map_refl [nontrivial R] :
  (orientation.map ι $ linear_equiv.refl R M) = equiv.refl _ :=
by rw [orientation.map, alternating_map.dom_lcongr_refl, module.ray.map_refl]

@[simp] lemma orientation.map_symm [nontrivial R] (e : M ≃ₗ[R] N) :
  (orientation.map ι e).symm = orientation.map ι e.symm := rfl

end ordered_comm_semiring

section ordered_comm_ring

local attribute [instance] ray_vector.same_ray_setoid

variables {R : Type*} [ordered_comm_ring R]
variables {M N : Type*} [add_comm_group M] [add_comm_group N] [module R M] [module R N]

namespace basis

variables {ι : Type*} [fintype ι] [decidable_eq ι]

/-- The orientation given by a basis. -/
protected def orientation [nontrivial R] (e : basis ι R M) : orientation R M ι :=
ray_of_ne_zero R _ e.det_ne_zero

lemma orientation_map [nontrivial R] (e : basis ι R M)
  (f : M ≃ₗ[R] N) : (e.map f).orientation = orientation.map ι f e.orientation :=
by simp_rw [basis.orientation, orientation.map_apply, basis.det_map']

/-- The value of `orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
lemma map_orientation_eq_det_inv_smul [nontrivial R] [is_domain R] (e : basis ι R M)
  (x : orientation R M ι) (f : M ≃ₗ[R] M) : orientation.map ι f x = (f.det)⁻¹ • x :=
begin
  induction x using module.ray.ind with g hg,
  rw [orientation.map_apply, smul_ray_of_ne_zero, ray_eq_iff, units.smul_def,
      (g.comp_linear_map ↑f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
      alternating_map.comp_linear_map_apply, alternating_map.smul_apply, basis.det_comp,
      basis.det_self, mul_one, smul_eq_mul, mul_comm, mul_smul, linear_equiv.coe_inv_det],
end

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
lemma orientation_units_smul [nontrivial R] (e : basis ι R M) (w : ι → units R) :
  (e.units_smul w).orientation = (∏ i, w i)⁻¹ • e.orientation :=
begin
  rw [basis.orientation, basis.orientation, smul_ray_of_ne_zero, ray_eq_iff,
      e.det.eq_smul_basis_det (e.units_smul w), det_units_smul, units.smul_def, smul_smul],
  norm_cast,
  simp
end

end basis

end ordered_comm_ring

section linear_ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

namespace basis

variables [fintype ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
lemma orientation_eq_iff_det_pos (e₁ e₂ : basis ι R M) :
  e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
by rw [basis.orientation, basis.orientation, ray_eq_iff,
       e₁.det.eq_smul_basis_det e₂, alternating_map.smul_apply, basis.det_self, smul_eq_mul,
       mul_one, same_ray_smul_left_iff e₂.det_ne_zero (_ : R)]

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
lemma orientation_eq_or_eq_neg (e : basis ι R M) (x : orientation R M ι) :
  x = e.orientation ∨ x = -e.orientation :=
begin
  induction x using module.ray.ind with x hx,
  rw [basis.orientation, ray_eq_iff, ←ray_neg, ray_eq_iff, x.eq_smul_basis_det e,
    same_ray_neg_smul_left_iff e.det_ne_zero (_ : R), same_ray_smul_left_iff e.det_ne_zero (_ : R),
    lt_or_lt_iff_ne, ne_comm, alternating_map.map_basis_ne_zero_iff],
  exact hx
end

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
lemma orientation_ne_iff_eq_neg (e : basis ι R M) (x : orientation R M ι) :
  x ≠ e.orientation ↔ x = -e.orientation :=
⟨λ h, (e.orientation_eq_or_eq_neg x).resolve_left h,
 λ h, h.symm ▸ (module.ray.ne_neg_self e.orientation).symm⟩

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
lemma orientation_comp_linear_equiv_eq_iff_det_pos (e : basis ι R M) (f : M ≃ₗ[R] M) :
  (e.map f).orientation = e.orientation ↔ 0 < (f : M →ₗ[R] M).det :=
by rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
  linear_equiv.coe_det]

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
lemma orientation_comp_linear_equiv_eq_neg_iff_det_neg (e : basis ι R M) (f : M ≃ₗ[R] M) :
  (e.map f).orientation = -e.orientation ↔ (f : M →ₗ[R] M).det < 0 :=
by rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
  linear_equiv.coe_det]

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp] lemma orientation_neg_single [nontrivial R] (e : basis ι R M) (i : ι) :
  (e.units_smul (function.update 1 i (-1))).orientation = -e.orientation :=
begin
  rw [orientation_units_smul, finset.prod_update_of_mem (finset.mem_univ _)],
  simp
end

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
def adjust_to_orientation [nontrivial R] [nonempty ι] (e : basis ι R M) (x : orientation R M ι) :
  basis ι R M :=
by haveI := classical.dec_eq (orientation R M ι); exact if e.orientation = x then e else
  (e.units_smul (function.update 1 (classical.arbitrary ι) (-1)))

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp] lemma orientation_adjust_to_orientation [nontrivial R] [nonempty ι] (e : basis ι R M)
  (x : orientation R M ι) : (e.adjust_to_orientation x).orientation = x :=
begin
  rw adjust_to_orientation,
  split_ifs with h,
  { exact h },
  { rw [orientation_neg_single, eq_comm, ←orientation_ne_iff_eq_neg, ne_comm],
    exact h }
end

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
lemma adjust_to_orientation_apply_eq_or_eq_neg [nontrivial R] [nonempty ι] (e : basis ι R M)
  (x : orientation R M ι) (i : ι) :
  e.adjust_to_orientation x i = e i ∨ e.adjust_to_orientation x i = -(e i) :=
begin
  rw adjust_to_orientation,
  split_ifs with h,
  { simp },
  { by_cases hi : i = classical.arbitrary ι;
      simp [units_smul_apply, hi] }
end

end basis

end linear_ordered_comm_ring

section linear_ordered_field

variables {R : Type*} [linear_ordered_field R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

namespace orientation

variables [fintype ι] [finite_dimensional R M]

open finite_dimensional

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
lemma eq_or_eq_neg (x₁ x₂ : orientation R M ι) (h : fintype.card ι = finrank R M) :
  x₁ = x₂ ∨ x₁ = -x₂ :=
begin
  have e := (fin_basis R M).reindex (fintype.equiv_fin_of_card_eq h).symm,
  rcases e.orientation_eq_or_eq_neg x₁ with h₁|h₁;
    rcases e.orientation_eq_or_eq_neg x₂ with h₂|h₂;
    simp [h₁, h₂]
end

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
lemma ne_iff_eq_neg (x₁ x₂ : orientation R M ι) (h : fintype.card ι = finrank R M) :
  x₁ ≠ x₂ ↔ x₁ = -x₂ :=
⟨λ hn, (eq_or_eq_neg x₁ x₂ h).resolve_left hn, λ he, he.symm ▸ (module.ray.ne_neg_self x₂).symm⟩

/-- The value of `orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
lemma map_eq_det_inv_smul (x : orientation R M ι) (f : M ≃ₗ[R] M)
  (h : fintype.card ι = finrank R M) :
  orientation.map ι f x = (f.det)⁻¹ • x :=
begin
  have e := (fin_basis R M).reindex (fintype.equiv_fin_of_card_eq h).symm,
  exact e.map_orientation_eq_det_inv_smul x f
end

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
lemma map_eq_iff_det_pos (x : orientation R M ι) (f : M ≃ₗ[R] M)
  (h : fintype.card ι = finrank R M) :
  orientation.map ι f x = x ↔  0 < (f : M →ₗ[R] M).det :=
by rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, linear_equiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
lemma map_eq_neg_iff_det_neg (x : orientation R M ι) (f : M ≃ₗ[R] M)
  (h : fintype.card ι = finrank R M) :
  orientation.map ι f x = -x ↔ (f : M →ₗ[R] M).det < 0 :=
by rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, linear_equiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
def some_basis [nonempty ι] (x : orientation R M ι) (h : fintype.card ι = finrank R M) :
  basis ι R M :=
((fin_basis R M).reindex (fintype.equiv_fin_of_card_eq h).symm).adjust_to_orientation x

/-- `some_basis` gives a basis with the required orientation. -/
@[simp] lemma some_basis_orientation [nonempty ι] (x : orientation R M ι)
  (h : fintype.card ι = finrank R M) : (x.some_basis h).orientation = x :=
basis.orientation_adjust_to_orientation _ _

end orientation

end linear_ordered_field

/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.determinant

/-!
# Orientations of modules and rays in modules

This file defines rays in modules and orientations of modules.

## Main definitions

* `module.ray` is a type for the equivalence class of nonzero vectors in a module with some
common positive multiple.

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

section ordered_comm_semiring

variables (R : Type*) [ordered_comm_semiring R]
variables {M : Type*} [add_comm_monoid M] [module R M]
variables (ι : Type*) [decidable_eq ι]

/-- Two vectors are in the same ray if some positive multiples of them are equal (in the typical
case over a field, this means each is a positive multiple of the other).  Over a field, this
is equivalent to `mul_action.orbit_rel`. -/
def same_ray (v₁ v₂ : M) : Prop :=
∃ (r₁ r₂ : R), 0 < r₁ ∧ 0 < r₂ ∧ r₁ • v₁ = r₂ • v₂

variables (M)

/-- `same_ray` is symmetric. -/
lemma symmetric_same_ray : symmetric (same_ray R : M → M → Prop) :=
λ _ _ ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₂, r₁, hr₂, hr₁, h.symm⟩

/-- `same_ray` is transitive. -/
lemma transitive_same_ray :
  transitive (same_ray R : M → M → Prop) :=
λ _ _ _ ⟨r₁, r₂, hr₁, hr₂, h₁⟩ ⟨r₃, r₄, hr₃, hr₄, h₂⟩,
  ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄,
   by rw [mul_smul, mul_smul, h₁, ←h₂, smul_comm]⟩

/-- `same_ray` is reflexive. -/
lemma reflexive_same_ray [nontrivial R] :
  reflexive (same_ray R : M → M → Prop) :=
λ _, ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩

/-- `same_ray` is an equivalence relation. -/
lemma equivalence_same_ray [nontrivial R] :
  equivalence (same_ray R : M → M → Prop) :=
⟨reflexive_same_ray R M, symmetric_same_ray R M, transitive_same_ray R M⟩

variables {R M}

/-- A vector is in the same ray as a positive multiple of itself. -/
lemma same_ray_pos_smul_right (v : M) {r : R} (h : 0 < r) : same_ray R v (r • v) :=
⟨r, 1, h, let f := nontrivial_of_lt _ _ h in by exactI zero_lt_one, (one_smul _ _).symm⟩

/-- A vector is in the same ray as a positive multiple of one it is in the same ray as. -/
lemma same_ray.pos_smul_right {v₁ v₂ : M} {r : R} (h : same_ray R v₁ v₂) (hr : 0 < r) :
  same_ray R v₁ (r • v₂) :=
transitive_same_ray R M h (same_ray_pos_smul_right v₂ hr)

/-- A positive multiple of a vector is in the same ray as that vector. -/
lemma same_ray_pos_smul_left (v : M) {r : R} (h : 0 < r) : same_ray R (r • v) v :=
⟨1, r, let f := nontrivial_of_lt _ _ h in by exactI zero_lt_one, h, one_smul _ _⟩

/-- A positive multiple of a vector is in the same ray as one it is in the same ray as. -/
lemma same_ray.pos_smul_left {v₁ v₂ : M} {r : R} (h : same_ray R v₁ v₂) (hr : 0 < r) :
  same_ray R (r • v₁) v₂ :=
transitive_same_ray R M (same_ray_pos_smul_left v₁ hr) h

variables (R M)

/-- The setoid of the `same_ray` relation for elements of a module. -/
def same_ray_setoid [nontrivial R] : setoid M :=
{ r := λ v₁ v₂, same_ray R v₁ v₂, iseqv := equivalence_same_ray R M }

/-- Nonzero vectors, as used to define rays. -/
@[reducible] def ray_vector := {v : M // v ≠ 0}

/-- The setoid of the `same_ray` relation for the subtype of nonzero vectors. -/
def ray_vector.same_ray_setoid [nontrivial R] : setoid (ray_vector M) :=
(same_ray_setoid R M).comap coe

local attribute [instance] ray_vector.same_ray_setoid

variables {R M}

/-- Equivalence of nonzero vectors, in terms of same_ray. -/
lemma equiv_iff_same_ray [nontrivial R] (v₁ v₂ : ray_vector M) :
  v₁ ≈ v₂ ↔ same_ray R (v₁ : M) v₂ :=
iff.rfl

variables (R M)

/-- A ray (equivalence class of nonzero vectors with common positive multiples) in a module. -/
@[nolint has_inhabited_instance]
def module.ray [nontrivial R] := quotient (ray_vector.same_ray_setoid R M)

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
abbreviation orientation [nontrivial R] := module.ray R (alternating_map R M R ι)

/-- A type class fixing an orientation of a module. -/
class module.oriented [nontrivial R] :=
(positive_orientation : orientation R M ι)

variables {M}

/-- The ray given by a nonzero vector. -/
protected def ray_of_ne_zero [nontrivial R] (v : M) (h : v ≠ 0) : module.ray R M :=
⟦⟨v, h⟩⟧

/-- An induction principle for `module.ray`, used as `induction x using module.ray.ind`. -/
lemma module.ray.ind [nontrivial R] {C : module.ray R M → Prop}
  (h : Π v (hv : v ≠ 0), C (ray_of_ne_zero R v hv)) (x : module.ray R M) : C x :=
quotient.ind (subtype.rec $ by exact h) x

/-- The rays given by two nonzero vectors are equal if and only if those vectors
satisfy `same_ray`. -/
lemma ray_eq_iff [nontrivial R] {v₁ v₂ : M} (hv₁ : v₁ ≠ 0) (hv₂ : v₂ ≠ 0) :
  ray_of_ne_zero R _ hv₁ = ray_of_ne_zero R _ hv₂ ↔ same_ray R v₁ v₂ :=
quotient.eq

variables {R}

/-- The ray given by a positive multiple of a nonzero vector. -/
@[simp] lemma ray_pos_smul [nontrivial R] {v : M} (h : v ≠ 0) {r : R} (hr : 0 < r)
  (hrv : r • v ≠ 0) : ray_of_ne_zero R _ hrv = ray_of_ne_zero R _ h :=
begin
  rw ray_eq_iff,
  exact same_ray_pos_smul_left v hr
end

namespace module.ray

/-- An arbitrary `ray_vector` giving a ray. -/
def some_ray_vector [nontrivial R] (x : module.ray R M) : ray_vector M :=
quotient.out x

/-- The ray of `some_ray_vector`. -/
@[simp] lemma some_ray_vector_ray [nontrivial R] (x : module.ray R M) :
  (⟦x.some_ray_vector⟧ : module.ray R M) = x :=
quotient.out_eq _

/-- An arbitrary nonzero vector giving a ray. -/
def some_vector [nontrivial R] (x : module.ray R M) : M :=
x.some_ray_vector

/-- `some_vector` is nonzero. -/
@[simp] lemma some_vector_ne_zero [nontrivial R] (x : module.ray R M) : x.some_vector ≠ 0 :=
x.some_ray_vector.property

/-- The ray of `some_vector`. -/
@[simp] lemma some_vector_ray [nontrivial R] (x : module.ray R M) :
  ray_of_ne_zero R _ x.some_vector_ne_zero = x :=
(congr_arg _ (subtype.coe_eta _ _) : _).trans x.out_eq

end module.ray

end ordered_comm_semiring

section ordered_comm_ring

local attribute [instance] ray_vector.same_ray_setoid

variables {R : Type*} [ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]

/-- If two vectors are in the same ray, so are their negations. -/
lemma same_ray.neg {v₁ v₂ : M} : same_ray R v₁ v₂ → same_ray R (-v₁) (-v₂) :=
λ ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₁, r₂, hr₁, hr₂, by rwa [smul_neg, smul_neg, neg_inj]⟩

/-- `same_ray.neg` as an `iff`. -/
@[simp] lemma same_ray_neg_iff {v₁ v₂ : M} : same_ray R (-v₁) (-v₂) ↔ same_ray R v₁ v₂ :=
⟨λ h, by simpa only [neg_neg] using h.neg, same_ray.neg⟩

lemma same_ray_neg_swap {v₁ v₂ : M} : same_ray R (-v₁) v₂ ↔ same_ray R v₁ (-v₂) :=
⟨λ h, by simpa only [neg_neg] using h.neg, λ h, by simpa only [neg_neg] using h.neg⟩

/-- If a vector is in the same ray as its negation, that vector is zero. -/
lemma eq_zero_of_same_ray_self_neg [no_zero_smul_divisors R M] {v₁ : M} (h : same_ray R v₁ (-v₁)) :
  v₁ = 0 :=
begin
  rcases h with ⟨r₁, r₂, hr₁, hr₂, h⟩,
  rw [smul_neg, ←neg_smul, ←sub_eq_zero, ←sub_smul, sub_neg_eq_add, smul_eq_zero] at h,
  exact h.resolve_left (add_pos hr₁ hr₂).ne',
end

namespace ray_vector

variables {R}

/-- Negating a nonzero vector. -/
instance : has_neg (ray_vector M) := ⟨λ v, ⟨-v, neg_ne_zero.2 v.prop⟩⟩

/-- Negating a nonzero vector commutes with coercion to the underlying module. -/
@[simp, norm_cast] lemma coe_neg (v : ray_vector M) : ↑(-v) = -(v : M) := rfl

/-- Negating a nonzero vector twice produces the original vector. -/
@[simp] protected lemma neg_neg (v : ray_vector M) : -(-v) = v :=
by rw [subtype.ext_iff, coe_neg, coe_neg, neg_neg]

variables (R)

/-- If two nonzero vectors are equivalent, so are their negations. -/
@[simp] lemma equiv_neg_iff [nontrivial R] (v₁ v₂ : ray_vector M) : -v₁ ≈ -v₂ ↔ v₁ ≈ v₂ :=
by rw [equiv_iff_same_ray, equiv_iff_same_ray, coe_neg, coe_neg, same_ray_neg_iff]

end ray_vector

variables (R)

/-- Negating a ray. -/
instance [nontrivial R] : has_neg (module.ray R M) :=
⟨quotient.map (λ v, -v) (λ v₁ v₂, (ray_vector.equiv_neg_iff R v₁ v₂).2)⟩

/-- The ray given by the negation of a nonzero vector. -/
lemma ray_neg [nontrivial R] (v : M) (h : v ≠ 0) :
  ray_of_ne_zero R _ (show -v ≠ 0, by rw neg_ne_zero; exact h) = -(ray_of_ne_zero R _ h) :=
rfl

namespace module.ray

variables {R}

/-- Negating a ray twice produces the original ray. -/
@[simp] protected lemma neg_neg [nontrivial R] (x : module.ray R M) : -(-x) = x :=
quotient.ind (λ a, congr_arg quotient.mk $ ray_vector.neg_neg _) x

/-- A ray does not equal its own negation. -/
lemma ne_neg_self [nontrivial R] [no_zero_smul_divisors R M] (x : module.ray R M) : x ≠ -x :=
begin
  intro h,
  induction x using module.ray.ind,
  rw [←ray_neg, ray_eq_iff] at h,
  exact x_hv (eq_zero_of_same_ray_self_neg h)
end

end module.ray

namespace basis

variables {R} {ι : Type*} [fintype ι] [decidable_eq ι]

/-- The orientation given by a basis. -/
protected def orientation [nontrivial R] (e : basis ι R M) : orientation R M ι :=
ray_of_ne_zero R _ e.det_ne_zero

end basis

end ordered_comm_ring

section linear_ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

/-- `same_ray` follows from membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
lemma same_ray_of_mem_orbit {v₁ v₂ : M} (h : v₁ ∈ mul_action.orbit (units.pos_subgroup R) v₂) :
  same_ray R v₁ v₂ :=
begin
  rcases h with ⟨⟨r, hr⟩, (rfl : r • v₂ = v₁)⟩,
  exact same_ray_pos_smul_left _ hr,
end

/-- A nonzero vector is in the same ray as a multiple of itself if and only if that multiple
is positive. -/
@[simp] lemma same_ray_smul_right_iff [no_zero_smul_divisors R M] {v : M} (hv : v ≠ 0) (r : R) :
  same_ray R v (r • v) ↔ 0 < r :=
begin
  split,
  { rintros ⟨r₁, r₂, hr₁, hr₂, h⟩,
    rw [smul_smul, ←sub_eq_zero, ←sub_smul, sub_eq_add_neg, neg_mul_eq_mul_neg] at h,
    by_contradiction hr,
    rw [not_lt, ←neg_le_neg_iff, neg_zero] at hr,
    have hzzz := ne_of_gt (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr)),
    simpa [ne_of_gt (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr)),
           -mul_neg_eq_neg_mul_symm] using h },
  { exact λ h, same_ray_pos_smul_right v h }
end

/-- A multiple of a nonzero vector is in the same ray as that vector if and only if that multiple
is positive. -/
@[simp] lemma same_ray_smul_left_iff [no_zero_smul_divisors R M] {v : M} (hv : v ≠ 0) (r : R) :
  same_ray R (r • v) v ↔ 0 < r :=
begin
  rw (symmetric_same_ray R M).iff,
  exact same_ray_smul_right_iff hv r
end

/-- The negation of a nonzero vector is in the same ray as a multiple of that vector if and
only if that multiple is negative. -/
@[simp] lemma same_ray_neg_smul_right_iff [no_zero_smul_divisors R M] {v : M} (hv : v ≠ 0)
  (r : R) : same_ray R (-v) (r • v) ↔ r < 0 :=
begin
  rw [←same_ray_neg_iff, neg_neg, ←neg_smul, same_ray_smul_right_iff hv (-r)],
  exact right.neg_pos_iff
end

/-- A multiple of a nonzero vector is in the same ray as the negation of that vector if and
only if that multiple is negative. -/
@[simp] lemma same_ray_neg_smul_left_iff [no_zero_smul_divisors R M] {v : M} (hv : v ≠ 0)
  (r : R) : same_ray R (r • v) (-v) ↔ r < 0 :=
begin
  rw [←same_ray_neg_iff, neg_neg, ←neg_smul, same_ray_smul_left_iff hv (-r)],
  exact left.neg_pos_iff
end

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
  rw [basis.orientation, ←x.some_vector_ray, ray_eq_iff, ←ray_neg, ray_eq_iff,
      x.some_vector.eq_smul_basis_det e],
  rcases lt_trichotomy (x.some_vector e) 0 with h|h|h,
  { right,
    exact (same_ray_neg_smul_left_iff e.det_ne_zero (_ : R)).2 h },
  { simpa [h] using x.some_vector.eq_smul_basis_det e },
  { left,
    exact (same_ray_smul_left_iff e.det_ne_zero (_ : R)).2 h }
end

end basis

end linear_ordered_comm_ring

section linear_ordered_field

variables (R : Type*) [linear_ordered_field R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

/-- `same_ray` is equivalent to membership of `mul_action.orbit` for the `units.pos_subgroup`. -/
lemma same_ray_iff_mem_orbit (v₁ v₂ : M) :
  same_ray R v₁ v₂ ↔ v₁ ∈ mul_action.orbit (units.pos_subgroup R) v₂ :=
begin
  split,
  { rintros ⟨r₁, r₂, hr₁, hr₂, h⟩,
    rw mul_action.mem_orbit_iff,
    have h' : (r₁⁻¹ * r₂) • v₂ = v₁,
    { rw [mul_smul, ←h, ←mul_smul, inv_mul_cancel (ne_of_lt hr₁).symm, one_smul] },
    have hr' : 0 < (r₁⁻¹ * r₂) := mul_pos (inv_pos.2 hr₁) hr₂,
    change (⟨units.mk0 (r₁⁻¹ * r₂) (ne_of_lt hr').symm, hr'⟩ : units.pos_subgroup R) • v₂ = v₁
      at h',
    exact ⟨_, h'⟩ },
  { exact same_ray_of_mem_orbit }
end

/-- `same_ray_setoid` equals `mul_action.orbit_rel` for the `units.pos_subgroup`. -/
lemma same_ray_setoid_eq_orbit_rel :
  same_ray_setoid R M = mul_action.orbit_rel (units.pos_subgroup R) M :=
setoid.ext' $ same_ray_iff_mem_orbit R

variables {R}

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

end orientation

end linear_ordered_field

/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import linear_algebra.determinant

/-!
# Orientations of modules

This file defines orientation of modules.

## Main definitions

* `orientation` is a type class for a choice of orientation of a module.  An orientation may
be associated with an alternating map or with a basis.

## Implementation notes

`orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `fintype` and there exists a basis of the same cardinality.

Although `orientation` is a type class, many lemmas have an `orientation` as an explicit
argument, in order to talk about how two orientations are related or to state results in
contexts where a particular orientation is not being chosen as canonical.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/

noncomputable theory

section ordered_comm_ring

variables {R : Type*} [ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

namespace alternating_map

/-- Two alternating maps have the same orientation if some positive multiples of them are
equal (in the typical case over a field, this means each is a positive multiple of the other). -/
def same_orientation (f g : alternating_map R M R ι) : Prop :=
∃ (r₁ r₂ : R), 0 < r₁ ∧ 0 < r₂ ∧ r₁ • f = r₂ • g

variables (R M ι)

/-- `same_orientation` is symmetric. -/
lemma symmetric_same_orientation :
  symmetric (same_orientation : alternating_map R M R ι → alternating_map R M R ι → Prop) :=
λ f g ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₂, r₁, hr₂, hr₁, h.symm⟩

/-- `same_orientation` is transitive. -/
lemma transitive_same_orientation :
  transitive (same_orientation : alternating_map R M R ι → alternating_map R M R ι → Prop) :=
λ f g h ⟨r₁, r₂, hr₁, hr₂, h₁⟩ ⟨r₃, r₄, hr₃, hr₄, h₂⟩,
  ⟨r₃ * r₁, r₂ * r₄, mul_pos hr₃ hr₁, mul_pos hr₂ hr₄,
   by rw [mul_smul, mul_smul, h₁, ←h₂, smul_comm]⟩

section nontrivial

variables [nontrivial R]

/-- `same_orientation` is reflexive. -/
lemma reflexive_same_orientation :
  reflexive (same_orientation : alternating_map R M R ι → alternating_map R M R ι → Prop) :=
λ f, ⟨1, 1, zero_lt_one, zero_lt_one, rfl⟩

/-- `same_orientation` is an equivalence relation. -/
lemma equivalence_same_orientation :
  equivalence (same_orientation : alternating_map R M R ι → alternating_map R M R ι → Prop) :=
⟨reflexive_same_orientation R M ι, symmetric_same_orientation R M ι,
 transitive_same_orientation R M ι⟩

variables {R M ι}

/-- An alternating map has the same orientation as a positive multiple of itself. -/
lemma same_orientation_pos_smul_right (f : alternating_map R M R ι) {r : R} (h : 0 < r) :
  same_orientation f (r • f) :=
⟨r, 1, h, zero_lt_one, (one_smul _ _).symm⟩

/-- A positive multiple of an alternating map has the same orientation as that map. -/
lemma same_orientation_pos_smul_left (f : alternating_map R M R ι) {r : R} (h : 0 < r) :
  same_orientation (r • f) f :=
⟨1, r, zero_lt_one, h, one_smul _ _⟩

end nontrivial

variables {R M ι}

/-- If two alternating maps have the same orientation, so do their negations. -/
@[simp] lemma same_orientation_neg_iff (f g : alternating_map R M R ι) :
  same_orientation (-f) (-g) ↔ same_orientation f g :=
⟨λ ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₁, r₂, hr₁, hr₂, by rwa [smul_neg, smul_neg, neg_inj] at h⟩,
 λ ⟨r₁, r₂, hr₁, hr₂, h⟩, ⟨r₁, r₂, hr₁, hr₂, by rwa [smul_neg, smul_neg, neg_inj]⟩⟩

end alternating_map

variables (R M ι)

/-- Nonzero alternating maps, as used to define orientations. -/
@[reducible] def orientation_map := {f : alternating_map R M R ι // f ≠ 0}

instance : has_coe_to_fun (orientation_map R M ι) (λ _, (ι → M) → R) :=
⟨λ x, ⇑(x : alternating_map R M R ι)⟩

namespace orientation_map

variables {R M ι}

/-- Negating a nonzero alternating map. -/
instance : has_neg (orientation_map R M ι) :=
⟨λ ⟨f, hf⟩, ⟨-f, by rw neg_ne_zero; exact hf⟩⟩

/-- Negating a nonzero alternating map commutes with coercion to `alternating_map`. -/
@[simp, norm_cast] lemma coe_neg (f : orientation_map R M ι) :
  ((-f : orientation_map R M ι) : alternating_map R M R ι) = -(f : alternating_map R M R ι) :=
by cases f; refl

/-- Negating a nonzero alternating map twice produces the original map. -/
@[simp] protected lemma neg_neg (f : orientation_map R M ι) : -(-f) = f :=
by rw [subtype.ext_iff, coe_neg, coe_neg, neg_neg]

variables (R M ι)

variables [nontrivial R]

/-- The setoid of the `same_orientation` relation for the subtype of nonzero alternating maps. -/
instance same_orientation_setoid : setoid (orientation_map R M ι) :=
{ r := λ f g, (f : alternating_map R M R ι).same_orientation g,
  iseqv := equivalence.comap (alternating_map.equivalence_same_orientation R M ι) _ }

variables {R M ι}

/-- Equivalence of nonzero alternating maps, in terms of same_orientation. -/
lemma equiv_iff_same_orientation (f g : orientation_map R M ι) :
  f ≈ g ↔ (f : alternating_map R M R ι).same_orientation g :=
iff.rfl

/-- If two nonzero alternating maps are equivalent, so are their negations. -/
@[simp] lemma equiv_neg_iff (f g : orientation_map R M ι) : -f ≈ -g ↔ f ≈ g :=
by rw [equiv_iff_same_orientation, equiv_iff_same_orientation, coe_neg, coe_neg,
       alternating_map.same_orientation_neg_iff]

end orientation_map

variables [nontrivial R]

/-- An orientation of a module, intended to be used when `ι` is a `fintype` with the same
cardinality as a basis. -/
@[ext] class orientation :=
(alt_maps : quotient (orientation_map.same_orientation_setoid R M ι))

variables {R M ι}

/-- Negating an orientation. -/
instance : has_neg (orientation R M ι) :=
⟨λ ⟨q⟩, ⟨quotient.lift (λ f, ⟦-f⟧) (λ f g h,
  quotient.sound ((orientation_map.equiv_neg_iff f g).2 h)) q⟩⟩

namespace alternating_map

/-- The orientation given by a nonzero alternating map. -/
protected def orientation (f : alternating_map R M R ι) (h : f ≠ 0) : orientation R M ι :=
⟨⟦⟨f, h⟩⟧⟩

/-- The orientation given by the negation of a nonzero alternating map. -/
lemma orientation_neg (f : alternating_map R M R ι) (h : f ≠ 0) :
  (-f).orientation (by rw neg_ne_zero; exact h) = -f.orientation h :=
rfl

/-- The orientations given by two nonzero alternating maps are equal if and only if those maps
satisfy `same_orientation`. -/
lemma orientation_eq_iff (f g : alternating_map R M R ι) (hf : f ≠ 0) (hg : g ≠ 0) :
  f.orientation hf = g.orientation hg ↔ same_orientation f g :=
begin
  rw orientation.ext_iff,
  exact quotient.eq
end

/-- The orientation given by a positive multiple of a nonzero alternating map. -/
@[simp] lemma orientation_pos_smul (f : alternating_map R M R ι) (h : f ≠ 0) (r : R) (hr : 0 < r)
  (hrf : r • f ≠ 0) : (r • f).orientation hrf = f.orientation h :=
begin
  rw orientation_eq_iff,
  exact f.same_orientation_pos_smul_left hr
end

end alternating_map

namespace orientation

/-- An arbitrary `orientation_map` giving an orientation. -/
def some_orientation_map (x : orientation R M ι) : orientation_map R M ι :=
quotient.out x.alt_maps

/-- The orientation of `some_orientation_map`. -/
@[simp] lemma some_orientation_map_orientation (x : orientation R M ι) :
  (⟨⟦x.some_orientation_map⟧⟩ : orientation R M ι) = x :=
begin
  rw some_orientation_map,
  ext,
  exact quotient.out_eq _
end

/-- An arbitrary nonzero alternating map giving an orientation. -/
def some_alternating_map (x : orientation R M ι) : alternating_map R M R ι :=
x.some_orientation_map

/-- `some_alternating_map` is nonzero. -/
@[simp] lemma some_alternating_map_ne_zero (x : orientation R M ι) : x.some_alternating_map ≠ 0 :=
x.some_orientation_map.property

/-- The orientation of `some_alternating_map`. -/
@[simp] lemma some_alternating_map_orientation (x : orientation R M ι) :
  x.some_alternating_map.orientation x.some_alternating_map_ne_zero = x :=
begin
  convert some_orientation_map_orientation x,
  rw alternating_map.orientation,
  congr,
  rw subtype.ext_iff,
  refl
end

/-- Negating an orientation twice produces the original orientation. -/
@[simp] protected lemma neg_neg (x : orientation R M ι) : -(-x) = x :=
begin
  rw [←some_alternating_map_orientation x, ←alternating_map.orientation_neg,
      ←alternating_map.orientation_neg],
  congr,
  exact neg_neg _
end

end orientation

namespace basis

variables [fintype ι]

/-- The orientation given by a basis. -/
protected def orientation (e : basis ι R M) : orientation R M ι :=
e.det.orientation e.det_ne_zero

end basis

end ordered_comm_ring

section linear_ordered_comm_ring

variables {R : Type*} [linear_ordered_comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {ι : Type*} [decidable_eq ι]

namespace alternating_map

/-- A nonzero alternating map has the same orientation as a multiple of itself if and only if
that multiple is positive. -/
@[simp] lemma same_orientation_smul_right_iff (f : alternating_map R M R ι) (hf : f ≠ 0) (r : R) :
  same_orientation f (r • f) ↔ 0 < r :=
begin
  split,
  { rintros ⟨r₁, r₂, hr₁, hr₂, h⟩,
    rw [smul_smul, ←sub_eq_zero, ←sub_smul, sub_eq_add_neg, neg_mul_eq_mul_neg] at h,
    by_contradiction hr,
    rw [not_lt, ←neg_le_neg_iff, neg_zero] at hr,
    have hzzz := ne_of_gt (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr)),
    simpa [ne_of_gt (add_pos_of_pos_of_nonneg hr₁ (mul_nonneg hr₂.le hr)),
           -mul_neg_eq_neg_mul_symm] using h },
  { exact λ h, f.same_orientation_pos_smul_right h }
end

/-- A multiple of a nonzero alternating map has the same orientation as that map if and only if
that multiple is positive. -/
@[simp] lemma same_orientation_smul_left_iff (f : alternating_map R M R ι) (hf : f ≠ 0) (r : R) :
  same_orientation (r • f) f ↔ 0 < r :=
begin
  rw (symmetric_same_orientation R M ι).iff,
  exact f.same_orientation_smul_right_iff hf r
end

/-- The negation of a nonzero alternating map has the same orientation as a multiple of that map
if and only if that multiple is negative. -/
@[simp] lemma same_orientation_neg_smul_right_iff (f : alternating_map R M R ι) (hf : f ≠ 0)
  (r : R) : same_orientation (-f) (r • f) ↔ r < 0 :=
begin
  rw [←same_orientation_neg_iff, neg_neg, ←neg_smul, f.same_orientation_smul_right_iff hf],
  exact right.neg_pos_iff
end

/-- A multiple of a nonzero alternating map has the same orientation as the negation of that map
if and only if that multiple is negative. -/
@[simp] lemma same_orientation_neg_smul_left_iff (f : alternating_map R M R ι) (hf : f ≠ 0)
  (r : R) : same_orientation (r • f) (-f) ↔ r < 0 :=
begin
  rw [←same_orientation_neg_iff, neg_neg, ←neg_smul, f.same_orientation_smul_left_iff hf],
  exact left.neg_pos_iff
end

end alternating_map

namespace basis

variables [fintype ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
lemma orientation_eq_iff_det_pos (e₁ e₂ : basis ι R M) :
  e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
by rw [basis.orientation, basis.orientation, alternating_map.orientation_eq_iff,
       e₁.det.eq_smul_basis_det e₂, alternating_map.smul_apply, basis.det_self, smul_eq_mul,
       mul_one, e₂.det.same_orientation_smul_left_iff e₂.det_ne_zero]

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
lemma orientation_eq_or_eq_neg (e : basis ι R M) (x : orientation R M ι) :
  x = e.orientation ∨ x = -e.orientation :=
begin
  rw [basis.orientation, ←x.some_alternating_map_orientation, alternating_map.orientation_eq_iff,
      ←alternating_map.orientation_neg, alternating_map.orientation_eq_iff,
      x.some_alternating_map.eq_smul_basis_det e],
  rcases lt_trichotomy (x.some_alternating_map e) 0 with h|h|h,
  { right,
    exact (e.det.same_orientation_neg_smul_left_iff e.det_ne_zero _).2 h },
  { have hz := x.some_alternating_map.eq_smul_basis_det e,
    rw h at hz,
    simpa using hz },
  { left,
    exact (e.det.same_orientation_smul_left_iff e.det_ne_zero _).2 h }
end

end basis

namespace orientation

/-- An orientation does not equal its own negation. -/
lemma ne_neg_self (x : orientation R M ι) : x ≠ -x :=
begin
  intro h,
  rw [←some_alternating_map_orientation x, ←alternating_map.orientation_neg,
      alternating_map.orientation_eq_iff] at h,
  rcases h with ⟨r₁, r₂, hr₁, hr₂, h⟩,
  rw [smul_neg, ←neg_smul, ←sub_eq_zero, ←sub_smul] at h,
  simpa [ne_of_gt (add_pos hr₁ hr₂)] using h
end

end orientation

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

end orientation

end linear_ordered_field

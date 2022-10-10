/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.localization.basic

/-!
# Integer elements of a localization

## Main definitions

 * `is_localization.is_integer` is a predicate stating that `x : S` is in the image of `R`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variables {R : Type*} [comm_ring R] {M : submonoid R} {S : Type*} [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open function
open_locale big_operators

namespace is_localization

section

variables (R) {M S}

-- TODO: define a subalgebra of `is_integer`s
/-- Given `a : S`, `S` a localization of `R`, `is_integer R a` iff `a` is in the image of
the localization map from `R` to `S`. -/
def is_integer (a : S) : Prop := a ∈ (algebra_map R S).range

end

lemma is_integer_zero : is_integer R (0 : S) := subring.zero_mem _
lemma is_integer_one : is_integer R (1 : S) := subring.one_mem _

lemma is_integer_add {a b : S} (ha : is_integer R a) (hb : is_integer R b) :
  is_integer R (a + b) :=
subring.add_mem _ ha hb

lemma is_integer_mul {a b : S} (ha : is_integer R a) (hb : is_integer R b) :
  is_integer R (a * b) :=
subring.mul_mem _ ha hb

lemma is_integer_smul {a : R} {b : S} (hb : is_integer R b) :
  is_integer R (a • b) :=
begin
  rcases hb with ⟨b', hb⟩,
  use a * b',
  rw [←hb, (algebra_map R S).map_mul, algebra.smul_def]
end

variables (M) {S} [is_localization M S]

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the right, matching the argument order in `localization_map.surj`.
-/
lemma exists_integer_multiple' (a : S) :
  ∃ (b : M), is_integer R (a * algebra_map R S b) :=
let ⟨⟨num, denom⟩, h⟩ := is_localization.surj _ a in ⟨denom, set.mem_range.mpr ⟨num, h.symm⟩⟩

/-- Each element `a : S` has an `M`-multiple which is an integer.

This version multiplies `a` on the left, matching the argument order in the `has_smul` instance.
-/
lemma exists_integer_multiple (a : S) :
  ∃ (b : M), is_integer R ((b : R) • a) :=
by { simp_rw [algebra.smul_def, mul_comm _ a], apply exists_integer_multiple' }

/-- We can clear the denominators of a `finset`-indexed family of fractions. -/
lemma exist_integer_multiples {ι : Type*} (s : finset ι) (f : ι → S) :
  ∃ (b : M), ∀ i ∈ s, is_localization.is_integer R ((b : R) • f i) :=
begin
  haveI := classical.prop_decidable,
  refine ⟨∏ i in s, (sec M (f i)).2, λ i hi, ⟨_, _⟩⟩,
  { exact (∏ j in s.erase i, (sec M (f j)).2) * (sec M (f i)).1 },
  rw [ring_hom.map_mul, sec_spec', ←mul_assoc, ←(algebra_map R S).map_mul, ← algebra.smul_def],
  congr' 2,
  refine trans _ ((submonoid.subtype M).map_prod _ _).symm,
  rw [mul_comm, ←finset.prod_insert (s.not_mem_erase i), finset.insert_erase hi],
  refl
end

/-- We can clear the denominators of a finite indexed family of fractions. -/
lemma exist_integer_multiples_of_finite {ι : Type*} [finite ι] (f : ι → S) :
  ∃ (b : M), ∀ i, is_localization.is_integer R ((b : R) • f i) :=
begin
  casesI nonempty_fintype ι,
  obtain ⟨b, hb⟩ := exist_integer_multiples M finset.univ f,
  exact ⟨b, λ i, hb i (finset.mem_univ _)⟩
end

/-- We can clear the denominators of a finite set of fractions. -/
lemma exist_integer_multiples_of_finset (s : finset S) :
  ∃ (b : M), ∀ a ∈ s, is_integer R ((b : R) • a) :=
exist_integer_multiples M s id

/-- A choice of a common multiple of the denominators of a `finset`-indexed family of fractions. -/
noncomputable
def common_denom {ι : Type*} (s : finset ι) (f : ι → S) : M :=
(exist_integer_multiples M s f).some

/-- The numerator of a fraction after clearing the denominators
of a `finset`-indexed family of fractions. -/
noncomputable
def integer_multiple {ι : Type*} (s : finset ι) (f : ι → S) (i : s) : R :=
((exist_integer_multiples M s f).some_spec i i.prop).some

@[simp]
lemma map_integer_multiple {ι : Type*} (s : finset ι) (f : ι → S) (i : s) :
  algebra_map R S (integer_multiple M s f i) = common_denom M s f • f i :=
((exist_integer_multiples M s f).some_spec _ i.prop).some_spec

/-- A choice of a common multiple of the denominators of a finite set of fractions. -/
noncomputable
def common_denom_of_finset (s : finset S) : M :=
common_denom M s id

/-- The finset of numerators after clearing the denominators of a finite set of fractions. -/
noncomputable
def finset_integer_multiple [decidable_eq R] (s : finset S) : finset R :=
s.attach.image (λ t, integer_multiple M s id t)

open_locale pointwise

lemma finset_integer_multiple_image [decidable_eq R] (s : finset S) :
  algebra_map R S '' (finset_integer_multiple M s) =
    common_denom_of_finset M s • s :=
begin
  delta finset_integer_multiple common_denom,
  rw finset.coe_image,
  ext,
  split,
  { rintro ⟨_, ⟨x, -, rfl⟩, rfl⟩,
    rw map_integer_multiple,
    exact set.mem_image_of_mem _ x.prop },
  { rintro ⟨x, hx, rfl⟩,
    exact ⟨_, ⟨⟨x, hx⟩, s.mem_attach _, rfl⟩, map_integer_multiple M s id _⟩ }
end

end is_localization

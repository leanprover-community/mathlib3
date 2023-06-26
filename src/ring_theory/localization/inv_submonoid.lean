/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import group_theory.submonoid.inverses
import ring_theory.finite_type
import ring_theory.localization.basic
import tactic.ring_exp

/-!
# Submonoid of inverses

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

 * `is_localization.inv_submonoid M S` is the submonoid of `S = M⁻¹R` consisting of inverses of
   each element `x ∈ M`

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

open function
open_locale big_operators

namespace is_localization

section inv_submonoid

variables (M S)

/-- The submonoid of `S = M⁻¹R` consisting of `{ 1 / x | x ∈ M }`. -/
def inv_submonoid : submonoid S := (M.map (algebra_map R S)).left_inv

variable [is_localization M S]

lemma submonoid_map_le_is_unit : M.map (algebra_map R S) ≤ is_unit.submonoid S :=
by { rintros _ ⟨a, ha, rfl⟩, exact is_localization.map_units S ⟨_, ha⟩ }

/-- There is an equivalence of monoids between the image of `M` and `inv_submonoid`. -/
noncomputable
abbreviation equiv_inv_submonoid : M.map (algebra_map R S) ≃* inv_submonoid M S :=
((M.map (algebra_map R S)).left_inv_equiv (submonoid_map_le_is_unit M S)).symm

/-- There is a canonical map from `M` to `inv_submonoid` sending `x` to `1 / x`. -/
noncomputable
def to_inv_submonoid : M →* inv_submonoid M S :=
(equiv_inv_submonoid M S).to_monoid_hom.comp ((algebra_map R S : R →* S).submonoid_map M)

lemma to_inv_submonoid_surjective : function.surjective (to_inv_submonoid M S) :=
function.surjective.comp (equiv.surjective _) (monoid_hom.submonoid_map_surjective _ _)

@[simp]
lemma to_inv_submonoid_mul (m : M) : (to_inv_submonoid M S m : S) * (algebra_map R S m) = 1 :=
submonoid.left_inv_equiv_symm_mul _ _ _

@[simp]
lemma mul_to_inv_submonoid (m : M) : (algebra_map R S m) * (to_inv_submonoid M S m : S) = 1 :=
submonoid.mul_left_inv_equiv_symm _ _ ⟨_, _⟩

@[simp]
lemma smul_to_inv_submonoid (m : M) : m • (to_inv_submonoid M S m : S) = 1 :=
by { convert mul_to_inv_submonoid M S m, rw ← algebra.smul_def, refl }

variables {S}

lemma surj' (z : S) : ∃ (r : R) (m : M), z = r • to_inv_submonoid M S m :=
begin
  rcases is_localization.surj M z with ⟨⟨r, m⟩, e : z * _ = algebra_map R S r⟩,
  refine ⟨r, m, _⟩,
  rw [algebra.smul_def, ← e, mul_assoc],
  simp,
end

lemma to_inv_submonoid_eq_mk' (x : M) :
  (to_inv_submonoid M S x : S) = mk' S 1 x :=
by { rw ← (is_localization.map_units S x).mul_left_inj, simp }

lemma mem_inv_submonoid_iff_exists_mk' (x : S) :
  x ∈ inv_submonoid M S ↔ ∃ m : M, mk' S 1 m = x :=
begin
  simp_rw ← to_inv_submonoid_eq_mk',
  exact ⟨λ h, ⟨_, congr_arg subtype.val (to_inv_submonoid_surjective M S ⟨x, h⟩).some_spec⟩,
    λ h, h.some_spec ▸ (to_inv_submonoid M S h.some).prop⟩
end

variables (S)

lemma span_inv_submonoid : submodule.span R (inv_submonoid M S : set S) = ⊤ :=
begin
  rw eq_top_iff,
  rintros x -,
  rcases is_localization.surj' M x with ⟨r, m, rfl⟩,
  exact submodule.smul_mem _ _ (submodule.subset_span (to_inv_submonoid M S m).prop),
end

lemma finite_type_of_monoid_fg [monoid.fg M] : algebra.finite_type R S :=
begin
  have := monoid.fg_of_surjective _ (to_inv_submonoid_surjective M S),
  rw monoid.fg_iff_submonoid_fg at this,
  rcases this with ⟨s, hs⟩,
  refine ⟨⟨s, _⟩⟩,
  rw eq_top_iff,
  rintro x -,
  change x ∈ ((algebra.adjoin R _ : subalgebra R S).to_submodule : set S),
  rw [algebra.adjoin_eq_span, hs, span_inv_submonoid],
  trivial
end

end inv_submonoid

end is_localization

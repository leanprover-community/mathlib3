/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import category_theory.abelian.pseudoelements
import algebra.category.Module.biproducts

/-!
# Pseudoelements and pullbacks
Borceux claims in Proposition 1.9.5 that the pseudoelement constructed in
`category_theory.abelian.pseudoelement.pseudo_pullback` is unique. We show here that this claim is
false. This means in particular that we cannot have an extensionality principle for pullbacks in
terms of pseudoelements.

## Implementation details
The construction, suggested in https://mathoverflow.net/a/419951/7845, is the following.
We work in the category of `Module ℤ` and we consider the special case of `ℚ ⊞ ℚ` (that is the
pullback over the terminal object). We consider the pseudoelements associated to `x : ℚ ⟶ ℚ ⊞ ℚ`
given by `t ↦ (t, 2 * t)` and `y : ℚ ⟶ ℚ ⊞ ℚ` given by `t ↦ (t, t)`.

## Main results
* `category_theory.abelian.pseudoelement.exist_ne_and_fst_eq_fst_and_snd_eq_snd` : there are two
  pseudoelements `x y : ℚ ⊞ ℚ` such that `x ≠ y`, `biprod.fst x = biprod.fst y` and
  `biprod.snd x = biprod.snd y`.

## References
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

open category_theory.abelian category_theory category_theory.limits Module linear_map

noncomputable theory

namespace category_theory.abelian.pseudoelement

/-- `x` is given by `t ↦ (t, 2 * t)`. -/
def x : over ((of ℤ ℚ) ⊞ (of ℤ ℚ)) :=
over.mk (biprod.lift (of_hom id) (of_hom (2 * id)))

/-- `y` is given by `t ↦ (t, t)`. -/
def y : over ((of ℤ ℚ) ⊞ (of ℤ ℚ)) :=
over.mk (biprod.lift (of_hom id) (of_hom id))

/-- `biprod.fst ≫ x` is pseudoequal to `biprod.fst y`. -/
lemma fst_x_pseudo_eq_fst_y : pseudo_equal _ (app biprod.fst x) (app biprod.fst y) :=
begin
  refine ⟨of ℤ ℚ, (of_hom id), (of_hom id),
    category_struct.id.epi (of ℤ ℚ), _, _⟩,
  { exact (Module.epi_iff_surjective _).2 (λ a, ⟨(a : ℚ), by simp⟩) },
  { dsimp [x, y],
    simp }
end

/-- `biprod.snd ≫ x` is pseudoequal to `biprod.snd y`. -/
lemma snd_x_pseudo_eq_snd_y : pseudo_equal _
  (app biprod.snd x) (app biprod.snd y) :=
begin
  refine ⟨of ℤ ℚ, (of_hom id), 2 • (of_hom id),
    category_struct.id.epi (of ℤ ℚ), _, _⟩,
  { refine (Module.epi_iff_surjective _).2 (λ a, ⟨(a/2 : ℚ), _⟩),
    simp only [two_smul, add_apply, of_hom_apply, id_coe, id.def],
    exact add_halves' (show ℚ, from a) },
  { dsimp [x, y],
    exact concrete_category.hom_ext _ _ (λ a, by simpa) }
end

/-- `x` is not pseudoequal to `y`. -/
lemma x_not_pseudo_eq : ¬(pseudo_equal _ x y) :=
begin
  intro h,
  replace h := Module.eq_range_of_pseudoequal h,
  dsimp [x, y] at h,
  let φ := (biprod.lift (of_hom (id : ℚ →ₗ[ℤ] ℚ)) (of_hom (2 * id))),
  have mem_range := mem_range_self φ (1 : ℚ),
  rw h at mem_range,
  obtain ⟨a, ha⟩ := mem_range,
  rw [← Module.id_apply (φ (1 : ℚ)), ← biprod.total, ← linear_map.comp_apply, ← comp_def,
    preadditive.comp_add] at ha,
  let π₁ := (biprod.fst : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _),
  have ha₁ := congr_arg π₁ ha,
  simp only [← linear_map.comp_apply, ← comp_def] at ha₁,
  simp only [biprod.lift_fst, of_hom_apply, id_coe, id.def, preadditive.add_comp, category.assoc,
    biprod.inl_fst, category.comp_id, biprod.inr_fst, limits.comp_zero, add_zero] at ha₁,
  let π₂ := (biprod.snd : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _),
  have ha₂ := congr_arg π₂ ha,
  simp only [← linear_map.comp_apply, ← comp_def] at ha₂,
  have : (2 : ℚ →ₗ[ℤ] ℚ) 1 = 1 + 1 := rfl,
  simp only [ha₁, this, biprod.lift_snd, of_hom_apply, id_coe, id.def, preadditive.add_comp,
    category.assoc, biprod.inl_snd, limits.comp_zero, biprod.inr_snd, category.comp_id, zero_add,
    mul_apply, self_eq_add_left] at ha₂,
  exact one_ne_zero' ℚ ha₂,
end

local attribute [instance] pseudoelement.setoid

open_locale pseudoelement

/-- `biprod.fst ⟦x⟧ = biprod.fst ⟦y⟧`. -/
lemma fst_mk_x_eq_fst_mk_y : (biprod.fst : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) ⟦x⟧ =
  (biprod.fst : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) ⟦y⟧ :=
by simpa only [abelian.pseudoelement.pseudo_apply_mk, quotient.eq] using fst_x_pseudo_eq_fst_y

/-- `biprod.snd ⟦x⟧ = biprod.snd ⟦y⟧`. -/
lemma snd_mk_x_eq_snd_mk_y : (biprod.snd : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) ⟦x⟧ =
  (biprod.snd : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) ⟦y⟧ :=
by simpa only [abelian.pseudoelement.pseudo_apply_mk, quotient.eq] using snd_x_pseudo_eq_snd_y

/-- `⟦x⟧ ≠ ⟦y⟧`. -/
lemma mk_x_ne_mk_y : ⟦x⟧ ≠ ⟦y⟧ :=
λ h, x_not_pseudo_eq $ quotient.eq.1 h

/-- There are two pseudoelements `x y : ℚ ⊞ ℚ` such that `x ≠ y`, `biprod.fst x = biprod.fst y` and
 `biprod.snd x = biprod.snd y`. -/
lemma exist_ne_and_fst_eq_fst_and_snd_eq_snd : ∃ x y : (of ℤ ℚ) ⊞ (of ℤ ℚ),
  x ≠ y ∧
  (biprod.fst : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) x = (biprod.fst : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) y ∧
  (biprod.snd : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) x = (biprod.snd : (of ℤ ℚ) ⊞ (of ℤ ℚ) ⟶ _) y:=
⟨⟦x⟧, ⟦y⟧, mk_x_ne_mk_y, fst_mk_x_eq_fst_mk_y, snd_mk_x_eq_snd_mk_y⟩

end category_theory.abelian.pseudoelement

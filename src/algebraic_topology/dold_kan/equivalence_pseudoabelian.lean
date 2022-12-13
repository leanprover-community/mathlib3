/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.equivalence_additive
import algebraic_topology.dold_kan.compatibility
import category_theory.idempotents.simplicial_object

/-!

# The Dold-Kan correspondence for pseudoabelian categories

In this file, for any idempotent complete additive category `C`,
the Dold-Kan equivalence
`idempotents.dold_kan.equivalence C : simplicial_object C ≌ chain_complex C ℕ`
is obtained. It is deduced from the equivalence
`preadditive.dold_kan.equivalence` between the respective idempotent
completions of these categories using the fact that when `C` is idempotent complete,
then both `simplicial_object C` and `chain_complex C ℕ` are idempotent complete.

The construction of `idempotents.dold_kan.equivalence` uses the tools
introduced in the file `compatibility.lean`. Doing so, the functor
`idempotents.dold_kan.N` of the equivalence is
the composition of `N₁ : simplicial_object C ⥤ karoubi (chain_complex C ℕ)`
(defined in `functor_n.lean`) and the inverse of the equivalence
`chain_complex C ℕ ≌ karoubi (chain_complex C ℕ)`. The functor
`idempotents.dold_kan.Γ` of the equivalence is by definition the functor
`Γ₀` introduced in `functor_gamma.lean`.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.idempotents

variables {C : Type*} [category C] [preadditive C] [is_idempotent_complete C]
  [has_finite_coproducts C]

namespace category_theory

namespace idempotents

namespace dold_kan

open algebraic_topology.dold_kan

/-- The functor `N` for the equivalence is obtained by composing
`N' : simplicial_object C ⥤ karoubi (chain_complex C ℕ)` and the inverse
of the equivalence `chain_complex C ℕ ≌ karoubi (chain_complex C ℕ)`. -/
@[simps, nolint unused_arguments]
def N : simplicial_object C ⥤ chain_complex C ℕ :=
N₁ ⋙ (to_karoubi_equivalence _).inverse

/-- The functor `Γ` for the equivalence is `Γ'`. -/
@[simps, nolint unused_arguments]
def Γ : chain_complex C ℕ ⥤ simplicial_object C := Γ₀

lemma hN₁ : (to_karoubi_equivalence (simplicial_object C)).functor ⋙
  preadditive.dold_kan.equivalence.functor = N₁ :=
functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi _ _) N₁

lemma hΓ₀ : (to_karoubi_equivalence (chain_complex C ℕ)).functor ⋙
  preadditive.dold_kan.equivalence.inverse = Γ ⋙ (to_karoubi_equivalence _).functor :=
functor.congr_obj (functor_extension₂_comp_whiskering_left_to_karoubi _ _) Γ₀

/-- The Dold-Kan equivalence for pseudoabelian categories given
by the functors `N` and `Γ`. It is obtained by applying the results in
`compatibility.lean` to the equivalence `preadditive.dold_kan.equivalence`. -/
def equivalence : simplicial_object C ≌ chain_complex C ℕ :=
compatibility.equivalence (eq_to_iso hN₁) (eq_to_iso hΓ₀)

lemma equivalence_functor : (equivalence : simplicial_object C ≌ _).functor = N := rfl
lemma equivalence_inverse : (equivalence : simplicial_object C ≌ _).inverse = Γ := rfl

/-- The natural isomorphism `NΓ' satisfies the compatibility that is needed
for the construction of our counit isomorphism `η` -/
lemma hη : compatibility.τ₀ =
  compatibility.τ₁ (eq_to_iso hN₁) (eq_to_iso hΓ₀)
  (N₁Γ₀ : Γ ⋙ N₁ ≅ (to_karoubi_equivalence (chain_complex C ℕ)).functor) :=
begin
  ext K : 3,
  simpa only [compatibility.τ₀_hom_app, compatibility.τ₁_hom_app, eq_to_iso.hom,
    preadditive.dold_kan.equivalence_counit_iso, N₂Γ₂_to_karoubi_iso_hom, eq_to_hom_map,
    eq_to_hom_trans_assoc, eq_to_hom_app] using N₂Γ₂_compatible_with_N₁Γ₀ K,
end

/-- The counit isomorphism induced by `N₁Γ₀` -/
@[simps]
def η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ) := compatibility.equivalence_counit_iso
  (N₁Γ₀ : (Γ : chain_complex C ℕ ⥤ _ ) ⋙ N₁ ≅ (to_karoubi_equivalence _).functor)

lemma equivalence_counit_iso :
  dold_kan.equivalence.counit_iso = (η : Γ ⋙ N ≅ 𝟭 (chain_complex C ℕ)) :=
compatibility.equivalence_counit_iso_eq hη

lemma hε : compatibility.υ (eq_to_iso hN₁) =
  (Γ₂N₁ : (to_karoubi_equivalence _).functor ≅ (N₁ : simplicial_object C ⥤ _) ⋙
  preadditive.dold_kan.equivalence.inverse) :=
begin
  ext X : 4,
  erw [nat_trans.comp_app, compatibility_Γ₂N₁_Γ₂N₂_nat_trans],
  simp only [compatibility.υ_hom_app, compatibility_Γ₂N₁_Γ₂N₂,
    preadditive.dold_kan.equivalence_unit_iso, Γ₂N₂, iso.symm_hom, as_iso_inv, assoc],
  erw [← nat_trans.comp_app_assoc, is_iso.hom_inv_id],
  dsimp,
  simpa only [id_comp, eq_to_hom_app, eq_to_hom_map, eq_to_hom_trans],
end

/-- The unit isomorphism induced by `Γ₂N₁`. -/
def ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ :=
compatibility.equivalence_unit_iso (eq_to_iso hΓ₀) Γ₂N₁

lemma equivalence_unit_iso : dold_kan.equivalence.unit_iso =
  (ε : 𝟭 (simplicial_object C) ≅ N ⋙ Γ) :=
compatibility.equivalence_unit_iso_eq hε

end dold_kan

end idempotents

end category_theory

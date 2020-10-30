/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.normal
import field_theory.primitive_element
import field_theory.fixed

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `fixing_subgroup_of_fixed_field` : If `E/F` is finite dimensional (but not necessarily Galois)
  then `fixing_subgroup (fixed_field H) = H`
- `fixed_field_of_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`
Together, these two result prove the Galois correspondence
-/

noncomputable theory
open_locale classical

open finite_dimensional

namespace galois

section

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
@[class] def is_galois : Prop := is_separable F E ∧ normal F E

instance is_galois_of_fixed_field (G : Type*) [group G] [fintype G] [mul_semiring_action G E] :
  is_galois (mul_action.fixed_points G E) E :=
⟨fixed_points.separable G E, fixed_points.normal G E⟩

instance aut : group (E ≃ₐ[F] E) :=
{ mul := λ ϕ ψ, ψ.trans ϕ,
  mul_assoc := λ ϕ ψ χ, rfl,
  one := 1,
  one_mul := λ ϕ, by {ext, refl},
  mul_one := λ ϕ, by {ext, refl},
  inv := alg_equiv.symm,
  mul_left_inv := λ ϕ, by {ext, exact alg_equiv.symm_apply_apply ϕ a} }

lemma is_galois_implies_card_aut_eq_findim [finite_dimensional F E] [h : is_galois F E] :
  fintype.card (E ≃ₐ[F] E) = findim F E :=
begin
  cases field.exists_primitive_element h.1 with α hα,
  cases h.1 α with H1 h_separable,
  cases h.2 α with H2 h_splits,
  have switch : (⊤ : intermediate_field F E).to_subalgebra.to_submodule = ⊤ :=
    by { ext, exact iff_of_true intermediate_field.mem_top submodule.mem_top },
  rw [←findim_top, ←switch],
  change fintype.card (E ≃ₐ[F] E) = findim F (⊤ : intermediate_field F E),
  replace h_splits : polynomial.splits (algebra_map F F⟮α⟯) (minimal_polynomial H2),
  { rw hα,
    let map : E →+* (⊤ : intermediate_field F E) :=
    { to_fun := λ x, ⟨x, intermediate_field.mem_top⟩,
      map_one' := rfl,
      map_mul' := λ _ _, rfl,
      map_zero' := rfl,
      map_add' := λ _ _, rfl },
    rw (show algebra_map F (⊤ : intermediate_field F E) = map.comp (algebra_map F E),
      by { ext, refl }),
    exact polynomial.splits_comp_of_splits (algebra_map F E) map h_splits },
  rw [←hα, @intermediate_field.findim_adjoin_integral F _ _ _ _ α H2,
      ←@intermediate_field.alg_equiv_adjoin_integral F _ _ _ _ α H2 h_separable h_splits],
  apply fintype.card_congr,
  rw hα,
  change (E ≃ₐ[F] E) ≃
    ((⊤ : intermediate_field F E).to_subalgebra ≃ₐ[F] (⊤ : intermediate_field F E).to_subalgebra),
  rw intermediate_field.top_to_subalgebra,
  exact
  { to_fun := λ ϕ, (algebra.top_equiv).trans (alg_equiv.trans ϕ (algebra.top_equiv).symm),
    inv_fun := λ ϕ, (algebra.top_equiv).symm.trans (alg_equiv.trans ϕ (algebra.top_equiv)),
    left_inv := λ _, by { ext, simp only [alg_equiv.apply_symm_apply, alg_equiv.trans_apply] },
    right_inv := λ _, by { ext, simp only [alg_equiv.symm_apply_apply, alg_equiv.trans_apply] } },
end

end

section galois_correspondence

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
variables (H : subgroup (E ≃ₐ[F] E)) (K : intermediate_field F E)

instance is_galois_of_tower_top [h : is_galois F E] : is_galois K E :=
begin
  split,
  { exact is_separable_tower_top_of_is_separable K h.1 },
  intros x,
  cases h.2 x with hx hhx,
  rw (show (algebra_map F E) = (algebra_map K E).comp (algebra_map F K), by ext;refl) at hhx,
  exact ⟨is_integral_of_is_scalar_tower x hx, polynomial.splits_of_splits_of_dvd (algebra_map K E)
    (polynomial.map_ne_zero (minimal_polynomial.ne_zero hx))
    ((polynomial.splits_map_iff (algebra_map F K) (algebra_map K E)).mpr hhx)
    (minimal_polynomial.dvd_map_of_is_scalar_tower K hx)⟩,
end

instance subgroup_action : faithful_mul_semiring_action H E := {
  smul := λ h x, h x,
  smul_zero := λ _, alg_equiv.map_zero _,
  smul_add := λ _, alg_equiv.map_add _,
  one_smul := λ _, rfl,
  smul_one := λ _, alg_equiv.map_one _,
  mul_smul := λ _ _ _, rfl,
  smul_mul := λ _, alg_equiv.map_mul _,
  eq_of_smul_eq_smul' := λ x y z, subtype.ext (alg_equiv.ext z),
}

/-- The intermediate_field fixed by a subgroup -/
def fixed_field : intermediate_field F E := {
  carrier := mul_action.fixed_points H E,
  zero_mem' := smul_zero,
  add_mem' := λ _ _ hx hy _, by rw [smul_add, hx, hy],
  neg_mem' := λ _ hx _, by rw [smul_neg, hx],
  one_mem' := smul_one,
  mul_mem' := λ _ _ hx hy _, by rw [smul_mul', hx, hy],
  inv_mem' := λ _ hx _, by rw [smul_inv, hx],
  algebra_map_mem' := λ _ _, alg_equiv.commutes _ _,
}

lemma findim_fixed_field_eq_card [finite_dimensional F E] :
  findim (fixed_field H) E = fintype.card H :=
fixed_points.findim_eq_card H E

/-- The subgroup fixing an intermediate_field -/
def fixing_subgroup : subgroup (E ≃ₐ[F] E) := {
  carrier := λ ϕ, ∀ x : K, ϕ x = x,
  one_mem' := λ _, rfl,
  mul_mem' := λ _ _ hx hy _, (congr_arg _ (hy _)).trans (hx _),
  inv_mem' := λ _ hx _, (equiv.symm_apply_eq (alg_equiv.to_equiv _)).mpr (hx _).symm,
}

lemma le_iff_le : K ≤ fixed_field H ↔ H ≤ fixing_subgroup K :=
⟨λ h g hg x, h (subtype.mem x) ⟨g, hg⟩, λ h x hx g, h (subtype.mem g) ⟨x, hx⟩⟩

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixing_subgroup_iso : fixing_subgroup K ≃* (E ≃ₐ[K] E) := {
  to_fun := λ ϕ, alg_equiv.of_bijective (alg_hom.mk ϕ (alg_equiv.map_one ϕ) (alg_equiv.map_mul ϕ)
    (alg_equiv.map_zero ϕ) (alg_equiv.map_add ϕ) (ϕ.mem)) (alg_equiv.bijective ϕ),
  inv_fun := λ ϕ, ⟨alg_equiv.of_bijective (alg_hom.mk ϕ (alg_equiv.map_one ϕ) (alg_equiv.map_mul ϕ)
    (alg_equiv.map_zero ϕ) (alg_equiv.map_add ϕ) (λ r, ϕ.commutes (algebra_map F K r)))
      (alg_equiv.bijective ϕ), ϕ.commutes⟩,
  left_inv := λ _, by {ext, refl},
  right_inv := λ _, by {ext, refl},
  map_mul' := λ _ _, by {ext, refl},
}

theorem fixing_subgroup_of_fixed_field [finite_dimensional F E] :
  fixing_subgroup (fixed_field H) = H :=
begin
  have H_le : H ≤ (fixing_subgroup (fixed_field H)) := (le_iff_le _ _).mp (le_refl _),
  suffices : fintype.card H = fintype.card (fixing_subgroup (fixed_field H)),
  { exact subgroup.ext' (set.eq_of_inclusion_surjective ((fintype.bijective_iff_injective_and_card
    (set.inclusion H_le)).mpr ⟨set.inclusion_injective H_le, this⟩).2).symm },
  rw fintype.card_congr (fixing_subgroup_iso (fixed_field H)).to_equiv,
  rw fintype.card_congr (fixed_points.to_alg_hom_equiv H E),
  rw fintype.card_congr (alg_equiv_equiv_alg_hom (fixed_field H) E),
  exact fintype.card_congr (by refl),
end

instance alg_instance : algebra K (fixed_field (fixing_subgroup K)) := {
  smul := λ x y, ⟨x*y, λ ϕ, by rw [smul_mul', (show ϕ • ↑x = ↑x, by exact subtype.mem ϕ x),
    (show ϕ • ↑y = ↑y, by exact subtype.mem y ϕ)]⟩,
  to_fun := λ x, ⟨x, λ ϕ, subtype.mem ϕ x⟩,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ _ _, rfl,
}

instance tower_instance : is_scalar_tower K (fixed_field (fixing_subgroup K)) E :=
⟨λ _ _ _, mul_assoc _ _ _⟩

theorem fixed_field_of_fixing_subgroup [finite_dimensional F E] [h : is_galois F E] :
  fixed_field (fixing_subgroup K) = K :=
begin
  have K_le : K ≤ fixed_field (fixing_subgroup K) := (le_iff_le _ _).mpr (le_refl _),
  suffices : findim K E = findim (fixed_field (fixing_subgroup K)) E,
  { exact (intermediate_field.eq_of_le_of_findim_eq' K_le this).symm },
  rw [findim_fixed_field_eq_card, fintype.card_congr (fixing_subgroup_iso K).to_equiv],
  exact (is_galois_implies_card_aut_eq_findim K E).symm,
end

lemma card_fixing_subgroup_eq_findim [finite_dimensional F E] [is_galois F E] :
  fintype.card (fixing_subgroup K) = findim K E :=
by conv { to_rhs, rw [←fixed_field_of_fixing_subgroup K, findim_fixed_field_eq_card] }

/-- The Galois correspondence from intermediate fields to subgroups -/
def galois_correspondence [finite_dimensional F E] [is_galois F E] :
  intermediate_field F E ≃o order_dual (subgroup (E ≃ₐ[F] E)) :=
{ to_fun := fixing_subgroup,
  inv_fun := fixed_field,
  left_inv := λ K, fixed_field_of_fixing_subgroup K,
  right_inv := λ H, fixing_subgroup_of_fixed_field H,
  map_rel_iff' := λ K L, by { rw [←fixed_field_of_fixing_subgroup L, le_iff_le,
                                  fixed_field_of_fixing_subgroup L, ←order_dual.dual_le], refl} }

end galois_correspondence

section galois_equivalent_definitions

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

lemma is_separable_splitting_field_of_is_galois [finite_dimensional F E] [h : is_galois F E] :
  ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E :=
begin
  cases field.exists_primitive_element h.1 with α h1,
  cases h.1 α with h2 h3,
  cases h.2 α with _ h4,
  use minimal_polynomial h2,
  split,
  { exact h3 },
  { split,
    { exact h4 },
    { rw [eq_top_iff, ←intermediate_field.top_to_subalgebra, ←h1],
      rw intermediate_field.adjoin_simple_to_subalgebra_of_integral F α h2,
      apply algebra.adjoin_mono,
      rw [set.singleton_subset_iff, finset.mem_coe, multiset.mem_to_finset, polynomial.mem_roots],
      { dsimp only [polynomial.is_root],
        rw [polynomial.eval_map, ←polynomial.aeval_def],
        exact minimal_polynomial.aeval h2 },
      { exact polynomial.map_ne_zero (minimal_polynomial.ne_zero h2) } } }
end

end galois_equivalent_definitions

end galois

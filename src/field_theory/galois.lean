/-
Copyright (c) 2020 Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning and Patrick Lutz
-/

import field_theory.normal
import field_theory.primitive_element
import field_theory.fixed
import ring_theory.power_basis

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

open finite_dimensional alg_equiv


section

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-- A field extension E/F is galois if it is both separable and normal -/
@[class] def is_galois : Prop := is_separable F E ∧ normal F E

namespace is_galois

@[priority 100] -- see Note [lower instance priority]
instance to_is_separable [h : is_galois F E] : is_separable F E := h.1

@[priority 100] -- see Note [lower instance priority]
instance to_normal [h : is_galois F E] : normal F E := h.2

variables {F} {E}

lemma integral (h : is_galois F E) (x : E) : is_integral F x :=
Exists.cases_on (h.1 x) (λ H _, H)

lemma separable (h : is_galois F E) (x : E) :
  (minimal_polynomial (integral h x)).separable :=
Exists.cases_on (h.1 x) (λ _ H, H)

lemma normal (h : is_galois F E) (x : E) :
  (minimal_polynomial (integral h x)).splits (algebra_map F E) :=
Exists.cases_on (h.2 x) (λ _ H, H)

variables (F) (E)

instance of_fixed_field (G : Type*) [group G] [fintype G] [mul_semiring_action G E] :
  is_galois (mul_action.fixed_points G E) E :=
⟨fixed_points.separable G E, fixed_points.normal G E⟩

lemma intermediate_field.adjoin_simple.card_aut_eq_findim
  [finite_dimensional F E] {α : E} (hα : is_integral F α)
  (h_sep : (minimal_polynomial hα).separable)
  (h_splits : (minimal_polynomial hα).splits (algebra_map F F⟮α⟯)) :
  fintype.card (F⟮α⟯ ≃ₐ[F] F⟮α⟯) = findim F F⟮α⟯ :=
begin
  letI : fintype (F⟮α⟯ →ₐ[F] F⟮α⟯) := intermediate_field.fintype_of_alg_hom_adjoin_integral F hα,
  rw intermediate_field.adjoin.findim hα,
  rw ← intermediate_field.card_alg_hom_adjoin_integral F hα h_sep h_splits,
  exact fintype.card_congr (alg_equiv_equiv_alg_hom F F⟮α⟯)
end

lemma card_aut_eq_findim [finite_dimensional F E] [h : is_galois F E] :
  fintype.card (E ≃ₐ[F] E) = findim F E :=
begin
  cases field.exists_primitive_element h.1 with α hα,
  let iso : F⟮α⟯ ≃ₐ[F] E := {
    to_fun := λ e, e.val,
    inv_fun := λ e, ⟨e, by { rw hα, exact intermediate_field.mem_top }⟩,
    left_inv := λ _, by { ext, refl },
    right_inv := λ _, rfl,
    map_mul' := λ _ _, rfl,
    map_add' := λ _ _, rfl,
    commutes' := λ _, rfl },
  have H : is_integral F α := h.integral α,
  have h_sep : (minimal_polynomial H).separable := h.separable α,
  have h_splits : (minimal_polynomial H).splits (algebra_map F E) := h.normal α,
  replace h_splits : polynomial.splits (algebra_map F F⟮α⟯) (minimal_polynomial H),
  { convert polynomial.splits_comp_of_splits
    (algebra_map F E) iso.symm.to_alg_hom.to_ring_hom h_splits },
  rw ← linear_equiv.findim_eq iso.to_linear_equiv,
  rw ← intermediate_field.adjoin_simple.card_aut_eq_findim F E H h_sep h_splits,
  apply fintype.card_congr,
  apply equiv.mk (λ ϕ, iso.trans (trans ϕ iso.symm)) (λ ϕ, iso.symm.trans (trans ϕ iso)),
  { intro ϕ, ext1, simp only [trans_apply, apply_symm_apply] },
  { intro ϕ, ext1, simp only [trans_apply, symm_apply_apply] },
end

end is_galois

end

section galois_correspondence

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]
variables (H : subgroup (E ≃ₐ[F] E)) (K : intermediate_field F E)

instance is_galois.tower_top [h : is_galois F E] : is_galois K E :=
⟨is_separable_tower_top_of_is_separable K h.1, normal.tower_top_of_normal F K E h.2⟩

namespace intermediate_field

instance subgroup_action : faithful_mul_semiring_action H E :=
{ smul := λ h x, h x,
  smul_zero := λ _, map_zero _,
  smul_add := λ _, map_add _,
  one_smul := λ _, rfl,
  smul_one := λ _, map_one _,
  mul_smul := λ _ _ _, rfl,
  smul_mul := λ _, map_mul _,
  eq_of_smul_eq_smul' := λ x y z, subtype.ext (alg_equiv.ext z) }

/-- The intermediate_field fixed by a subgroup -/
def fixed_field : intermediate_field F E :=
{ carrier := mul_action.fixed_points H E,
  zero_mem' := λ g, smul_zero g,
  add_mem' := λ a b hx hy g, by rw [smul_add g a b, hx, hy],
  neg_mem' := λ a hx g, by rw [smul_neg g a, hx],
  one_mem' := λ g, smul_one g,
  mul_mem' := λ a b hx hy g, by rw [smul_mul' g a b, hx, hy],
  inv_mem' := λ a hx g, by rw [smul_inv _ g a, hx],
  algebra_map_mem' := λ a g, commutes g a }

lemma findim_fixed_field_eq_card [finite_dimensional F E] :
  findim (fixed_field H) E = fintype.card H :=
fixed_points.findim_eq_card H E

/-- The subgroup fixing an intermediate_field -/
def fixing_subgroup : subgroup (E ≃ₐ[F] E) :=
{ carrier := λ ϕ, ∀ x : K, ϕ x = x,
  one_mem' := λ _, rfl,
  mul_mem' := λ _ _ hx hy _, (congr_arg _ (hy _)).trans (hx _),
  inv_mem' := λ _ hx _, (equiv.symm_apply_eq (to_equiv _)).mpr (hx _).symm }

lemma le_iff_le : K ≤ fixed_field H ↔ H ≤ fixing_subgroup K :=
⟨λ h g hg x, h (subtype.mem x) ⟨g, hg⟩, λ h x hx g, h (subtype.mem g) ⟨x, hx⟩⟩

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixing_subgroup_equiv : fixing_subgroup K ≃* (E ≃ₐ[K] E) :=
{ to_fun := λ ϕ, of_bijective (alg_hom.mk ϕ (map_one ϕ) (map_mul ϕ)
    (map_zero ϕ) (map_add ϕ) (ϕ.mem)) (bijective ϕ),
  inv_fun := λ ϕ, ⟨of_bijective (alg_hom.mk ϕ (ϕ.map_one) (ϕ.map_mul)
    (ϕ.map_zero) (ϕ.map_add) (λ r, ϕ.commutes (algebra_map F K r)))
      (ϕ.bijective), ϕ.commutes⟩,
  left_inv := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl },
  map_mul' := λ _ _, by { ext, refl } }

theorem fixing_subgroup_fixed_field [finite_dimensional F E] :
  fixing_subgroup (fixed_field H) = H :=
begin
  have H_le : H ≤ (fixing_subgroup (fixed_field H)) := (le_iff_le _ _).mp (le_refl _),
  suffices : fintype.card H = fintype.card (fixing_subgroup (fixed_field H)),
  { exact subgroup.ext' (set.eq_of_inclusion_surjective ((fintype.bijective_iff_injective_and_card
    (set.inclusion H_le)).mpr ⟨set.inclusion_injective H_le, this⟩).2).symm },
  apply fintype.card_congr,
  refine (fixed_points.to_alg_hom_equiv H E).trans _,
  refine (alg_equiv_equiv_alg_hom (fixed_field H) E).symm.trans _,
  exact (fixing_subgroup_equiv (fixed_field H)).to_equiv.symm
end

instance fixed_field.algebra : algebra K (fixed_field (fixing_subgroup K)) :=
{ smul := λ x y, ⟨x*y, λ ϕ, by rw [smul_mul', (show ϕ • ↑x = ↑x, by exact subtype.mem ϕ x),
    (show ϕ • ↑y = ↑y, by exact subtype.mem y ϕ)]⟩,
  to_fun := λ x, ⟨x, λ ϕ, subtype.mem ϕ x⟩,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  map_one' := rfl,
  map_mul' := λ _ _, rfl,
  commutes' := λ _ _, mul_comm _ _,
  smul_def' := λ _ _, rfl }

instance fixed_field.is_scalar_tower : is_scalar_tower K (fixed_field (fixing_subgroup K)) E :=
⟨λ _ _ _, mul_assoc _ _ _⟩

end intermediate_field

namespace is_galois
theorem fixed_field_fixing_subgroup [finite_dimensional F E] [h : is_galois F E] :
  intermediate_field.fixed_field (intermediate_field.fixing_subgroup K) = K :=
begin
  have K_le : K ≤ intermediate_field.fixed_field (intermediate_field.fixing_subgroup K) :=
    (intermediate_field.le_iff_le _ _).mpr (le_refl _),
  suffices : findim K E =
    findim (intermediate_field.fixed_field (intermediate_field.fixing_subgroup K)) E,
  { exact (intermediate_field.eq_of_le_of_findim_eq' K_le this).symm },
  rw [intermediate_field.findim_fixed_field_eq_card,
    fintype.card_congr (intermediate_field.fixing_subgroup_equiv K).to_equiv],
  exact (card_aut_eq_findim K E).symm,
end

lemma card_fixing_subgroup_eq_findim [finite_dimensional F E] [is_galois F E] :
  fintype.card (intermediate_field.fixing_subgroup K) = findim K E :=
by conv { to_rhs, rw [←fixed_field_fixing_subgroup K,
  intermediate_field.findim_fixed_field_eq_card] }

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediate_field_equiv_subgroup [finite_dimensional F E] [is_galois F E] :
  intermediate_field F E ≃o order_dual (subgroup (E ≃ₐ[F] E)) :=
{ to_fun := intermediate_field.fixing_subgroup,
  inv_fun := intermediate_field.fixed_field,
  left_inv := λ K, fixed_field_fixing_subgroup K,
  right_inv := λ H, intermediate_field.fixing_subgroup_fixed_field H,
  map_rel_iff' := λ K L, by { rw [←fixed_field_fixing_subgroup L, intermediate_field.le_iff_le,
                                  fixed_field_fixing_subgroup L, ←order_dual.dual_le], refl } }

/-- The Galois correspondence as a galois_insertion -/
def galois_insertion_intermediate_field_subgroup [finite_dimensional F E] :
  galois_insertion (order_dual.to_dual ∘
      (intermediate_field.fixing_subgroup : intermediate_field F E → subgroup (E ≃ₐ[F] E)))
    ((intermediate_field.fixed_field : subgroup (E ≃ₐ[F] E) → intermediate_field F E) ∘
      order_dual.to_dual) :=
{ choice := λ K _, intermediate_field.fixing_subgroup K,
  gc := λ K H, (intermediate_field.le_iff_le H K).symm,
  le_l_u := λ H, le_of_eq (intermediate_field.fixing_subgroup_fixed_field H).symm,
  choice_eq := λ K _, rfl }

/-- The Galois correspondence as a galois_coinsertion -/
def galois_coinsertion_intermediate_field_subgroup [finite_dimensional F E] [is_galois F E] :
  galois_coinsertion (order_dual.to_dual ∘
      (intermediate_field.fixing_subgroup : intermediate_field F E → subgroup (E ≃ₐ[F] E)))
    ((intermediate_field.fixed_field : subgroup (E ≃ₐ[F] E) → intermediate_field F E) ∘
      order_dual.to_dual) :=
{ choice := λ H _, intermediate_field.fixed_field H,
  gc := λ K H, (intermediate_field.le_iff_le H K).symm,
  u_l_le := λ K, le_of_eq (fixed_field_fixing_subgroup K),
  choice_eq := λ H _, rfl }

end is_galois

end galois_correspondence

section galois_equivalent_definitions

variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

namespace is_galois

lemma is_separable_splitting_field [finite_dimensional F E] [h : is_galois F E] :
  ∃ p : polynomial F, p.separable ∧ p.is_splitting_field F E :=
begin
  cases field.exists_primitive_element h.1 with α h1,
  have h2 : is_integral F α := h.integral α,
  have h3 : (minimal_polynomial h2).separable := h.separable α,
  have h4 : (minimal_polynomial h2).splits (algebra_map F E) := h.normal α,
  use [minimal_polynomial h2, h3, h4],
  rw [eq_top_iff, ←intermediate_field.top_to_subalgebra, ←h1],
  rw intermediate_field.adjoin_simple_to_subalgebra_of_integral F α h2,
  apply algebra.adjoin_mono,
  rw [set.singleton_subset_iff, finset.mem_coe, multiset.mem_to_finset, polynomial.mem_roots],
  { dsimp only [polynomial.is_root],
    rw [polynomial.eval_map, ←polynomial.aeval_def],
    exact minimal_polynomial.aeval h2 },
  { exact polynomial.map_ne_zero (minimal_polynomial.ne_zero h2) }
end

end is_galois

end galois_equivalent_definitions

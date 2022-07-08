/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.inner_product_space.dual

/-!
# Trace Class

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

## Tags

Foobars, barfoos
-/

open tensor_product inner_product_space
open_locale tensor_product big_operators

section finite_rank

def finite_rank_operator_submodule {𝕜₁ 𝕜₂ : Type*} [semiring 𝕜₁] [field 𝕜₂]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) [ring_hom_surjective σ₁₂] (E F : Type*) [add_comm_monoid E]
  [add_comm_group F] [module 𝕜₁ E] [module 𝕜₂ F] [topological_space E] [topological_space F]
  [has_continuous_add F] [has_continuous_const_smul 𝕜₂ F] : submodule 𝕜₂ (E →SL[σ₁₂] F) :=
{ carrier := {f | finite_dimensional 𝕜₂ f.range},
  zero_mem' :=
  begin
    change finite_dimensional 𝕜₂ (0 : E →ₛₗ[σ₁₂] F).range,
    rw linear_map.range_zero,
    exact finite_dimensional_bot _ _
  end,
  add_mem' := λ f g (hf : finite_dimensional _ _) (hg : finite_dimensional _ _),
  begin
    change finite_dimensional _ _,
    rw [continuous_linear_map.range, linear_map.range_eq_map] at *,
    haveI := hf,
    haveI := hg,
    exact submodule.finite_dimensional_of_le ((⊤ : submodule 𝕜₁ E).map_add_le f g)
  end,
  smul_mem' := λ a f (hf : finite_dimensional _ _),
  begin
    change finite_dimensional _ _,
    rw [continuous_linear_map.range, linear_map.range_eq_map] at *,
    by_cases ha : a = 0,
    { rw [ha, zero_smul _ f, continuous_linear_map.coe_zero, submodule.map_zero],
      exact finite_dimensional_bot _ _ },
    { rwa [continuous_linear_map.coe_smul, submodule.map_smul _ _ _ ha] }
  end }

def finite_rank_operator {𝕜₁ 𝕜₂ : Type*} [semiring 𝕜₁] [field 𝕜₂]
  (σ₁₂ : 𝕜₁ →+* 𝕜₂) [ring_hom_surjective σ₁₂] (E F : Type*) [add_comm_monoid E]
  [add_comm_group F] [module 𝕜₁ E] [module 𝕜₂ F] [topological_space E] [topological_space F]
  [has_continuous_add F] [has_continuous_const_smul 𝕜₂ F] : Type* :=
finite_rank_operator_submodule σ₁₂ E F

namespace finite_rank_operator

section basics

variables {S R K 𝕜 : Type*} [semiring S] [ring R] [field K] {σₛ : S →+* K} {σ : R →+* K}
  [ring_hom_surjective σₛ] [ring_hom_surjective σ] {E F G : Type*} [add_comm_monoid E]
  [add_comm_group F] [add_comm_group G] [module S E] [module R E] [module K F] [module K G]
  [topological_space E] [topological_space F] [topological_space G]
  [has_continuous_const_smul K F] [has_continuous_const_smul K G]

instance [has_continuous_add F] : has_coe (finite_rank_operator σₛ E F) (E →SL[σₛ] F) :=
⟨subtype.val⟩

instance to_fun [has_continuous_add F] :
  has_coe_to_fun (finite_rank_operator σₛ E F) (λ _, E → F) :=
⟨λ f, (f : E →SL[σₛ] F).to_fun⟩

@[simp, norm_cast] lemma coe_coe [has_continuous_add F] (f : finite_rank_operator σₛ E F) :
  ⇑(f : E →SL[σₛ] F) = f := rfl

instance [has_continuous_add F] :
  continuous_semilinear_map_class (finite_rank_operator σₛ E F) σₛ E F :=
{ coe := λ f, f,
  coe_injective' := λ f g hfg, by ext; exact congr_fun hfg x,
  map_add := λ f, map_add (f : E →SL[σₛ] F),
  map_smulₛₗ := λ f, map_smulₛₗ (f : E →SL[σₛ] F),
  map_continuous := λ f, map_continuous (f : E →SL[σₛ] F) }

@[ext] theorem ext [has_continuous_add F] {f g : finite_rank_operator σₛ E F}
  (h : ∀ x, f x = g x) : f = g :=
fun_like.ext f g h

theorem ext_iff [has_continuous_add F] {f g : finite_rank_operator σₛ E F} :
  f = g ↔ ∀ x, f x = g x :=
fun_like.ext_iff

instance [has_continuous_add F] {f : finite_rank_operator σₛ E F} :
  finite_dimensional K (f : E →SL[σₛ] F).range :=
f.2

instance [has_continuous_add F] : add_comm_monoid (finite_rank_operator σₛ E F) :=
submodule.add_comm_monoid _

instance [topological_add_group F] : add_comm_group (finite_rank_operator σ E F) :=
submodule.add_comm_group _

instance [has_continuous_add F] : module K (finite_rank_operator σₛ E F) :=
submodule.module _

@[simp, norm_cast] lemma coe_sum [has_continuous_add F] {ι : Type*} (t : finset ι)
  (f : ι → finite_rank_operator σₛ E F) :
  ↑(∑ d in t, f d) = (∑ d in t, f d : E →SL[σₛ] F) :=
(add_monoid_hom.mk (coe : (finite_rank_operator σₛ E F) → (E →SL[σₛ] F))
  rfl (λ _ _, rfl)).map_sum _ _

@[simp, norm_cast] lemma coe_sum' [has_continuous_add F] {ι : Type*} (t : finset ι)
  (f : ι → finite_rank_operator σₛ E F) :
  ⇑(∑ d in t, f d) = ∑ d in t, f d :=
by simp only [← coe_coe, coe_sum, continuous_linear_map.coe_sum']

lemma sum_apply [has_continuous_add F] {ι : Type*} (t : finset ι)
  (f : ι → finite_rank_operator σₛ E F) (b : E) :
  (∑ d in t, f d) b = ∑ d in t, f d b :=
by simp only [coe_sum', finset.sum_apply]

def smul_rightf [module K E] [topological_space K] [has_continuous_add F] [has_continuous_smul K F]
  (l : E →L[K] K) (x : F) : (finite_rank_operator (ring_hom.id K) E F) :=
⟨l.smul_right x, smul_right_range_finite_dimensional⟩

def smul_rightfₗ [module K E] [topological_space K] [topological_ring K] [has_continuous_add F]
  [has_continuous_smul K F] :
  (E →L[K] K) →ₗ[K] F →ₗ[K] (finite_rank_operator (ring_hom.id K) E F) :=
⟨λ f, ⟨smul_rightf f, λ x y, by ext; apply smul_add, λ r x, by ext; apply smul_comm⟩,
  λ f g, by ext; apply add_smul, λ r f, by ext; apply smul_assoc⟩

@[simp] lemma smul_rightfₗ_apply [module K E] [topological_space K] [topological_ring K] [has_continuous_add F]
  [has_continuous_smul K F] (f : E →L[K] K) (c : F) (x : E) :
  smul_rightfₗ f c x = f x • c :=
rfl

variables (𝕜 E G)

def dual_tensor_hom [nondiscrete_normed_field 𝕜] [module 𝕜 E] [module 𝕜 G]
  [has_continuous_add G] [has_continuous_smul 𝕜 G] :
  ((E →L[𝕜] 𝕜) ⊗[𝕜] G) →ₗ[𝕜] (finite_rank_operator (ring_hom.id 𝕜) E G) :=
uncurry 𝕜 (E →L[𝕜] 𝕜) G (finite_rank_operator (ring_hom.id 𝕜) E G) smul_rightfₗ

end basics

section hilbert_space

variables {𝕜 E F : Type*} [is_R_or_C 𝕜] [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]

noncomputable def dual_tensor_inv (f : finite_rank_operator (ring_hom.id 𝕜) E F) :
  (E →L[𝕜] 𝕜) ⊗[𝕜] F :=
∑ (i : orthonormal_basis_index 𝕜 (f : E →L[𝕜] F).range),
  (to_dual_map 𝕜 F (std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i)).comp (f : E →L[𝕜] F) ⊗ₜ[𝕜]
  std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i

noncomputable def dual_tensor_invₗ :
  finite_rank_operator (ring_hom.id 𝕜) E F →ₗ[𝕜] (E →L[𝕜] 𝕜) ⊗[𝕜] F :=
{ to_fun := dual_tensor_inv,
  map_add' := sorry }

lemma foo (f : finite_rank_operator (ring_hom.id 𝕜) E F) :
  dual_tensor_hom 𝕜 E F (f.dual_tensor_inv) = f :=
begin
  simp_rw [dual_tensor_inv, map_sum, dual_tensor_hom, uncurry_apply],
  ext x,
  simp_rw [sum_apply, smul_rightfₗ_apply],
  --change ∑ i, to_dual_map 𝕜 F (std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i) (f x) •
  --  (std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i : F) = f x,
  --dsimp,
  sorry -- This is clearly true x)
end

lemma bar (f : finite_rank_operator (ring_hom.id 𝕜) E F) :
  dual_tensor_hom 𝕜 E F (f.dual_tensor_inv) = f :=
begin
  simp_rw [dual_tensor_inv, map_sum, dual_tensor_hom, uncurry_apply],
  ext x,
  simp_rw [sum_apply, smul_rightfₗ_apply],
  --change ∑ i, to_dual_map 𝕜 F (std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i) (f x) •
  --  (std_orthonormal_basis 𝕜 (f : E →L[𝕜] F).range i : F) = f x,
  --dsimp,
  sorry -- This is clearly true x)
end

end hilbert_space

end finite_rank_operator

end finite_rank

/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import algebra.direct_sum.module
import analysis.complex.basic
import analysis.convex.uniform
import analysis.normed_space.completion
import analysis.normed_space.bounded_linear_maps
import linear_algebra.bilinear_form

import analysis.inner_product_space.basic

/-!
# Orthogonal complements of submodules

In this file, the `orthogonal` complement of a submodule `K` is defined, and basic API established.
Some of the more subtle results about the orthogonal complement are delayed to
`analysis.inner_product_space.projection`.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.
-/

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [inner_product_space 𝕜 E]
variables [normed_add_comm_group F] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace submodule

variables (K : submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def orthogonal : submodule 𝕜 E :=
{ carrier := {v | ∀ u ∈ K, ⟪u, v⟫ = 0},
  zero_mem' := λ _ _, inner_zero_right _,
  add_mem' := λ x y hx hy u hu, by rw [inner_add_right, hx u hu, hy u hu, add_zero],
  smul_mem' := λ c x hx u hu, by rw [inner_smul_right, hx u hu, mul_zero] }

notation K`ᗮ`:1200 := orthogonal K

/-- When a vector is in `Kᗮ`. -/
lemma mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 := iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
lemma mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 :=
by simp_rw [mem_orthogonal, inner_eq_zero_symm]

variables {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
lemma inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
(K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
lemma inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 :=
by rw [inner_eq_zero_symm]; exact inner_right_of_mem_orthogonal hu hv

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
lemma mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 :=
begin
  refine ⟨inner_right_of_mem_orthogonal (mem_span_singleton_self u), _⟩,
  intros hv w hw,
  rw mem_span_singleton at hw,
  obtain ⟨c, rfl⟩ := hw,
  simp [inner_smul_left, hv],
end

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
lemma mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 :=
by rw [mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm]

lemma sub_mem_orthogonal_of_inner_left {x y : E}
  (h : ∀ (v : K), ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Kᗮ :=
begin
  rw mem_orthogonal',
  intros u hu,
  rw [inner_sub_left, sub_eq_zero],
  exact h ⟨u, hu⟩,
end

lemma sub_mem_orthogonal_of_inner_right {x y : E}
  (h : ∀ (v : K), ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x - y ∈ Kᗮ :=
begin
  intros u hu,
  rw [inner_sub_right, sub_eq_zero],
  exact h ⟨u, hu⟩,
end

variables (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
begin
  rw eq_bot_iff,
  intros x,
  rw mem_inf,
  exact λ ⟨hx, ho⟩, inner_self_eq_zero.1 (ho x hx)
end

/-- `K` and `Kᗮ` have trivial intersection. -/
lemma orthogonal_disjoint : disjoint K Kᗮ :=
by simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
lemma orthogonal_eq_inter : Kᗮ = ⨅ v : K, linear_map.ker (innerSL 𝕜 (v : E)) :=
begin
  apply le_antisymm,
  { rw le_infi_iff,
    rintros ⟨v, hv⟩ w hw,
    simpa using hw _ hv },
  { intros v hv w hw,
    simp only [mem_infi] at hv,
    exact hv ⟨w, hw⟩ }
end

/-- The orthogonal complement of any submodule `K` is closed. -/
lemma is_closed_orthogonal : is_closed (Kᗮ : set E) :=
begin
  rw orthogonal_eq_inter K,
  have := λ v : K, continuous_linear_map.is_closed_ker (innerSL 𝕜 (v : E)),
  convert is_closed_Inter this,
  simp only [infi_coe],
end

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [complete_space E] : complete_space Kᗮ := K.is_closed_orthogonal.complete_space_coe

variables (𝕜 E)

/-- `orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
lemma orthogonal_gc :
  @galois_connection (submodule 𝕜 E) (submodule 𝕜 E)ᵒᵈ _ _
    orthogonal orthogonal :=
λ K₁ K₂, ⟨λ h v hv u hu, inner_left_of_mem_orthogonal hv (h hu),
          λ h v hv u hu, inner_left_of_mem_orthogonal hv (h hu)⟩

variables {𝕜 E}

/-- `orthogonal` reverses the `≤` ordering of two
subspaces. -/
lemma orthogonal_le {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
(orthogonal_gc 𝕜 E).monotone_l h

/-- `orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
lemma orthogonal_orthogonal_monotone {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂) :
  K₁ᗮᗮ ≤ K₂ᗮᗮ :=
orthogonal_le (orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
lemma le_orthogonal_orthogonal : K ≤ Kᗮᗮ := (orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
lemma inf_orthogonal (K₁ K₂ : submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
(orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
lemma infi_orthogonal {ι : Type*} (K : ι → submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (supr K)ᗮ :=
(orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
lemma Inf_orthogonal (s : set $ submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (Sup s)ᗮ :=
(orthogonal_gc 𝕜 E).l_Sup.symm

@[simp] lemma top_orthogonal_eq_bot : (⊤ : submodule 𝕜 E)ᗮ = ⊥ :=
begin
  ext,
  rw [mem_bot, mem_orthogonal],
  exact ⟨λ h, inner_self_eq_zero.mp (h x mem_top), by { rintro rfl, simp }⟩
end

@[simp] lemma bot_orthogonal_eq_top : (⊥ : submodule 𝕜 E)ᗮ = ⊤ :=
begin
  rw [← top_orthogonal_eq_bot, eq_top_iff],
  exact le_orthogonal_orthogonal ⊤
end

@[simp] lemma orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
begin
  refine ⟨_, by { rintro rfl, exact bot_orthogonal_eq_top }⟩,
  intro h,
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot,
  rwa [h, inf_comm, top_inf_eq] at this
end

lemma orthogonal_family_self :
  orthogonal_family 𝕜 (λ b, ↥(cond b K Kᗮ)) (λ b, (cond b K Kᗮ).subtypeₗᵢ)
| tt tt := absurd rfl
| tt ff := λ _ x y, inner_right_of_mem_orthogonal x.prop y.prop
| ff tt := λ _ x y, inner_left_of_mem_orthogonal y.prop x.prop
| ff ff := absurd rfl

end submodule

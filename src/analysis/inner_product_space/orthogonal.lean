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

See also `bilin_form.orthogonal` for orthogonality with respect to a general bilinear form.

## Notation

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

The proposition that two submodules are orthogonal, `submodule.is_ortho`, is denoted by `U ⟂ V`.
Note this is not the same unicode symbol as `⊥` (`has_bot`).
-/

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [inner_product_space 𝕜 E]
variables [normed_add_comm_group F] [inner_product_space 𝕜 F]
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

@[simp]
lemma bilin_form_of_real_inner_orthogonal {E} [normed_add_comm_group E] [inner_product_space ℝ E]
  (K : submodule ℝ E) :
  bilin_form_of_real_inner.orthogonal K = Kᗮ := rfl

/-!
### Orthogonality of submodules

In this section we define `submodule.is_ortho U V`, with notation `U ⟂ V`.

The API roughly matches that of `disjoint`.
-/
namespace submodule

/-- The proposition that two submodules are orthogonal. Has notation `U ⟂ V`. -/
def is_ortho (U V : submodule 𝕜 E) : Prop :=
U ≤ Vᗮ

infix ` ⟂ `:50 := submodule.is_ortho

lemma is_ortho.le {U V : submodule 𝕜 E} (h : U ⟂ V) : U ≤ Vᗮ := h

lemma is_ortho_iff_le {U V : submodule 𝕜 E} : U ⟂ V ↔ U ≤ Vᗮ := iff.rfl

@[symm]
lemma is_ortho.symm {U V : submodule 𝕜 E} (h : U ⟂ V) : V ⟂ U :=
(le_orthogonal_orthogonal _).trans (orthogonal_le h)
lemma is_ortho_comm {U V : submodule 𝕜 E} : U ⟂ V ↔ V ⟂ U := ⟨is_ortho.symm, is_ortho.symm⟩
lemma symmetric_is_ortho : symmetric (is_ortho : submodule 𝕜 E → submodule 𝕜 E → Prop) :=
λ _ _, is_ortho.symm

lemma is_ortho.inner_eq {U V : submodule 𝕜 E} (h : U ⟂ V) {u v : E} (hu : u ∈ U) (hv : v ∈ V) :
  ⟪u, v⟫ = 0 :=
h.symm hv _ hu

lemma is_ortho_iff_inner_eq {U V : submodule 𝕜 E} : U ⟂ V ↔ ∀ (u ∈ U) (v ∈ V), ⟪u, v⟫ = 0 :=
forall₄_congr $ λ u hu v hv, inner_eq_zero_symm

@[simp] lemma is_ortho_bot_left {V : submodule 𝕜 E} : ⊥ ⟂ V := bot_le
@[simp] lemma is_ortho_bot_right {U : submodule 𝕜 E} : U ⟂ ⊥ := is_ortho_bot_left.symm

lemma is_ortho.mono_left {U₁ U₂ V : submodule 𝕜 E} (hU : U₂ ≤ U₁) (h : U₁ ⟂ V) : U₂ ⟂ V :=
hU.trans h

lemma is_ortho.mono_right {U V₁ V₂ : submodule 𝕜 E} (hV : V₂ ≤ V₁) (h : U ⟂ V₁) : U ⟂ V₂ :=
(h.symm.mono_left hV).symm

lemma is_ortho.mono {U₁ V₁ U₂ V₂ : submodule 𝕜 E} (hU : U₂ ≤ U₁) (hV : V₂ ≤ V₁) (h : U₁ ⟂ V₁) :
  U₂ ⟂ V₂ :=
(h.mono_right hV).mono_left hU

@[simp]
lemma is_ortho_self {U : submodule 𝕜 E} : U ⟂ U ↔ U = ⊥ :=
⟨λ h, eq_bot_iff.mpr $ λ x hx, inner_self_eq_zero.mp (h hx x hx), λ h, h.symm ▸ is_ortho_bot_left⟩

@[simp] lemma self_is_ortho_orthogonal (U : submodule 𝕜 E) : U ⟂ Uᗮ :=
le_orthogonal_orthogonal _

@[simp] lemma orthogonal_is_ortho_self (U : submodule 𝕜 E) : Uᗮ ⟂ U :=
(self_is_ortho_orthogonal U).symm

@[simp]
lemma is_ortho_top_right {U : submodule 𝕜 E} : U ⟂ ⊤ ↔ U = ⊥ :=
⟨λ h, eq_bot_iff.mpr $ λ x hx, inner_self_eq_zero.mp (h hx _ mem_top),
  λ h, h.symm ▸ is_ortho_bot_left⟩

@[simp]
lemma is_ortho_top_left {V : submodule 𝕜 E} : ⊤ ⟂ V ↔ V = ⊥ :=
is_ortho_comm.trans is_ortho_top_right

/-- Orthogonal submodules are disjoint. -/
lemma is_ortho.disjoint {U V : submodule 𝕜 E} (h : U ⟂ V) : disjoint U V :=
(submodule.orthogonal_disjoint _).mono_right h.symm

@[simp] lemma is_ortho_sup_left {U₁ U₂ V : submodule 𝕜 E} : U₁ ⊔ U₂ ⟂ V ↔ U₁ ⟂ V ∧ U₂ ⟂ V :=
sup_le_iff

@[simp] lemma is_ortho_sup_right {U V₁ V₂ : submodule 𝕜 E} : U ⟂ V₁ ⊔ V₂ ↔ U ⟂ V₁ ∧ U ⟂ V₂ :=
is_ortho_comm.trans $ is_ortho_sup_left.trans $ is_ortho_comm.and is_ortho_comm

@[simp] lemma is_ortho_Sup_left {U : set (submodule 𝕜 E)} {V : submodule 𝕜 E} :
  Sup U ⟂ V ↔ ∀ Uᵢ ∈ U, Uᵢ ⟂ V :=
Sup_le_iff

@[simp] lemma is_ortho_Sup_right {U : submodule 𝕜 E} {V : set (submodule 𝕜 E)} :
  U ⟂ Sup V ↔ ∀ Vᵢ ∈ V, U ⟂ Vᵢ :=
is_ortho_comm.trans $ is_ortho_Sup_left.trans $ by simp_rw is_ortho_comm

@[simp] lemma is_ortho_supr_left {ι : Sort*} {U : ι → submodule 𝕜 E} {V : submodule 𝕜 E} :
  supr U ⟂ V ↔ ∀ i, U i ⟂ V :=
supr_le_iff

@[simp] lemma is_ortho_supr_right {ι : Sort*} {U : submodule 𝕜 E} {V : ι → submodule 𝕜 E} :
  U ⟂ supr V ↔ ∀ i, U ⟂ V i :=
is_ortho_comm.trans $ is_ortho_supr_left.trans $ by simp_rw is_ortho_comm

@[simp] lemma is_ortho_span {s t : set E} : span 𝕜 s ⟂ span 𝕜 t ↔ ∀ (u ∈ s) (v ∈ t), ⟪u, v⟫ = 0 :=
begin
  simp_rw [span_eq_supr_of_singleton_spans s, span_eq_supr_of_singleton_spans t,
    is_ortho_supr_left, is_ortho_supr_right, is_ortho_iff_le, span_le, set.subset_def,
    set_like.mem_coe, mem_orthogonal_singleton_iff_inner_left, set.mem_singleton_iff, forall_eq],
end

lemma is_ortho.map (f : E →ₗᵢ[𝕜] F) {U V : submodule 𝕜 E} (h : U ⟂ V) : U.map f ⟂ V.map f :=
begin
  rw is_ortho_iff_inner_eq at *,
  simp_rw [mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    linear_isometry.inner_map_map],
  exact h,
end

lemma is_ortho.comap (f : E →ₗᵢ[𝕜] F) {U V : submodule 𝕜 F} (h : U ⟂ V) : U.comap f ⟂ V.comap f :=
begin
  rw is_ortho_iff_inner_eq at *,
  simp_rw [mem_comap, ←f.inner_map_map],
  intros u hu v hv,
  exact h _ hu _ hv,
end

@[simp] lemma is_ortho.map_iff (f : E ≃ₗᵢ[𝕜] F) {U V : submodule 𝕜 E} : U.map f ⟂ V.map f ↔ U ⟂ V :=
⟨λ h, begin
  have hf : ∀ p : submodule 𝕜 E, (p.map f).comap f.to_linear_isometry = p :=
    comap_map_eq_of_injective f.injective,
  simpa only [hf] using h.comap f.to_linear_isometry,
end, is_ortho.map f.to_linear_isometry⟩

@[simp] lemma is_ortho.comap_iff (f : E ≃ₗᵢ[𝕜] F) {U V : submodule 𝕜 F} :
  U.comap f ⟂ V.comap f ↔ U ⟂ V :=
⟨λ h, begin
  have hf : ∀ p : submodule 𝕜 F, (p.comap f).map f.to_linear_isometry = p :=
    map_comap_eq_of_surjective f.surjective,
  simpa only [hf] using h.map f.to_linear_isometry,
end, is_ortho.comap f.to_linear_isometry⟩

end submodule

/-- Two submodules in an orthogonal family with different indices are orthogonal. -/
lemma orthogonal_family.is_ortho {ι} {V : ι → submodule 𝕜 E}
  (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ)) {i j : ι} (hij : i ≠ j) :
  V i ⟂ V j :=
λ x hx y hy, hV hij.symm ⟨y, hy⟩ ⟨x, hx⟩

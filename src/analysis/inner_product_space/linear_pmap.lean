/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.inner_product_space.basic
import topology.algebra.module.linear_pmap
import analysis.inner_product_space.projection
import analysis.inner_product_space.dual

/-!
# Linear Pmap

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


noncomputable theory
open is_R_or_C
open_locale complex_conjugate



variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [inner_product_space 𝕜 G]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

-- Todolist:
-- PR inner_* lemmas
-- PR compl lemmas
-- PR operator norm lemma


def is_formal_adjoint (T : linear_pmap 𝕜 E F) (S : linear_pmap 𝕜 F E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

@[simp] lemma inner_zero : @inner 𝕜 E _ 0 = 0 :=
funext (λ _, inner_zero_left)

lemma inner_add (x y : E) : @inner 𝕜 E _ (x + y) = @inner 𝕜 E _ x + @inner 𝕜 E _ y :=
funext (λ _, inner_add_left)

lemma inner_smul (a : 𝕜) (x : E) : @inner 𝕜 E _ (a • x) = (star_ring_end 𝕜) a • @inner 𝕜 E _ x :=
funext (λ _, inner_smul_left)

variables [complete_space E]

lemma sub_mem_compl_of_inner_left {x y : E} (S : submodule 𝕜 E)
  (h : ∀ (v : S), ⟪x, v⟫ = ⟪y, v⟫) : x - y ∈ Sᗮ :=
begin
  rw submodule.mem_orthogonal',
  intros u hu,
  rw inner_sub_left,
  rw sub_eq_zero,
  exact h ⟨u, hu⟩,
end

lemma sub_mem_compl_of_inner_right {x y : E} (S : submodule 𝕜 E)
  (h : ∀ (v : S), ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x - y ∈ Sᗮ :=
begin
  rw submodule.mem_orthogonal,
  intros u hu,
  rw inner_sub_right,
  rw sub_eq_zero,
  exact h ⟨u, hu⟩,
end

lemma ext_of_mem_dense_compl {x y : E} (S : submodule 𝕜 E) (hS : dense (S : set E))
  (h : x - y ∈ Sᗮ) : x = y :=
begin
  rw submodule.dense_iff_topological_closure_eq_top at hS,
  rw submodule.topological_closure_eq_top_iff at hS,
  rw hS at h,
  rw submodule.mem_bot at h,
  rwa sub_eq_zero at h,
end

lemma ext_inner_left_of_submodule {x y : E} (S : submodule 𝕜 E) (hS : dense (S : set E))
  (h : ∀ (v : S), ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
ext_of_mem_dense_compl S hS (sub_mem_compl_of_inner_left S h)

lemma ext_inner_right_of_submodule {x y : E} (S : submodule 𝕜 E) (hS : dense (S : set E))
  (h : ∀ (v : S), ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x = y :=
ext_of_mem_dense_compl S hS (sub_mem_compl_of_inner_right S h)

namespace linear_pmap

/-- The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred version to use is
`T.adjoint.domain` instead of `T.adjoint_domain`. -/
def adjoint_domain (T : linear_pmap 𝕜 E F) : submodule 𝕜 F :=
{ carrier := {y | continuous ((@inner 𝕜 _ _ y).comp T)},
  zero_mem' := by { simp only [set.mem_set_of_eq, inner_zero, pi.zero_comp],
    exact continuous_zero },
  add_mem' := λ x y hx hy, by { simp only [set.mem_set_of_eq, inner_add] at *, exact hx.add hy },
  smul_mem' := λ a x hx, by { simp only [set.mem_set_of_eq, inner_smul] at *,
    exact hx.const_smul (conj a) } }

variables (T : linear_pmap 𝕜 E F)

/-- The operator `λ x, ⟪y, T x⟫` considered as a continuous linear operator from `T.adjoint_domain`
to `𝕜`. -/
def adjoint_domain_mk_clm (y : T.adjoint_domain) : T.domain →L[𝕜] 𝕜 :=
⟨(innerₛₗ (y : F)).comp T.to_fun, y.prop⟩

lemma adjoint_domain_mk_clm_apply (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm T y x = ⟪(y : F), T x⟫ := rfl

variables [idom : fact (dense (T.domain : set E))]

include idom

/-- The unique continuous extension of the operator `adjoint_domain_mk_clm` to `E`. -/
def adjoint_domain_mk_clm_extend (y : T.adjoint_domain) : E →L[𝕜] 𝕜 :=
(adjoint_domain_mk_clm T y).extend (submodule.subtypeL T.domain)
  idom.out.dense_range_coe uniform_embedding_subtype_coe.to_uniform_inducing

-- Move to `operator_norm`
lemma adjoint_domain_mk_clm_extend_eq (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm_extend T y x = adjoint_domain_mk_clm T y x :=
dense_inducing.extend_eq _ (adjoint_domain_mk_clm T y).cont _

lemma adjoint_domain_mk_clm_extend_apply (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm_extend T y (x : E) = ⟪(y : F), T x⟫ :=
by rw [adjoint_domain_mk_clm_extend_eq, adjoint_domain_mk_clm_apply]

lemma exists_unique_adjoint_elem (y : T.adjoint_domain) : ∃! (w : E),
  ∀ (x : T.domain), ⟪w, x⟫ = ⟪(y : F), T x⟫ :=
begin
  refine exists_unique_of_exists_of_unique _ _,
  { use (inner_product_space.to_dual 𝕜 E).symm (T.adjoint_domain_mk_clm_extend y),
    intros x,
    simp only [inner_product_space.to_dual_symm_apply],
    rw adjoint_domain_mk_clm_extend_apply, },
  intros y₁ y₂ hy₁ hy₂,
  refine ext_inner_left_of_submodule _ idom.out _,
  intros v,
  rw [hy₁ v, hy₂ v],
end

/-- The image of the adjoint operator.

This is an auxiliary definition needed to define the adjoint operator as a `linear_pmap`. -/
def adjoint_elem (y : T.adjoint_domain) : E := (T.exists_unique_adjoint_elem y).exists.some

lemma adjoint_elem_spec (y : T.adjoint_domain) : ∀ (x : T.domain),
  ⟪T.adjoint_elem y, x⟫ = ⟪(y : F), T x⟫ := (T.exists_unique_adjoint_elem y).exists.some_spec

/-- The adjoint operator -/
def adjoint : F →ₗ.[𝕜] E :=
{ domain := T.adjoint_domain,
  to_fun := { to_fun := T.adjoint_elem,
    map_add' := λ _ _, ext_inner_left_of_submodule _ idom.out $ λ _,
      by simp only [inner_add_left, adjoint_elem_spec, submodule.coe_add],
    map_smul' := λ _ _, ext_inner_left_of_submodule _ idom.out $ λ _,
      by simp only [inner_smul_left, adjoint_elem_spec, submodule.coe_smul_of_tower,
        ring_hom.id_apply] } }

lemma adjoint_apply (y : T.adjoint.domain) : T.adjoint y = T.adjoint_elem y := rfl

/-- The fundamental property of the adjoint. -/
lemma inner_adjoint_apply (y : T.adjoint.domain) (x : T.domain) :
  ⟪T.adjoint y, x⟫ = ⟪(y : F), T x⟫ := T.adjoint_elem_spec _ _

lemma adjoint_is_formal_adjoint : is_formal_adjoint T.adjoint T :=
T.adjoint_elem_spec

lemma mem_adjoint_domain_iff (y : F) : y ∈ T.adjoint.domain ↔ continuous ((@inner 𝕜 _ _ y).comp T) :=
by refl

lemma mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ (x : T.domain), ⟪w, x⟫ = ⟪y, T x⟫) :
  y ∈ T.adjoint.domain :=
begin
  cases h with w hw,
  rw mem_adjoint_domain_iff,
  have : continuous ((innerSL w).comp T.domain.subtypeL) := by continuity,
  convert this,
  exact funext (λ x, (hw x).symm),
end


end linear_pmap

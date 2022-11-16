/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/

import analysis.inner_product_space.basic
import topology.algebra.module.linear_pmap
import analysis.inner_product_space.dual

/-!
# Partially defined linear operators on Hilbert spaces

We will develop the basics of the theory of unbounded operators on Hilbert spaces.

## Main definitions

* `linear_pmap.is_formal_adjoint`: An operator `T` is a formal adjoint of `S` if for all `x` in the
domain of `T` and `y` in the domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`.
* `linear_pmap.adjoint`: The adjoint of a map `E →ₗ.[𝕜] F` as a map `F →ₗ.[𝕜] E`.

## Main statements

* `linear_pmap.adjoint_is_formal_adjoint`: The adjoint is a formal adjoint

## Notation

* For `T : E →ₗ.[𝕜] F` the adjoint can be written as `T†`.
This notation is localized in `linear_pmap`.

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/


noncomputable theory
open is_R_or_C
open_locale complex_conjugate

variables {𝕜 E F G : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace linear_pmap

/-- An operator `T` is a formal adjoint of `S` if for all `x` in the domain of `T` and `y` in the
domain of `S`, we have that `⟪T x, y⟫ = ⟪x, S y⟫`. -/
def is_formal_adjoint (T : E →ₗ.[𝕜] F) (S : F →ₗ.[𝕜] E) : Prop :=
  ∀ (x : T.domain) (y : S.domain), ⟪T x, y⟫ = ⟪(x : E), S y⟫

/-- The domain of the adjoint operator.

This definition is needed to construct the adjoint operator and the preferred version to use is
`T.adjoint.domain` instead of `T.adjoint_domain`. -/
def adjoint_domain (T : E →ₗ.[𝕜] F) : submodule 𝕜 F :=
{ carrier := {y | continuous ((innerₛₗ y).comp T.to_fun)},
  zero_mem' := by { rw [set.mem_set_of_eq, linear_map.map_zero, linear_map.zero_comp],
      exact continuous_zero },
  add_mem' := λ x y hx hy, by { rw [set.mem_set_of_eq, linear_map.map_add] at *, exact hx.add hy },
  smul_mem' := λ a x hx, by { rw [set.mem_set_of_eq, linear_map.map_smulₛₗ] at *,
    exact hx.const_smul (conj a) } }

variables (T : E →ₗ.[𝕜] F)

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

@[simp] lemma adjoint_domain_mk_clm_extend_apply (y : T.adjoint_domain) (x : T.domain) :
  adjoint_domain_mk_clm_extend T y (x : E) = ⟪(y : F), T x⟫ :=
continuous_linear_map.extend_eq _ _ _ _ _

variables [complete_space E]

lemma exists_unique_adjoint_elem (y : T.adjoint_domain) : ∃! (w : E),
  ∀ (x : T.domain), ⟪w, x⟫ = ⟪(y : F), T x⟫ :=
exists_unique_of_exists_of_unique
  -- For the existence we use the Fréchet-Riesz representation theorem and extend
  -- the map that is only defined on `T.domain` to `E`:
  ⟨(inner_product_space.to_dual 𝕜 E).symm (T.adjoint_domain_mk_clm_extend y),
    -- Implementation note: this is true `by simp`
    by simp only [inner_product_space.to_dual_symm_apply, adjoint_domain_mk_clm_extend_apply,
      eq_self_iff_true, forall_const]⟩
  -- The uniqueness follows directly from the fact that `T.domain` is dense in `E`.
  (λ _ _ hy₁ hy₂, idom.out.eq_of_inner_left (λ v, (hy₁ v).trans (hy₂ v).symm))

/-- The image of the adjoint operator.

This is an auxiliary definition needed to define the adjoint operator as a `linear_pmap`. -/
def adjoint_elem (y : T.adjoint_domain) : E := (T.exists_unique_adjoint_elem y).exists.some

lemma adjoint_elem_spec (y : T.adjoint_domain) (x : T.domain) :
  ⟪T.adjoint_elem y, x⟫ = ⟪(y : F), T x⟫ :=
(T.exists_unique_adjoint_elem y).exists.some_spec _

/-- The adjoint operator as a partially defined linear operator. -/
def adjoint : F →ₗ.[𝕜] E :=
{ domain := T.adjoint_domain,
  to_fun := { to_fun := T.adjoint_elem,
    map_add' := λ _ _, idom.out.eq_of_inner_left $ λ _,
      by simp only [inner_add_left, adjoint_elem_spec, submodule.coe_add],
    map_smul' := λ _ _, idom.out.eq_of_inner_left $ λ _,
      by simp only [inner_smul_left, adjoint_elem_spec, submodule.coe_smul_of_tower,
        ring_hom.id_apply] } }

localized "postfix (name := adjoint) `†`:1100 := linear_pmap.adjoint" in linear_pmap

lemma adjoint_apply (y : T.adjoint.domain) : T† y = T.adjoint_elem y := rfl

/-- The fundamental property of the adjoint. -/
lemma adjoint_is_formal_adjoint : T†.is_formal_adjoint T :=
T.adjoint_elem_spec

lemma mem_adjoint_domain_iff (y : F) :
  y ∈ T†.domain ↔ continuous ((innerₛₗ y).comp T.to_fun) :=
by refl

lemma mem_adjoint_domain_of_exists (y : F) (h : ∃ w : E, ∀ (x : T.domain), ⟪w, x⟫ = ⟪y, T x⟫) :
  y ∈ T†.domain :=
begin
  cases h with w hw,
  rw mem_adjoint_domain_iff,
  have : continuous ((innerSL w).comp T.domain.subtypeL) := by continuity,
  convert this using 1,
  exact funext (λ x, (hw x).symm),
end

end linear_pmap

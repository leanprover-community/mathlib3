/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Frédéric Dupuis, Heather Macbeth
-/
import analysis.inner_product_space.basic
import analysis.normed_space.banach
import linear_algebra.sesquilinear_form

/-!
# Symmetric linear maps in an inner product space

This file defines and proves basic theorems about symmetric **not necessarily bounded** operators
on an inner product space, i.e linear maps `T : E → E` such that `∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫`.

In comparison to `is_self_adjoint`, this definition works for non-continuous linear maps, and
doesn't rely on the definition of the adjoint, which allows it to be stated in non-complete space.

## Main definitions

* `linear_map.is_symmetric`: a (not necessarily bounded) operator on an inner product space is
symmetric, if for all `x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`

## Main statements

* `is_symmetric.continuous`: if a symmetric operator is defined on a complete space, then
  it is automatically continuous.

## Tags

self-adjoint, symmetric
-/

open is_R_or_C
open_locale complex_conjugate

variables {𝕜 E E' F G : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space 𝕜 F] [inner_product_space 𝕜 G]
variables [inner_product_space ℝ E']
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

namespace linear_map

/-! ### Symmetric operators -/

/-- A (not necessarily bounded) operator on an inner product space is symmetric, if for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def is_symmetric (T : E →ₗ[𝕜] E) : Prop := ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

section real

variables

/-- An operator `T` on an inner product space is symmetric if and only if it is
`linear_map.is_self_adjoint` with respect to the sesquilinear form given by the inner product. -/
lemma is_symmetric_iff_sesq_form (T : E →ₗ[𝕜] E) :
  T.is_symmetric ↔
  @linear_map.is_self_adjoint 𝕜 E _ _ _ (star_ring_end 𝕜) sesq_form_of_inner T :=
⟨λ h x y, (h y x).symm, λ h x y, (h y x).symm⟩

end real

lemma is_symmetric.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : is_symmetric T) (x y : E) :
  conj ⟪T x, y⟫ = ⟪T y, x⟫ :=
by rw [hT x y, inner_conj_sym]

@[simp] lemma is_symmetric.apply_clm {T : E →L[𝕜] E} (hT : is_symmetric (T : E →ₗ[𝕜] E))
  (x y : E) : ⟪T x, y⟫ = ⟪x, T y⟫ :=
hT x y

lemma is_symmetric_zero : (0 : E →ₗ[𝕜] E).is_symmetric :=
λ x y, (inner_zero_right : ⟪x, 0⟫ = 0).symm ▸ (inner_zero_left : ⟪0, y⟫ = 0)

lemma is_symmetric_id : (linear_map.id : E →ₗ[𝕜] E).is_symmetric :=
λ x y, rfl

lemma is_symmetric.add {T S : E →ₗ[𝕜] E} (hT : T.is_symmetric) (hS : S.is_symmetric) :
  (T + S).is_symmetric :=
begin
  intros x y,
  rw [linear_map.add_apply, inner_add_left, hT x y, hS x y, ← inner_add_right],
  refl
end

/-- The **Hellinger--Toeplitz theorem**: if a symmetric operator is defined on a complete space,
  then it is automatically continuous. -/
lemma is_symmetric.continuous [complete_space E] {T : E →ₗ[𝕜] E} (hT : is_symmetric T) :
  continuous T :=
begin
  -- We prove it by using the closed graph theorem
  refine T.continuous_of_seq_closed_graph (λ u x y hu hTu, _),
  rw [←sub_eq_zero, ←inner_self_eq_zero],
  have hlhs : ∀ k : ℕ, ⟪T (u k) - T x, y - T x⟫ = ⟪u k - x, T (y - T x)⟫ :=
  by { intro k, rw [←T.map_sub, hT] },
  refine tendsto_nhds_unique ((hTu.sub_const _).inner tendsto_const_nhds) _,
  simp_rw hlhs,
  rw ←@inner_zero_left 𝕜 E _ _ (T (y - T x)),
  refine filter.tendsto.inner _ tendsto_const_nhds,
  rw ←sub_self x,
  exact hu.sub_const _,
end

/-- For a symmetric operator `T`, the function `λ x, ⟪T x, x⟫` is real-valued. -/
@[simp] lemma is_symmetric.coe_re_apply_inner_self_apply
  {T : E →L[𝕜] E} (hT : is_symmetric (T : E →ₗ[𝕜] E)) (x : E) :
  (T.re_apply_inner_self x : 𝕜) = ⟪T x, x⟫ :=
begin
  rsuffices ⟨r, hr⟩ : ∃ r : ℝ, ⟪T x, x⟫ = r,
  { simp [hr, T.re_apply_inner_self_apply] },
  rw ← eq_conj_iff_real,
  exact hT.conj_inner_sym x x
end

/-- If a symmetric operator preserves a submodule, its restriction to that submodule is
symmetric. -/
lemma is_symmetric.restrict_invariant {T : E →ₗ[𝕜] E} (hT : is_symmetric T)
  {V : submodule 𝕜 E} (hV : ∀ v ∈ V, T v ∈ V) :
  is_symmetric (T.restrict hV) :=
λ v w, hT v w

lemma is_symmetric.restrict_scalars {T : E →ₗ[𝕜] E} (hT : T.is_symmetric) :
  @linear_map.is_symmetric ℝ E _ (inner_product_space.is_R_or_C_to_real 𝕜 E)
  (@linear_map.restrict_scalars ℝ 𝕜 _ _ _ _ _ _
    (inner_product_space.is_R_or_C_to_real 𝕜 E).to_module
    (inner_product_space.is_R_or_C_to_real 𝕜 E).to_module _ _ _ T) :=
λ x y, by simp [hT x y, real_inner_eq_re_inner, linear_map.coe_restrict_scalars_eq_coe]

section complex

variables {V : Type*}
  [inner_product_space ℂ V]

/-- A linear operator on a complex inner product space is symmetric precisely when
`⟪T v, v⟫_ℂ` is real for all v.-/
lemma is_symmetric_iff_inner_map_self_real (T : V →ₗ[ℂ] V):
  is_symmetric T ↔ ∀ (v : V), conj ⟪T v, v⟫_ℂ = ⟪T v, v⟫_ℂ :=
begin
  split,
  { intros hT v,
    apply is_symmetric.conj_inner_sym hT },
  { intros h x y,
    nth_rewrite 1 ← inner_conj_sym,
    nth_rewrite 1 inner_map_polarization,
    simp only [star_ring_end_apply, star_div', star_sub, star_add, star_mul],
    simp only [← star_ring_end_apply],
    rw [h (x + y), h (x - y), h (x + complex.I • y), h (x - complex.I • y)],
    simp only [complex.conj_I],
    rw inner_map_polarization',
    norm_num,
    ring },
end

end complex

end linear_map

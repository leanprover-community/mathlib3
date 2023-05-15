/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import analysis.normed_space.basic

/-! # Constructions of continuous linear maps between (semi-)normed spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A fundamental fact about (semi-)linear maps between normed spaces over sensible fields is that
continuity and boundedness are equivalent conditions.  That is, for normed spaces `E`, `F`, a
`linear_map` `f : E →ₛₗ[σ] F` is the coercion of some `continuous_linear_map` `f' : E →SL[σ] F`, if
and only if there exists a bound `C` such that for all `x`, `‖f x‖ ≤ C * ‖x‖`.

We prove one direction in this file: `linear_map.mk_continuous`, boundedness implies continuity. The
other direction, `continuous_linear_map.bound`, is deferred to a later file, where the
strong operator topology on `E →SL[σ] F` is available, because it is natural to use
`continuous_linear_map.bound` to define a norm `⨆ x, ‖f x‖ / ‖x‖` on `E →SL[σ] F` and to show that
this is compatible with the strong operator topology.

This file also contains several corollaries of `linear_map.mk_continuous`: other "easy"
constructions of continuous linear maps between normed spaces.

This file is meant to be lightweight (it is imported by much of the analysis library); think twice
before adding imports!
-/

open metric continuous_linear_map
open set real

open_locale nnreal

variables {𝕜 𝕜₂ E F G : Type*}

variables [normed_field 𝕜] [normed_field 𝕜₂]

/-! # General constructions -/

section seminormed

variables [seminormed_add_comm_group E] [seminormed_add_comm_group F] [seminormed_add_comm_group G]
variables [normed_space 𝕜 E] [normed_space 𝕜₂ F] [normed_space 𝕜 G]
variables {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
⟨f, add_monoid_hom_class.continuous_of_bound f C h⟩

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def linear_map.to_continuous_linear_map₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
f.mk_continuous (‖f 1‖) $ λ x, le_of_eq $
by { conv_lhs { rw ← mul_one x }, rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm] }

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) : E →SL[σ] F :=
⟨f, let ⟨C, hC⟩ := h in add_monoid_hom_class.continuous_of_bound f C hC⟩

lemma continuous_of_linear_of_boundₛₗ {f : E → F} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = (σ c) • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C*‖x‖) :
  continuous f :=
let φ : E →ₛₗ[σ] F := { to_fun := f, map_add' := h_add, map_smul' := h_smul } in
add_monoid_hom_class.continuous_of_bound φ C h_bound

lemma continuous_of_linear_of_bound {f : E → G} (h_add : ∀ x y, f (x + y) = f x + f y)
  (h_smul : ∀ (c : 𝕜) x, f (c • x) = c • f x) {C : ℝ} (h_bound : ∀ x, ‖f x‖ ≤ C*‖x‖) :
  continuous f :=
let φ : E →ₗ[𝕜] G := { to_fun := f, map_add' := h_add, map_smul' := h_smul } in
add_monoid_hom_class.continuous_of_bound φ C h_bound

@[simp, norm_cast] lemma linear_map.mk_continuous_coe (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ((f.mk_continuous C h) : E →ₛₗ[σ] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_apply (C : ℝ) (h : ∀x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
  f.mk_continuous C h x = f x := rfl

@[simp, norm_cast] lemma linear_map.mk_continuous_of_exists_bound_coe
  (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) :
  ((f.mk_continuous_of_exists_bound h) : E →ₛₗ[σ] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_of_exists_bound_apply (h : ∃C, ∀x, ‖f x‖ ≤ C * ‖x‖) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x := rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_coe (f : 𝕜 →ₗ[𝕜] E) :
  (f.to_continuous_linear_map₁ : 𝕜 →ₗ[𝕜] E) = f :=
rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
  f.to_continuous_linear_map₁ x = f x :=
rfl

namespace continuous_linear_map

theorem antilipschitz_of_bound (f : E →SL[σ] F) {K : ℝ≥0} (h : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
  antilipschitz_with K f :=
add_monoid_hom_class.antilipschitz_of_bound _ h

lemma bound_of_antilipschitz (f : E →SL[σ] F) {K : ℝ≥0} (h : antilipschitz_with K f) (x) :
  ‖x‖ ≤ K * ‖f x‖ :=
add_monoid_hom_class.bound_of_antilipschitz _ h x

end continuous_linear_map

section

variables {σ₂₁ : 𝕜₂ →+* 𝕜} [ring_hom_inv_pair σ σ₂₁] [ring_hom_inv_pair σ₂₁ σ]

include σ₂₁

/-- Construct a continuous linear equivalence from a linear equivalence together with
bounds in both directions. -/
def linear_equiv.to_continuous_linear_equiv_of_bounds (e : E ≃ₛₗ[σ] F) (C_to C_inv : ℝ)
  (h_to : ∀ x, ‖e x‖ ≤ C_to * ‖x‖) (h_inv : ∀ x : F, ‖e.symm x‖ ≤ C_inv * ‖x‖) : E ≃SL[σ] F :=
{ to_linear_equiv := e,
  continuous_to_fun := add_monoid_hom_class.continuous_of_bound e C_to h_to,
  continuous_inv_fun := add_monoid_hom_class.continuous_of_bound e.symm C_inv h_inv }

end

end seminormed

section normed

variables [normed_add_comm_group E] [normed_add_comm_group F] [normed_space 𝕜 E] [normed_space 𝕜₂ F]
variables {σ : 𝕜 →+* 𝕜₂} (f g : E →SL[σ] F) (x y z : E)

theorem continuous_linear_map.uniform_embedding_of_bound {K : ℝ≥0} (hf : ∀ x, ‖x‖ ≤ K * ‖f x‖) :
  uniform_embedding f :=
(add_monoid_hom_class.antilipschitz_of_bound f hf).uniform_embedding f.uniform_continuous

end normed

/-! ## Homotheties -/

section seminormed

variables [seminormed_add_comm_group E] [seminormed_add_comm_group F]
variables [normed_space 𝕜 E] [normed_space 𝕜₂ F]
variables {σ : 𝕜 →+* 𝕜₂} (f : E →ₛₗ[σ] F)

/-- A (semi-)linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def continuous_linear_map.of_homothety (f : E →ₛₗ[σ] F) (a : ℝ) (hf : ∀x, ‖f x‖ = a * ‖x‖) :
  E →SL[σ] F :=
f.mk_continuous a (λ x, le_of_eq (hf x))

variables {σ₂₁ : 𝕜₂ →+* 𝕜} [ring_hom_inv_pair σ σ₂₁] [ring_hom_inv_pair σ₂₁ σ]

include σ₂₁

lemma continuous_linear_equiv.homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₛₗ[σ] F) :
  (∀ (x : E), ‖f x‖ = a * ‖x‖) → (∀ (y : F), ‖f.symm y‖ = a⁻¹ * ‖y‖) :=
begin
  intros hf y,
  calc ‖(f.symm) y‖ = a⁻¹ * (a * ‖ (f.symm) y‖) : _
  ... =  a⁻¹ * ‖f ((f.symm) y)‖ : by rw hf
  ... = a⁻¹ * ‖y‖ : by simp,
  rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul],
end

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
noncomputable def continuous_linear_equiv.of_homothety (f : E ≃ₛₗ[σ] F) (a : ℝ) (ha : 0 < a)
  (hf : ∀x, ‖f x‖ = a * ‖x‖) :
  E ≃SL[σ] F :=
linear_equiv.to_continuous_linear_equiv_of_bounds f a a⁻¹
  (λ x, (hf x).le) (λ x, (continuous_linear_equiv.homothety_inverse a ha f hf x).le)

end seminormed

/-! ## The span of a single vector -/

section seminormed

variables [seminormed_add_comm_group E] [normed_space 𝕜 E]

namespace continuous_linear_map

variable (𝕜)

lemma to_span_singleton_homothety (x : E) (c : 𝕜) :
  ‖linear_map.to_span_singleton 𝕜 E x c‖ = ‖x‖ * ‖c‖ :=
by {rw mul_comm, exact norm_smul _ _}

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `𝕜` to `E` by taking multiples of `x`.-/
def to_span_singleton (x : E) : 𝕜 →L[𝕜] E :=
of_homothety (linear_map.to_span_singleton 𝕜 E x) ‖x‖ (to_span_singleton_homothety 𝕜 x)

lemma to_span_singleton_apply (x : E) (r : 𝕜) : to_span_singleton 𝕜 x r = r • x :=
by simp [to_span_singleton, of_homothety, linear_map.to_span_singleton]

lemma to_span_singleton_add (x y : E) :
  to_span_singleton 𝕜 (x + y) = to_span_singleton 𝕜 x + to_span_singleton 𝕜 y :=
by { ext1, simp [to_span_singleton_apply], }

lemma to_span_singleton_smul' (𝕜') [normed_field 𝕜'] [normed_space 𝕜' E]
  [smul_comm_class 𝕜 𝕜' E] (c : 𝕜') (x : E) :
  to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
by { ext1, rw [to_span_singleton_apply, smul_apply, to_span_singleton_apply, smul_comm], }

lemma to_span_singleton_smul (c : 𝕜) (x : E) :
  to_span_singleton 𝕜 (c • x) = c • to_span_singleton 𝕜 x :=
to_span_singleton_smul' 𝕜 𝕜 c x

end continuous_linear_map

section

namespace continuous_linear_equiv

variable (𝕜)

lemma to_span_nonzero_singleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
  ‖linear_equiv.to_span_nonzero_singleton 𝕜 E x h c‖ = ‖x‖ * ‖c‖ :=
continuous_linear_map.to_span_singleton_homothety _ _ _

end continuous_linear_equiv

end

end seminormed

section normed

variables [normed_add_comm_group E] [normed_space 𝕜 E]

namespace continuous_linear_equiv
variable (𝕜)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural
    continuous linear equivalence from `E₁` to the span of `x`.-/
noncomputable def to_span_nonzero_singleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] (𝕜 ∙ x) :=
of_homothety
  (linear_equiv.to_span_nonzero_singleton 𝕜 E x h)
  ‖x‖
  (norm_pos_iff.mpr h)
  (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E₁` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
noncomputable def coord (x : E) (h : x ≠ 0) : (𝕜 ∙ x) →L[𝕜] 𝕜 :=
  (to_span_nonzero_singleton 𝕜 x h).symm

@[simp] lemma coe_to_span_nonzero_singleton_symm {x : E} (h : x ≠ 0) :
  ⇑(to_span_nonzero_singleton 𝕜 x h).symm = coord 𝕜 x h := rfl

@[simp] lemma coord_to_span_nonzero_singleton {x : E} (h : x ≠ 0) (c : 𝕜) :
  coord 𝕜 x h (to_span_nonzero_singleton 𝕜 x h c) = c :=
(to_span_nonzero_singleton 𝕜 x h).symm_apply_apply c

@[simp] lemma to_span_nonzero_singleton_coord {x : E} (h : x ≠ 0) (y : 𝕜 ∙ x) :
  to_span_nonzero_singleton 𝕜 x h (coord 𝕜 x h y) = y :=
(to_span_nonzero_singleton 𝕜 x h).apply_symm_apply y

@[simp] lemma coord_self (x : E) (h : x ≠ 0) :
  (coord 𝕜 x h) (⟨x, submodule.mem_span_singleton_self x⟩ : 𝕜 ∙ x) = 1 :=
linear_equiv.coord_self 𝕜 E x h

end continuous_linear_equiv

end normed

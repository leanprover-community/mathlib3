/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang
-/
import geometry.euclidean.basic
import geometry.manifold.charted_space
import analysis.normed_space.inner_product

/-!
# Conformal Maps on Inner Product Spaces

A map between real inner product spaces `X`, `Y` is `conformal_at` some point `x` in `X` if it is
real differentiable and its differential at that point is a nonzero constant multiple of
a linear isometry equivalence.

## Main results

* `conformal_at`: the main definition
* The conformality of the composition of two conformal maps, the identity map
  and multiplications by a constant
* `conformal_at_iff`: an equivalent definition of the conformality at some point
* `conformal_at.preserves_angle`: if a map is `conformal_at` some point, then its differential
                                  preserves all angles at that point

## Tags

conformal

## Warning

The definition of conformality in this file does NOT require the maps to be orientation-preserving.
Maps such as the conjugate function on the complex plane is considered as conformal maps.
-/

noncomputable theory

section loc_conformality

open linear_isometry continuous_linear_map
open_locale real_inner_product_space

/-- A continuous linear map `f'` is said to be conformal if it's
    a nonzero multiple of a linear isometry. -/
def is_conformal_map (R : Type*) {X Y : Type*} [nondiscrete_normed_field R]
  [normed_group X] [normed_group Y] [normed_space R X] [normed_space R Y]
  (f' : X →L[R] Y) :=
∃ (c : R) (hc : c ≠ 0) (li : X →ₗᵢ[R] Y), (f' : X → Y) = c • li

variables {E F : Type*} [inner_product_space ℝ E] [inner_product_space ℝ F]
  {X Y Z : Type*} [normed_group X] [normed_group Y] [normed_group Z]
  [normed_space ℝ X] [normed_space ℝ Y] [normed_space ℝ Z]
  {R M N G : Type*} [nondiscrete_normed_field R]
  [normed_group M] [normed_group N] [normed_group G]
  [normed_space R M] [normed_space R N] [normed_space R G]

lemma is_conformal_map_iff (f' : E →L[ℝ] F) :
  is_conformal_map ℝ f' ↔ ∃ (c : ℝ) (hc : 0 < c),
  ∀ (u v : E), ⟪f' u, f' v⟫ = (c : ℝ) * ⟪u, v⟫ :=
begin
  split,
  { rintros ⟨c₁, hc₁, li, h⟩,
    refine ⟨c₁ * c₁, mul_self_pos hc₁, λ u v, _⟩,
    simp only [h, pi.smul_apply, inner_map_map,
               real_inner_smul_left, real_inner_smul_right, mul_assoc], },
  { rintros ⟨c₁, hc₁, huv⟩,
    let c := real.sqrt c₁⁻¹,
    have hc : c ≠ 0 := λ w, by {simp only [c] at w;
      exact (real.sqrt_ne_zero'.mpr $ inv_pos.mpr hc₁) w},
    let f₁ := c • f',
    have minor : (f₁ : E → F) = c • f' := rfl,
    have minor' : (f' : E → F) = c⁻¹ • f₁ := by ext;
      simp_rw [minor, pi.smul_apply]; rw [smul_smul, inv_mul_cancel hc, one_smul],
    refine ⟨c⁻¹, inv_ne_zero hc, f₁.to_linear_map.isometry_of_inner (λ u v, _), minor'⟩,
    simp_rw [to_linear_map_eq_coe, continuous_linear_map.coe_coe, minor, pi.smul_apply],
    rw [real_inner_smul_left, real_inner_smul_right,
        huv u v, ← mul_assoc, ← mul_assoc,
        real.mul_self_sqrt $ le_of_lt $ inv_pos.mpr hc₁,
        inv_mul_cancel $ ne_of_gt hc₁, one_mul], },
end

namespace is_conformal_map

lemma comp {f' : M →L[R] N} {g' : N →L[R] G}
  (hf' : is_conformal_map R f') (hg' : is_conformal_map R g') :
  is_conformal_map R (g'.comp f') :=
begin
  rcases hf' with ⟨cf, hcf, lif, hlif⟩,
  rcases hg' with ⟨cg, hcg, lig, hlig⟩,
  refine ⟨cg * cf, mul_ne_zero hcg hcf, lig.comp lif, funext (λ x, _)⟩,
  simp only [coe_comp', linear_isometry.coe_comp, hlif, hlig, pi.smul_apply,
             function.comp_app, linear_isometry.map_smul, smul_smul],
end

lemma preserves_angle (f' : E →L[ℝ] F) (h : is_conformal_map ℝ f') (u v : E) :
  inner_product_geometry.angle (f' u) (f' v) = inner_product_geometry.angle u v :=
begin
  obtain ⟨c, hc, li, hcf⟩ := h,
  suffices : c * (c * inner u v) / (∥c∥ * ∥u∥ * (∥c∥ * ∥v∥)) = inner u v / (∥u∥ * ∥v∥),
  { simp [this, inner_product_geometry.angle, hcf, norm_smul, inner_smul_left, inner_smul_right] },
  by_cases hu : ∥u∥ = 0,
  { simp [norm_eq_zero.mp hu] },
  by_cases hv : ∥v∥ = 0,
  { simp [norm_eq_zero.mp hv] },
  have hc : ∥c∥ ≠ 0 := λ w, hc (norm_eq_zero.mp w),
  field_simp,
  have : c * c = ∥c∥ * ∥c∥ := by simp [real.norm_eq_abs, abs_mul_abs_self],
  convert congr_arg (λ x, x * ⟪u, v⟫ * ∥u∥ * ∥v∥) this using 1; ring,
end

end is_conformal_map

/-- A map `f` is said to be conformal if it has a conformal differential `f'`. -/
def conformal_at {X Y : Type*}
  [normed_group X] [normed_group Y] [normed_space ℝ X] [normed_space ℝ Y]
  (f : X → Y) (x : X) :=
∃ (f' : X →L[ℝ] Y), has_fderiv_at f f' x ∧ is_conformal_map ℝ f'

lemma conformal_at_id {X : Type*}
  [normed_group X] [normed_space ℝ X] (x : X) : conformal_at id x :=
⟨id ℝ X, has_fderiv_at_id _, 1, one_ne_zero, id, by ext; simp⟩

lemma conformal_at_const_smul {X : Type*}
  [normed_group X] [normed_space ℝ X] {c : ℝ} (h : c ≠ 0) (x : X) :
  conformal_at (λ (x': X), c • x') x :=
⟨c • continuous_linear_map.id ℝ X, has_fderiv_at.const_smul (has_fderiv_at_id x) c,
  c, h, id, by ext; simp⟩

namespace conformal_at

lemma differentiable_at {f : X → Y} {x : X} (h : conformal_at f x) :
  differentiable_at ℝ f x :=
let ⟨_, h₁, _, _, _, _⟩ := h in h₁.differentiable_at

lemma comp {f : X → Y} {g : Y → Z} (x : X)
  (hg : conformal_at g (f x)) (hf : conformal_at f x)  : conformal_at (g ∘ f) x :=
begin
  rcases hf with ⟨f', hf₁, cf, hcf, lif, hf₂⟩,
  rcases hg with ⟨g', hg₁, cg, hcg, lig, hg₂⟩,
  exact ⟨g'.comp f', has_fderiv_at.comp x hg₁ hf₁, cf.comp cg⟩,
end

lemma const_smul {f : X → Y} {x : X} {c : ℝ} (hc : c ≠ 0) (hf : conformal_at f x) :
  conformal_at (c • f) x :=
(conformal_at_const_smul hc $ f x).comp x hf

/-- A real differentiable map `f` is conformal at point `x` if and only if
    its differential `f'` at that point scales any inner product by a positive scalar. -/
lemma _root_.conformal_at_iff {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) : conformal_at f x ↔ ∃ (c : ℝ) (hc : 0 < c),
  ∀ (u v : E), ⟪f' u, f' v⟫ = (c : ℝ) * ⟪u, v⟫ :=
begin
  split,
  { rintros ⟨f₁, hf, c₁, hc₁, li, hf₁⟩,
    exact (hf.unique h) ▸ (is_conformal_map_iff f₁).mp ⟨c₁, hc₁, li, hf₁⟩, },
  { rintros ⟨c, hc, huv⟩,
    exact ⟨f', h, (is_conformal_map_iff f').mpr ⟨c, hc, huv⟩⟩, },
end

/-- The conformal factor of a conformal map at some point `x`. Some authors refer to this function
    as the characteristic function of the conformal map. -/
def conformal_factor_at {f : E → F} (x : E) {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) : ℝ :=
by choose c hc huv using (conformal_at_iff h).mp H; exact c

/-- If a real differentiable map `f` is conformal at a point `x`,
    then it preserves the angles at that point. -/
lemma _root_.preserves_angle {f : E → F} {x : E} {f' : E →L[ℝ] F}
  (h : has_fderiv_at f f' x) (H : conformal_at f x) (u v : E) :
  inner_product_geometry.angle (f' u) (f' v) = inner_product_geometry.angle u v :=
let ⟨f₁, h₁, c⟩ := H in h₁.unique h ▸ c.preserves_angle f₁ u v

end conformal_at


/-- A map `f` is conformal on a set `s` if it's conformal at every point in that set. -/
def conformal_on (f : X → Y) (s : set X) :=
∀ (x : X), x ∈ s → conformal_at f x

namespace conformal_on

lemma conformal_at {f : X → Y} {u : set X} (h : conformal_on f u) {x : X} (hx : x ∈ u) :
conformal_at f x := h x hx

lemma comp {f : X → Y} {g : Y → Z}
  {u : set X} {v : set Y} (hf : conformal_on f u) (hg : conformal_on g v) :
  conformal_on (g ∘ f) (u ∩ f⁻¹' v) :=
λ x hx, (hg (f x) $ set.mem_preimage.mp hx.2).comp x (hf x hx.1)

lemma congr {f : X → X} {g : X → X}
  {u : set X} (hu : is_open u) (h : ∀ (x : X), x ∈ u → g x = f x) (hf : conformal_on f u) :
  conformal_on g u :=
λ x hx, begin
  obtain ⟨f', h₁, c⟩ := hf x hx,
  refine ⟨f', h₁.congr_of_eventually_eq _, c⟩,
  rw filter.eventually_eq_iff_exists_mem,
  exact ⟨u, hu.mem_nhds hx, h⟩,
end

end conformal_on

end loc_conformality

section global_conformality

variables {X Y Z : Type*}
  [normed_group X] [normed_group Y] [normed_group Z]
  [normed_space ℝ X] [normed_space ℝ Y] [normed_space ℝ Z]

/-- A map `f` is conformal if it's conformal at every point. -/
def conformal (f : X → Y) :=
∀ (x : X), conformal_at f x

lemma conformal_id : conformal (id : X → X) := λ x, conformal_at_id x

lemma conformal_const_smul {c : ℝ} (h : c ≠ 0) : conformal (λ (x : X), c • x) :=
λ x, conformal_at_const_smul h x

namespace conformal

lemma conformal_at {f : X → Y} (h : conformal f) (x : X) : conformal_at f x := h x

lemma conformal_on {f : X → Y} (h : conformal f) : conformal_on f set.univ := λ x hx, h x

lemma differentiable {f : X → Y} (h : conformal f) : differentiable ℝ f :=
λ x, (h x).differentiable_at

lemma comp {f : X → Y} {g : Y → Z} (hf : conformal f) (hg : conformal g) : conformal (g ∘ f) :=
λ x, (hg $ f x).comp x (hf x)

lemma const_smul {f : X → Y} (hf : conformal f) {c : ℝ} (hc : c ≠ 0) : conformal (c • f) :=
λ x, (hf x).const_smul hc

end conformal

end global_conformality

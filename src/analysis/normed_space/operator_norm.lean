/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo

Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.
-/

import topology.metric_space.lipschitz analysis.normed_space.riesz_lemma
import analysis.asymptotics
noncomputable theory
open_locale classical

set_option class.instance_max_depth 70

variables {𝕜 : Type*} {E : Type*} {F : Type*} {G : Type*}
[normed_group E] [normed_group F] [normed_group G]

open metric continuous_linear_map

lemma exists_pos_bound_of_bound {f : E → F} (M : ℝ) (h : ∀x, ∥f x∥ ≤ M * ∥x∥) :
  ∃ N, 0 < N ∧ ∀x, ∥f x∥ ≤ N * ∥x∥ :=
⟨max M 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), λx, calc
  ∥f x∥ ≤ M * ∥x∥ : h x
  ... ≤ max M 1 * ∥x∥ : mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _) ⟩

section normed_field
/- Most statements in this file require the field to be non-discrete, as this is necessary
to deduce an inequality `∥f x∥ ≤ C ∥x∥` from the continuity of f. However, the other direction always
holds. In this section, we just assume that `𝕜` is a normed field. In the remainder of the file,
it will be non-discrete. -/

variables [normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] (f : E →ₗ[𝕜] F)

lemma linear_map.lipschitz_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (nnreal.of_real C) f :=
lipschitz_with.of_dist_le $ λ x y, by simpa [dist_eq_norm] using h (x - y)

lemma linear_map.uniform_continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  uniform_continuous f :=
(f.lipschitz_of_bound C h).to_uniform_continuous

lemma linear_map.continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).to_continuous

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, linear_map.continuous_of_bound f C h⟩

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, let ⟨C, hC⟩ := h in linear_map.continuous_of_bound f C hC⟩

@[simp, elim_cast] lemma linear_map.mk_continuous_coe (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous C h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_apply (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous C h x = f x := rfl

@[simp, elim_cast] lemma linear_map.mk_continuous_of_exists_bound_coe (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous_of_exists_bound h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_of_exists_bound_apply (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x := rfl

lemma linear_map.continuous_iff_is_closed_ker {f : E →ₗ[𝕜] 𝕜} :
  continuous f ↔ is_closed (f.ker : set E) :=
begin
  -- the continuity of f obviously implies that its kernel is closed
  refine ⟨λh, (continuous_iff_is_closed.1 h) {0} (t1_space.t1 0), λh, _⟩,
  -- for the other direction, we assume that the kernel is closed
  by_cases hf : ∀x, x ∈ f.ker,
  { -- if `f = 0`, its continuity is obvious
    have : (f : E → 𝕜) = (λx, 0), by { ext x, simpa using hf x },
    rw this,
    exact continuous_const },
  { /- if `f` is not zero, we use an element `x₀ ∉ ker f` such that `∥x₀∥ ≤ 2 ∥x₀ - y∥` for all
    `y ∈ ker f`, given by Riesz's lemma, and prove that `2 ∥f x₀∥ / ∥x₀∥` gives a bound on the
    operator norm of `f`. For this, start from an arbitrary `x` and note that
    `y = x₀ - (f x₀ / f x) x` belongs to the kernel of `f`. Applying the above inequality to `x₀`
    and `y` readily gives the conclusion. -/
    push_neg at hf,
    let r : ℝ := (2 : ℝ)⁻¹,
    have : 0 ≤ r, by norm_num [r],
    have : r < 1, by norm_num [r],
    obtain ⟨x₀, x₀ker, h₀⟩ : ∃ (x₀ : E), x₀ ∉ f.ker ∧ ∀ y ∈ linear_map.ker f, r * ∥x₀∥ ≤ ∥x₀ - y∥,
      from riesz_lemma h hf this,
    have : x₀ ≠ 0,
    { assume h,
      have : x₀ ∈ f.ker, by { rw h, exact (linear_map.ker f).zero },
      exact x₀ker this },
    have rx₀_ne_zero : r * ∥x₀∥ ≠ 0, by { simp [norm_eq_zero, this], norm_num },
    have : ∀x, ∥f x∥ ≤ (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥,
    { assume x,
      by_cases hx : f x = 0,
      { rw [hx, norm_zero],
        apply_rules [mul_nonneg', norm_nonneg, inv_nonneg.2, norm_nonneg] },
      { let y := x₀ - (f x₀ * (f x)⁻¹ ) • x,
        have fy_zero : f y = 0, by calc
          f y = f x₀ - (f x₀ * (f x)⁻¹ ) * f x :
            by { dsimp [y], rw [f.map_add, f.map_neg, f.map_smul], refl }
          ... = 0 :
            by { rw [mul_assoc, inv_mul_cancel hx, mul_one, sub_eq_zero_of_eq], refl },
        have A : r * ∥x₀∥ ≤ ∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥, from calc
          r * ∥x₀∥ ≤ ∥x₀ - y∥ : h₀ _ (linear_map.mem_ker.2 fy_zero)
          ... = ∥(f x₀ * (f x)⁻¹ ) • x∥ : by { dsimp [y], congr, abel }
          ... = ∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥ :
            by rw [norm_smul, normed_field.norm_mul, normed_field.norm_inv],
        calc
          ∥f x∥ = (r * ∥x₀∥)⁻¹ * (r * ∥x₀∥) * ∥f x∥ : by rwa [inv_mul_cancel, one_mul]
          ... ≤ (r * ∥x₀∥)⁻¹ * (∥f x₀∥ * ∥f x∥⁻¹ * ∥x∥) * ∥f x∥ : begin
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left A _) (norm_nonneg _),
            exact inv_nonneg.2 (mul_nonneg' (by norm_num) (norm_nonneg _))
          end
          ... = (∥f x∥ ⁻¹ * ∥f x∥) * (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥ : by ring
          ... = (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥ :
            by { rw [inv_mul_cancel, one_mul], simp [norm_eq_zero, hx] } } },
    exact linear_map.continuous_of_bound f _ this }
end

end normed_field

variables [nondiscrete_normed_field 𝕜] [normed_space 𝕜 E] [normed_space 𝕜 F] [normed_space 𝕜 G]
(c : 𝕜) (f g : E →L[𝕜] F) (h : F →L[𝕜] G) (x y z : E)
include 𝕜

/-- A continuous linear map between normed spaces is bounded when the field is nondiscrete.
The continuity ensures boundedness on a ball of some radius `δ`. The nondiscreteness is then
used to rescale any element into an element of norm in `[δ/C, δ]`, whose image has a controlled norm.
The norm control for the original element follows by rescaling. -/
lemma linear_map.bound_of_continuous (f : E →ₗ[𝕜] F) (hf : continuous f) :
  ∃ C, 0 < C ∧ (∀ x : E, ∥f x∥ ≤ C * ∥x∥) :=
begin
  have : continuous_at f 0 := continuous_iff_continuous_at.1 hf _,
  rcases metric.tendsto_nhds_nhds.1 this 1 zero_lt_one with ⟨ε, ε_pos, hε⟩,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos ε_pos,
  have H : ∀{a}, ∥a∥ ≤ δ → ∥f a∥ ≤ 1,
  { assume a ha,
    have : dist (f a) (f 0) ≤ 1,
    { apply le_of_lt (hε _),
      rw [dist_eq_norm, sub_zero],
      exact lt_of_le_of_lt ha (half_lt_self ε_pos) },
    simpa using this },
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine ⟨δ⁻¹ * ∥c∥, mul_pos (inv_pos δ_pos) (lt_trans zero_lt_one hc), (λx, _)⟩,
  by_cases h : x = 0,
  { simp only [h, norm_zero, mul_zero, linear_map.map_zero] },
  { rcases rescale_to_shell hc δ_pos h with ⟨d, hd, dxle, ledx, dinv⟩,
    calc ∥f x∥
      = ∥f ((d⁻¹ * d) • x)∥ : by rwa [inv_mul_cancel, one_smul]
      ... = ∥d∥⁻¹ * ∥f (d • x)∥ :
        by rw [mul_smul, linear_map.map_smul, norm_smul, normed_field.norm_inv]
      ... ≤ ∥d∥⁻¹ * 1 :
        mul_le_mul_of_nonneg_left (H dxle) (by { rw ← normed_field.norm_inv, exact norm_nonneg _ })
      ... ≤ δ⁻¹ * ∥c∥ * ∥x∥ : by { rw mul_one, exact dinv } }
end

namespace continuous_linear_map

theorem bound : ∃ C, 0 < C ∧ (∀ x : E, ∥f x∥ ≤ C * ∥x∥) :=
f.to_linear_map.bound_of_continuous f.2

section
open asymptotics filter

theorem is_O_id (l : filter E) : is_O f (λ x, x) l :=
let ⟨M, hMp, hM⟩ := f.bound in is_O_of_le' l hM

theorem is_O_comp {E : Type*} (g : F →L[𝕜] G) (f : E → F) (l : filter E) :
  is_O (λ x', g (f x')) f l :=
(g.is_O_id ⊤).comp_tendsto lattice.le_top

theorem is_O_sub (f : E →L[𝕜] F) (l : filter E) (x : E) :
  is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
f.is_O_comp _ l

end

section op_norm
open set real

set_option class.instance_max_depth 100

/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm := Inf { c | c ≥ 0 ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ }
instance has_op_norm : has_norm (E →L[𝕜] F) := ⟨op_norm⟩

-- So that invocations of `real.Inf_le` make sense: we show that the set of
-- bounds is nonempty and bounded below.
lemma bounds_nonempty {f : E →L[𝕜] F} :
  ∃ c, c ∈ { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
let ⟨M, hMp, hMb⟩ := f.bound in ⟨M, le_of_lt hMp, hMb⟩

lemma bounds_bdd_below {f : E →L[𝕜] F} :
  bdd_below { c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥ } :=
⟨0, λ _ ⟨hn, _⟩, hn⟩

lemma op_norm_nonneg : 0 ≤ ∥f∥ :=
lb_le_Inf _ bounds_nonempty (λ _ ⟨hx, _⟩, hx)

/-- The fundamental property of the operator norm: `∥f x∥ ≤ ∥f∥ * ∥x∥`. -/
theorem le_op_norm : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
classical.by_cases
  (λ heq : x = 0, by { rw heq, simp })
  (λ hne, have hlt : 0 < ∥x∥, from (norm_pos_iff _).2 hne,
    le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by { rw mul_comm, apply hc }))))

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
(or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by { rw mul_comm, apply le_op_norm }))
  (λ heq, by { rw [←heq, div_zero], apply op_norm_nonneg }))

/-- The image of the unit ball under a continuous linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
λ hx, begin
  rw [←(mul_one ∥f∥)],
  calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
  ...    ≤ _ : mul_le_mul_of_nonneg_left hx (op_norm_nonneg _)
end

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
Inf_le _ bounds_bdd_below
  ⟨add_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x, by { rw add_mul,
    exact norm_add_le_of_le (le_op_norm _ _) (le_op_norm _ _) }⟩

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, continuous_linear_map.ext (λ x, (norm_le_zero_iff _).1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

@[simp] lemma norm_zero : ∥(0 : E →L[𝕜] F)∥ = 0 :=
by rw op_norm_zero_iff

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
lemma norm_id : ∥(id : E →L[𝕜] E)∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- The operator norm is homogeneous. -/
lemma op_norm_smul : ∥c • f∥ = ∥c∥ * ∥f∥ :=
le_antisymm
  (Inf_le _ bounds_bdd_below
    ⟨mul_nonneg (norm_nonneg _) (op_norm_nonneg _), λ _,
    begin
      erw [norm_smul, mul_assoc],
      exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
    end⟩)
  (lb_le_Inf _ bounds_nonempty (λ _ ⟨hn, hc⟩,
    (or.elim (lt_or_eq_of_le (norm_nonneg c))
      (λ hlt,
        begin
          rw mul_comm,
          exact mul_le_of_le_div hlt (Inf_le _ bounds_bdd_below
          ⟨div_nonneg hn hlt, λ _,
          (by { rw div_mul_eq_mul_div, exact le_div_of_mul_le hlt
          (by { rw [ mul_comm, ←norm_smul ], exact hc _ }) })⟩)
        end)
      (λ heq, by { rw [←heq, zero_mul], exact hn }))))

lemma op_norm_neg : ∥-f∥ = ∥f∥ := calc
  ∥-f∥ = ∥(-1:𝕜) • f∥ : by rw neg_one_smul
  ... = ∥(-1:𝕜)∥ * ∥f∥ : by rw op_norm_smul
  ... = ∥f∥ : by simp

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (E →L[𝕜] F) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space : normed_space 𝕜 (E →L[𝕜] F) :=
⟨op_norm_smul⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le : ∥comp h f∥ ≤ ∥h∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
  begin
    rw mul_assoc,
    calc _ ≤ ∥h∥ * ∥f x∥: le_op_norm _ _
    ... ≤ _ : mul_le_mul_of_nonneg_left
              (le_op_norm _ _) (op_norm_nonneg _)
  end⟩)

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ⟨∥f∥, op_norm_nonneg f⟩ f :=
λ x y, by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }

/-- A continuous linear map is automatically uniformly continuous. -/
protected theorem uniform_continuous : uniform_continuous f :=
f.lipschitz.to_uniform_continuous

variable {f}
/-- A continuous linear map is an isometry if and only if it preserves the norm. -/
lemma isometry_iff_norm_image_eq_norm :
  isometry f ↔ ∀x, ∥f x∥ = ∥x∥ :=
begin
  rw isometry_emetric_iff_metric,
  split,
  { assume H x,
    have := H x 0,
    rwa [dist_eq_norm, dist_eq_norm, f.map_zero, sub_zero, sub_zero] at this },
  { assume H x y,
    rw [dist_eq_norm, dist_eq_norm, ← f.map_sub, H] }
end

variable (f)
/-- A continuous linear map is a uniform embedding if it expands the norm by a constant factor. -/
theorem uniform_embedding_of_bound (C : ℝ) (hC : ∀x, ∥x∥ ≤ C * ∥f x∥) :
  uniform_embedding f :=
begin
  have Cpos : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _),
  refine uniform_embedding_iff'.2 ⟨metric.uniform_continuous_iff.1 f.uniform_continuous,
                                    λδ δpos, ⟨δ / (max C 1), div_pos δpos Cpos, λx y hxy, _⟩⟩,
  calc dist x y = ∥x - y∥ : by rw dist_eq_norm
  ... ≤ C * ∥f (x - y)∥ : hC _
  ... = C * dist (f x) (f y) : by rw [f.map_sub, dist_eq_norm]
  ... ≤ max C 1 * dist (f x) (f y) :
    mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  ... < max C 1 * (δ / max C 1) : mul_lt_mul_of_pos_left hxy Cpos
  ... = δ : by { rw mul_comm, exact div_mul_cancel _ (ne_of_lt Cpos).symm }
end

/-- If a continuous linear map is a uniform embedding, then it expands the norm by a positive
factor.-/
theorem bound_of_uniform_embedding (hf : uniform_embedding f) :
  ∃ C : ℝ, 0 < C ∧ ∀x, ∥x∥ ≤ C * ∥f x∥ :=
begin
  obtain ⟨ε, εpos, hε⟩ : ∃ (ε : ℝ) (H : ε > 0), ∀ {x y : E}, dist (f x) (f y) < ε → dist x y < 1, from
    (uniform_embedding_iff.1 hf).2.2 1 zero_lt_one,
  let δ := ε/2,
  have δ_pos : δ > 0 := half_pos εpos,
  have H : ∀{x}, ∥f x∥ ≤ δ → ∥x∥ ≤ 1,
  { assume x hx,
    have : dist x 0 ≤ 1,
    { apply le_of_lt,
      apply hε,
      simp [dist_eq_norm],
      exact lt_of_le_of_lt hx (half_lt_self εpos) },
  simpa using this },
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  refine ⟨δ⁻¹ * ∥c∥, (mul_pos (inv_pos δ_pos) ((lt_trans zero_lt_one hc))), (λx, _)⟩,
  by_cases hx : f x = 0,
  { have : f x = f 0, by { simp [hx] },
    have : x = 0 := (uniform_embedding_iff.1 hf).1 this,
    simp [this] },
  { rcases rescale_to_shell hc δ_pos hx with ⟨d, hd, dxle, ledx, dinv⟩,
    have : ∥f (d • x)∥ ≤ δ, by simpa,
    have : ∥d • x∥ ≤ 1 := H this,
    calc ∥x∥ = ∥d∥⁻¹ * ∥d • x∥ :
      by rwa [← normed_field.norm_inv, ← norm_smul, ← mul_smul, inv_mul_cancel, one_smul]
    ... ≤ ∥d∥⁻¹ * 1 :
      mul_le_mul_of_nonneg_left this (inv_nonneg.2 (norm_nonneg _))
    ... ≤ δ⁻¹ * ∥c∥ * ∥f x∥ :
      by rwa [mul_one] }
end

section uniformly_extend

variables [complete_space F] (e : E →L[𝕜] G) (h_dense : dense_range e)

section
variables (h_e : uniform_inducing e)

/-- Extension of a continuous linear map `f : E →L[𝕜] F`, with `E` a normed space and `F` a complete
    normed space, along a uniform and dense embedding `e : E →L[𝕜] G`.  -/
def extend : G →L[𝕜] F :=
/- extension of `f` is continuous -/
have cont : _ := (uniform_continuous_uniformly_extend h_e h_dense f.uniform_continuous).continuous,
/- extension of `f` agrees with `f` on the domain of the embedding `e` -/
have eq : _ := uniformly_extend_of_ind h_e h_dense f.uniform_continuous,
{ to_fun := (h_e.dense_inducing h_dense).extend f,
  add :=
  begin
    refine is_closed_property2 h_dense (is_closed_eq _ _) _,
    { exact cont.comp (continuous_fst.add continuous_snd) },
    { exact (cont.comp continuous_fst).add (cont.comp continuous_snd) },
    { assume x y, rw ← e.map_add, simp only [eq], exact f.map_add _ _  },
  end,
  smul := λk,
  begin
    refine is_closed_property h_dense (is_closed_eq _ _) _,
    { exact cont.comp (continuous_const.smul continuous_id)  },
    { exact (continuous_const.smul continuous_id).comp cont },
    { assume x, rw ← map_smul, simp only [eq], exact map_smul _ _ _  },
  end,
  cont := cont
}

@[simp] lemma extend_zero : extend (0 : E →L[𝕜] F) e h_dense h_e = 0 :=
begin
  apply ext,
  refine is_closed_property h_dense (is_closed_eq _ _) _,
  { exact (uniform_continuous_uniformly_extend h_e h_dense uniform_continuous_const).continuous },
  { simp only [zero_apply], exact continuous_const },
  { assume x, exact uniformly_extend_of_ind h_e h_dense uniform_continuous_const x }
end

end

section
variables {N : ℝ} (h_e : ∀x, ∥x∥ ≤ N * ∥e x∥)

local notation `ψ` := f.extend e h_dense (uniform_embedding_of_bound _ _ h_e).to_uniform_inducing

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the norm
    of the extension of `f` along `e` is bounded by `N * ∥f∥`. -/
lemma op_norm_extend_le : ∥ψ∥ ≤ N * ∥f∥ :=
begin
  have uni : uniform_inducing e := (uniform_embedding_of_bound _ _ h_e).to_uniform_inducing,
  have eq : ∀x, ψ (e x) = f x := uniformly_extend_of_ind uni h_dense f.uniform_continuous,
  by_cases N0 : 0 ≤ N,
  { refine op_norm_le_bound ψ _ (is_closed_property h_dense (is_closed_le _ _) _),
    { exact mul_nonneg N0 (norm_nonneg _) },
    { exact continuous_norm.comp (cont ψ) },
    { exact continuous_const.mul continuous_norm },
    { assume x,
      rw eq,
      calc ∥f x∥ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
        ... ≤ ∥f∥ * (N * ∥e x∥) : mul_le_mul_of_nonneg_left (h_e x) (norm_nonneg _)
        ... ≤ N * ∥f∥ * ∥e x∥ : by rw [mul_comm N ∥f∥, mul_assoc] } },
  { have he : ∀ x : E, x = 0,
    { assume x,
      have N0 : N ≤ 0 := le_of_lt (lt_of_not_ge N0),
      rw ← norm_le_zero_iff,
      exact le_trans (h_e x) (mul_nonpos_of_nonpos_of_nonneg N0 (norm_nonneg _)) },
    have hf : f = 0, { ext, simp only [he x, zero_apply, map_zero] },
    have hψ : ψ = 0, { rw hf, apply extend_zero },
    rw [hψ, hf, norm_zero, norm_zero, mul_zero] }
end

end

end uniformly_extend

end op_norm

/-- The norm of the tensor product of a scalar linear map and of an element of a normed space
is the product of the norms. -/
@[simp] lemma smul_right_norm {c : E →L[𝕜] 𝕜} {f : F} :
  ∥smul_right c f∥ = ∥c∥ * ∥f∥ :=
begin
  refine le_antisymm _ _,
  { apply op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (λx, _),
    calc
     ∥(c x) • f∥ = ∥c x∥ * ∥f∥ : norm_smul _ _
     ... ≤ (∥c∥ * ∥x∥) * ∥f∥ :
       mul_le_mul_of_nonneg_right (le_op_norm _ _) (norm_nonneg _)
     ... = ∥c∥ * ∥f∥ * ∥x∥ : by ring },
  { by_cases h : ∥f∥ = 0,
    { rw h, simp [norm_nonneg] },
    { have : 0 < ∥f∥ := lt_of_le_of_ne (norm_nonneg _) (ne.symm h),
      rw ← le_div_iff this,
      apply op_norm_le_bound _ (div_nonneg (norm_nonneg _) this) (λx, _),
      rw [div_mul_eq_mul_div, le_div_iff this],
      calc ∥c x∥ * ∥f∥ = ∥c x • f∥ : (norm_smul _ _).symm
      ... = ∥((smul_right c f) : E → F) x∥ : rfl
      ... ≤ ∥smul_right c f∥ * ∥x∥ : le_op_norm _ _ } },
end

section restrict_scalars

variable (𝕜)
variables {𝕜' : Type*} [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
{E' : Type*} [normed_group E'] [normed_space 𝕜' E']
{F' : Type*} [normed_group F'] [normed_space 𝕜' F']

local attribute [instance, priority 500] normed_space.restrict_scalars

/-- `𝕜`-linear continuous function induced by a `𝕜'`-linear continuous function when `𝕜'` is a
normed algebra over `𝕜`. -/
def restrict_scalars (f : E' →L[𝕜'] F') : E' →L[𝕜] F' :=
{ cont := f.cont,
  ..linear_map.restrict_scalars 𝕜 (f.to_linear_map) }

@[simp, move_cast] lemma restrict_scalars_coe_eq_coe (f : E' →L[𝕜'] F') :
  (f.restrict_scalars 𝕜 : E' →ₗ[𝕜] F') = (f : E' →ₗ[𝕜'] F').restrict_scalars 𝕜 := rfl

@[simp, squash_cast] lemma restrict_scalars_coe_eq_coe' (f : E' →L[𝕜'] F') :
  (f.restrict_scalars 𝕜 : E' → F') = f := rfl

end restrict_scalars

end continuous_linear_map

/-- If both directions in a linear equiv `e` are continuous, then `e` is a uniform embedding. -/
lemma linear_equiv.uniform_embedding (e : E ≃ₗ[𝕜] F) (h₁ : continuous e) (h₂ : continuous e.symm) :
  uniform_embedding e :=
begin
  rcases linear_map.bound_of_continuous e.symm.to_linear_map h₂ with ⟨C, Cpos, hC⟩,
  let f : E →L[𝕜] F := { cont := h₁, ..e },
  apply f.uniform_embedding_of_bound C (λx, _),
  have : e.symm (e x) = x := linear_equiv.symm_apply_apply _ _,
  conv_lhs { rw ← this },
  exact hC _
end

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
lemma linear_map.mk_continuous_norm_le (f : E →ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ C :=
continuous_linear_map.op_norm_le_bound _ hC h

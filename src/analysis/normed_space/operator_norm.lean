/-
Copyright (c) 2019 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo
-/
import linear_algebra.finite_dimensional
import analysis.normed_space.riesz_lemma
import analysis.asymptotics

/-!
# Operator norm on the space of continuous linear maps

Define the operator norm on the space of continuous linear maps between normed spaces, and prove
its basic properties. In particular, show that this space is itself a normed space.
-/

noncomputable theory
open_locale classical


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
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

theorem linear_map.antilipschitz_of_bound {K : nnreal} (h : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  antilipschitz_with K f :=
antilipschitz_with.of_le_mul_dist $
λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

lemma linear_map.uniform_continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  uniform_continuous f :=
(f.lipschitz_of_bound C h).uniform_continuous

lemma linear_map.continuous_of_bound (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).continuous

/-- Construct a continuous linear map from a linear map and a bound on this linear map.
The fact that the norm of the continuous linear map is then controlled is given in
`linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, linear_map.continuous_of_bound f C h⟩

/-- Reinterpret a linear map `𝕜 →ₗ[𝕜] E` as a continuous linear map. This construction
is generalized to the case of any finite dimensional domain
in `linear_map.to_continuous_linear_map`. -/
def linear_map.to_continuous_linear_map₁ (f : 𝕜 →ₗ[𝕜] E) : 𝕜 →L[𝕜] E :=
f.mk_continuous (∥f 1∥) $ λ x, le_of_eq $
by { conv_lhs { rw ← mul_one x }, rw [← smul_eq_mul, f.map_smul, norm_smul, mul_comm] }

/-- Construct a continuous linear map from a linear map and the existence of a bound on this linear
map. If you have an explicit bound, use `linear_map.mk_continuous` instead, as a norm estimate will
follow automatically in `linear_map.mk_continuous_norm_le`. -/
def linear_map.mk_continuous_of_exists_bound (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) : E →L[𝕜] F :=
⟨f, let ⟨C, hC⟩ := h in linear_map.continuous_of_bound f C hC⟩

@[simp, norm_cast] lemma linear_map.mk_continuous_coe (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous C h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_apply (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous C h x = f x := rfl

@[simp, norm_cast] lemma linear_map.mk_continuous_of_exists_bound_coe (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ((f.mk_continuous_of_exists_bound h) : E →ₗ[𝕜] F) = f := rfl

@[simp] lemma linear_map.mk_continuous_of_exists_bound_apply (h : ∃C, ∀x, ∥f x∥ ≤ C * ∥x∥) (x : E) :
  f.mk_continuous_of_exists_bound h x = f x := rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_coe (f : 𝕜 →ₗ[𝕜] E) :
  (f.to_continuous_linear_map₁ : 𝕜 →ₗ[𝕜] E) = f :=
rfl

@[simp] lemma linear_map.to_continuous_linear_map₁_apply (f : 𝕜 →ₗ[𝕜] E) (x) :
  f.to_continuous_linear_map₁ x = f x :=
rfl

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
      have : x₀ ∈ f.ker, by { rw h, exact (linear_map.ker f).zero_mem },
      exact x₀ker this },
    have rx₀_ne_zero : r * ∥x₀∥ ≠ 0, by { simp [norm_eq_zero, this], norm_num },
    have : ∀x, ∥f x∥ ≤ (((r * ∥x₀∥)⁻¹) * ∥f x₀∥) * ∥x∥,
    { assume x,
      by_cases hx : f x = 0,
      { rw [hx, norm_zero],
        apply_rules [mul_nonneg, norm_nonneg, inv_nonneg.2] },
      { let y := x₀ - (f x₀ * (f x)⁻¹ ) • x,
        have fy_zero : f y = 0, by calc
          f y = f x₀ - (f x₀ * (f x)⁻¹ ) * f x : by simp [y]
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
            exact inv_nonneg.2 (mul_nonneg (by norm_num) (norm_nonneg _))
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
  refine ⟨δ⁻¹ * ∥c∥, mul_pos (inv_pos.2 δ_pos) (lt_trans zero_lt_one hc), (λx, _)⟩,
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

theorem is_O_comp {α : Type*} (g : F →L[𝕜] G) (f : α → F) (l : filter α) :
  is_O (λ x', g (f x')) f l :=
(g.is_O_id ⊤).comp_tendsto le_top

theorem is_O_sub (f : E →L[𝕜] F) (l : filter E) (x : E) :
  is_O (λ x', f (x' - x)) (λ x', x' - x) l :=
f.is_O_comp _ l

/-- A linear map which is a homothety is a continuous linear map.
    Since the field `𝕜` need not have `ℝ` as a subfield, this theorem is not directly deducible from
    the corresponding theorem about isometries plus a theorem about scalar multiplication.  Likewise
    for the other theorems about homotheties in this file.
 -/
def of_homothety (f : E →ₗ[𝕜] F) (a : ℝ) (hf : ∀x, ∥f x∥ = a * ∥x∥) : E →L[𝕜] F :=
f.mk_continuous a (λ x, le_of_eq (hf x))

variable (𝕜)

lemma to_span_singleton_homothety (x : E) (c : 𝕜) : ∥linear_map.to_span_singleton 𝕜 E x c∥ = ∥x∥ * ∥c∥ :=
by {rw mul_comm, exact norm_smul _ _}

/-- Given an element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from `E` to the span of `x`.-/
def to_span_singleton (x : E) : 𝕜 →L[𝕜] E :=
of_homothety (linear_map.to_span_singleton 𝕜 E x) ∥x∥ (to_span_singleton_homothety 𝕜 x)

end

section op_norm
open set real


/-- The operator norm of a continuous linear map is the inf of all its bounds. -/
def op_norm := Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥}
instance has_op_norm : has_norm (E →L[𝕜] F) := ⟨op_norm⟩

lemma norm_def : ∥f∥ = Inf {c | 0 ≤ c ∧ ∀ x, ∥f x∥ ≤ c * ∥x∥} := rfl

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
  (λ hne, have hlt : 0 < ∥x∥, from norm_pos_iff.2 hne,
    le_mul_of_div_le hlt ((le_Inf _ bounds_nonempty bounds_bdd_below).2
    (λ c ⟨_, hc⟩, div_le_of_le_mul hlt (by { rw mul_comm, apply hc }))))

theorem le_op_norm_of_le {c : ℝ} {x} (h : ∥x∥ ≤ c) : ∥f x∥ ≤ ∥f∥ * c :=
le_trans (f.le_op_norm x) (mul_le_mul_of_nonneg_left h f.op_norm_nonneg)

/-- continuous linear maps are Lipschitz continuous. -/
theorem lipschitz : lipschitz_with ⟨∥f∥, op_norm_nonneg f⟩ f :=
lipschitz_with.of_dist_le_mul $ λ x y,
  by { rw [dist_eq_norm, dist_eq_norm, ←map_sub], apply le_op_norm }

lemma ratio_le_op_norm : ∥f x∥ / ∥x∥ ≤ ∥f∥ :=
(or.elim (lt_or_eq_of_le (norm_nonneg _))
  (λ hlt, div_le_of_le_mul hlt (by { rw mul_comm, apply le_op_norm }))
  (λ heq, by { rw [←heq, div_zero], apply op_norm_nonneg }))

/-- The image of the unit ball under a continuous linear map is bounded. -/
lemma unit_le_op_norm : ∥x∥ ≤ 1 → ∥f x∥ ≤ ∥f∥ :=
mul_one ∥f∥ ▸ f.le_op_norm_of_le

/-- If one controls the norm of every `A x`, then one controls the norm of `A`. -/
lemma op_norm_le_bound {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
Inf_le _ bounds_bdd_below ⟨hMp, hM⟩

theorem op_norm_le_of_lipschitz {f : E →L[𝕜] F} {K : nnreal} (hf : lipschitz_with K f) :
  ∥f∥ ≤ K :=
f.op_norm_le_bound K.2 $ λ x, by simpa only [dist_zero_right, f.map_zero] using hf.dist_le_mul x 0

/-- The operator norm satisfies the triangle inequality. -/
theorem op_norm_add_le : ∥f + g∥ ≤ ∥f∥ + ∥g∥ :=
show ∥f + g∥ ≤ (coe : nnreal → ℝ) (⟨_, f.op_norm_nonneg⟩ + ⟨_, g.op_norm_nonneg⟩),
from op_norm_le_of_lipschitz (f.lipschitz.add g.lipschitz)

/-- An operator is zero iff its norm vanishes. -/
theorem op_norm_zero_iff : ∥f∥ = 0 ↔ f = 0 :=
iff.intro
  (λ hn, continuous_linear_map.ext (λ x, norm_le_zero_iff.1
    (calc _ ≤ ∥f∥ * ∥x∥ : le_op_norm _ _
     ...     = _ : by rw [hn, zero_mul])))
  (λ hf, le_antisymm (Inf_le _ bounds_bdd_below
    ⟨ge_of_eq rfl, λ _, le_of_eq (by { rw [zero_mul, hf], exact norm_zero })⟩)
    (op_norm_nonneg _))

@[simp] lemma norm_zero : ∥(0 : E →L[𝕜] F)∥ = 0 :=
by rw op_norm_zero_iff

/-- The norm of the identity is at most `1`. It is in fact `1`, except when the space is trivial
where it is `0`. It means that one can not do better than an inequality in general. -/
lemma norm_id_le : ∥id 𝕜 E∥ ≤ 1 :=
op_norm_le_bound _ zero_le_one (λx, by simp)

/-- If a space is non-trivial, then the norm of the identity equals `1`. -/
lemma norm_id [nontrivial E] : ∥id 𝕜 E∥ = 1 :=
le_antisymm norm_id_le $ let ⟨x, hx⟩ := exists_ne (0 : E) in
have _ := (id 𝕜 E).ratio_le_op_norm x,
by rwa [id_apply, div_self (ne_of_gt $ norm_pos_iff.2 hx)] at this

@[simp] lemma norm_id_field : ∥id 𝕜 𝕜∥ = 1 :=
norm_id

@[simp] lemma norm_id_field' : ∥(1 : 𝕜 →L[𝕜] 𝕜)∥ = 1 :=
norm_id_field

lemma op_norm_smul_le : ∥c • f∥ ≤ ∥c∥ * ∥f∥ :=
((c • f).op_norm_le_bound
  (mul_nonneg (norm_nonneg _) (op_norm_nonneg _)) (λ _,
  begin
    erw [norm_smul, mul_assoc],
    exact mul_le_mul_of_nonneg_left (le_op_norm _ _) (norm_nonneg _)
  end))

lemma op_norm_neg : ∥-f∥ = ∥f∥ := by { rw norm_def, apply congr_arg, ext, simp }

/-- Continuous linear maps themselves form a normed space with respect to
    the operator norm. -/
instance to_normed_group : normed_group (E →L[𝕜] F) :=
normed_group.of_core _ ⟨op_norm_zero_iff, op_norm_add_le, op_norm_neg⟩

instance to_normed_space : normed_space 𝕜 (E →L[𝕜] F) :=
⟨op_norm_smul_le⟩

/-- The operator norm is submultiplicative. -/
lemma op_norm_comp_le (f : E →L[𝕜] F) : ∥h.comp f∥ ≤ ∥h∥ * ∥f∥ :=
(Inf_le _ bounds_bdd_below
  ⟨mul_nonneg (op_norm_nonneg _) (op_norm_nonneg _), λ x,
    by { rw mul_assoc, exact h.le_op_norm_of_le (f.le_op_norm x) } ⟩)

/-- Continuous linear maps form a normed ring with respect to the operator norm. -/
instance to_normed_ring : normed_ring (E →L[𝕜] E) :=
{ norm_mul := op_norm_comp_le,
  .. continuous_linear_map.to_normed_group }

/-- For a nonzero normed space `E`, continuous linear endomorphisms form a normed algebra with
respect to the operator norm. -/
instance to_normed_algebra [nontrivial E] : normed_algebra 𝕜 (E →L[𝕜] E) :=
{ norm_algebra_map_eq := λ c, show ∥c • id 𝕜 E∥ = ∥c∥,
    by {rw [norm_smul, norm_id], simp},
  .. continuous_linear_map.algebra }

/-- A continuous linear map is automatically uniformly continuous. -/
protected theorem uniform_continuous : uniform_continuous f :=
f.lipschitz.uniform_continuous

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

lemma homothety_norm (hE : 0 < vector_space.dim 𝕜 E) (f : E →L[𝕜] F) {a : ℝ} (ha : 0 ≤ a) (hf : ∀x, ∥f x∥ = a * ∥x∥) :
  ∥f∥ = a :=
begin
  refine le_antisymm_iff.mpr ⟨_, _⟩,
  { exact continuous_linear_map.op_norm_le_bound f ha (λ y, le_of_eq (hf y)) },
  { rw continuous_linear_map.norm_def,
    apply real.lb_le_Inf _ continuous_linear_map.bounds_nonempty,
    cases dim_pos_iff_exists_ne_zero.mp hE with x hx,
    intros c h, rw mem_set_of_eq at h,
    apply (mul_le_mul_right (norm_pos_iff.mpr hx)).mp,
    rw ← hf x, exact h.2 x }
end

lemma to_span_singleton_norm (x : E) : ∥to_span_singleton 𝕜 x∥ = ∥x∥ :=
begin
  refine homothety_norm _ _ (norm_nonneg x) (to_span_singleton_homothety 𝕜 x),
  rw dim_of_field, exact cardinal.zero_lt_one,
end

variable (f)

theorem uniform_embedding_of_bound {K : nnreal} (hf : ∀ x, ∥x∥ ≤ K * ∥f x∥) :
  uniform_embedding f :=
(f.to_linear_map.antilipschitz_of_bound hf).uniform_embedding f.uniform_continuous

/-- If a continuous linear map is a uniform embedding, then it is expands the distances
by a positive factor.-/
theorem antilipschitz_of_uniform_embedding (hf : uniform_embedding f) :
  ∃ K, antilipschitz_with K f :=
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
  refine ⟨⟨δ⁻¹, _⟩ * nnnorm c, f.to_linear_map.antilipschitz_of_bound $ λx, _⟩,
  exact inv_nonneg.2 (le_of_lt δ_pos),
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

section completeness

open_locale topological_space
open filter

/-- If the target space is complete, the space of continuous linear maps with its norm is also
complete. -/
instance [complete_space F] : complete_space (E →L[𝕜] F) :=
begin
  -- We show that every Cauchy sequence converges.
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf, _),
  -- We now expand out the definition of a Cauchy sequence,
  rcases cauchy_seq_iff_le_tendsto_0.1 hf with ⟨b, b0, b_bound, b_lim⟩, clear hf,
  -- and establish that the evaluation at any point `v : E` is Cauchy.
  have cau : ∀ v, cauchy_seq (λ n, f n v),
  { assume v,
    apply cauchy_seq_iff_le_tendsto_0.2 ⟨λ n, b n * ∥v∥, λ n, _, _, _⟩,
    { exact mul_nonneg (b0 n) (norm_nonneg _) },
    { assume n m N hn hm,
      rw dist_eq_norm,
      apply le_trans ((f n - f m).le_op_norm v) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m N hn hm) (norm_nonneg v) },
    { simpa using b_lim.mul tendsto_const_nhds } },
  -- We assemble the limits points of those Cauchy sequences
  -- (which exist as `F` is complete)
  -- into a function which we call `G`.
  choose G hG using λv, cauchy_seq_tendsto_of_complete (cau v),
  -- Next, we show that this `G` is linear,
  let Glin : E →ₗ[𝕜] F :=
  { to_fun := G,
    map_add' := λ v w, begin
      have A := hG (v + w),
      have B := (hG v).add (hG w),
      simp only [map_add] at A B,
      exact tendsto_nhds_unique A B,
    end,
    map_smul' := λ c v, begin
      have A := hG (c • v),
      have B := filter.tendsto.smul (@tendsto_const_nhds _ ℕ _ c _) (hG v),
      simp only [map_smul] at A B,
      exact tendsto_nhds_unique A B
    end },
  -- and that `G` has norm at most `(b 0 + ∥f 0∥)`.
  have Gnorm : ∀ v, ∥G v∥ ≤ (b 0 + ∥f 0∥) * ∥v∥,
  { assume v,
    have A : ∀ n, ∥f n v∥ ≤ (b 0 + ∥f 0∥) * ∥v∥,
    { assume n,
      apply le_trans ((f n).le_op_norm _) _,
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v),
      calc ∥f n∥ = ∥(f n - f 0) + f 0∥ : by { congr' 1, abel }
      ... ≤ ∥f n - f 0∥ + ∥f 0∥ : norm_add_le _ _
      ... ≤ b 0 + ∥f 0∥ : begin
        apply add_le_add_right,
        simpa [dist_eq_norm] using b_bound n 0 0 (zero_le _) (zero_le _)
      end },
    exact le_of_tendsto (hG v).norm (eventually_of_forall A) },
  -- Thus `G` is continuous, and we propose that as the limit point of our original Cauchy sequence.
  let Gcont := Glin.mk_continuous _ Gnorm,
  use Gcont,
  -- Our last task is to establish convergence to `G` in norm.
  have : ∀ n, ∥f n - Gcont∥ ≤ b n,
  { assume n,
    apply op_norm_le_bound _ (b0 n) (λ v, _),
    have A : ∀ᶠ m in at_top, ∥(f n - f m) v∥ ≤ b n * ∥v∥,
    { refine eventually_at_top.2 ⟨n, λ m hm, _⟩,
      apply le_trans ((f n - f m).le_op_norm _) _,
      exact mul_le_mul_of_nonneg_right (b_bound n m n (le_refl _) hm) (norm_nonneg v) },
    have B : tendsto (λ m, ∥(f n - f m) v∥) at_top (𝓝 (∥(f n - Gcont) v∥)) :=
      tendsto.norm (tendsto_const_nhds.sub (hG v)),
    exact le_of_tendsto B A },
  erw tendsto_iff_norm_tendsto_zero,
  exact squeeze_zero (λ n, norm_nonneg _) this b_lim,
end

end completeness

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
  map_add' :=
  begin
    refine h_dense.induction_on₂ _ _,
    { exact is_closed_eq (cont.comp continuous_add)
        ((cont.comp continuous_fst).add (cont.comp continuous_snd)) },
    { assume x y, simp only [eq, ← e.map_add], exact f.map_add _ _  },
  end,
  map_smul' := λk,
  begin
    refine (λ b, h_dense.induction_on b _ _),
    { exact is_closed_eq (cont.comp (continuous_const.smul continuous_id))
        ((continuous_const.smul continuous_id).comp cont) },
    { assume x, rw ← map_smul, simp only [eq], exact map_smul _ _ _  },
  end,
  cont := cont
}

lemma extend_unique (g : G →L[𝕜] F) (H : g.comp e = f) : extend f e h_dense h_e = g :=
continuous_linear_map.coe_injective' $
  uniformly_extend_unique h_e h_dense (continuous_linear_map.ext_iff.1 H) g.continuous

@[simp] lemma extend_zero : extend (0 : E →L[𝕜] F) e h_dense h_e = 0 :=
extend_unique _ _ _ _ _ (zero_comp _)

end

section
variables {N : nnreal} (h_e : ∀x, ∥x∥ ≤ N * ∥e x∥)

local notation `ψ` := f.extend e h_dense (uniform_embedding_of_bound _ h_e).to_uniform_inducing

/-- If a dense embedding `e : E →L[𝕜] G` expands the norm by a constant factor `N⁻¹`, then the norm
    of the extension of `f` along `e` is bounded by `N * ∥f∥`. -/
lemma op_norm_extend_le : ∥ψ∥ ≤ N * ∥f∥ :=
begin
  have uni : uniform_inducing e := (uniform_embedding_of_bound _ h_e).to_uniform_inducing,
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
        ... ≤ N * ∥f∥ * ∥e x∥ : by rw [mul_comm ↑N ∥f∥, mul_assoc] } },
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

/-- Left-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_left (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_ring 𝕜']
  [h : normed_algebra 𝕜 𝕜'] : 𝕜' → (𝕜' →L[𝕜] 𝕜') :=
λ x, (algebra.lmul_left 𝕜 𝕜' x).mk_continuous ∥x∥
(λ y, by {rw algebra.lmul_left_apply, exact norm_mul_le x y})

@[simp] lemma lmul_left_apply {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] (x y : 𝕜') :
  lmul_left 𝕜 𝕜' x y = x * y := rfl

/-- Right-multiplication in a normed algebra, considered as a continuous linear map. -/
def lmul_right (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] : 𝕜' → (𝕜' →L[𝕜] 𝕜') :=
λ x, (algebra.lmul_right 𝕜 𝕜' x).mk_continuous ∥x∥
(λ y, by {rw [algebra.lmul_right_apply, mul_comm], exact norm_mul_le y x})

@[simp] lemma lmul_right_apply {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] (x y : 𝕜') :
  lmul_right 𝕜 𝕜' x y = y * x := rfl

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

@[simp, norm_cast] lemma restrict_scalars_coe_eq_coe (f : E' →L[𝕜'] F') :
  (f.restrict_scalars 𝕜 : E' →ₗ[𝕜] F') = (f : E' →ₗ[𝕜'] F').restrict_scalars 𝕜 := rfl

@[simp, norm_cast squash] lemma restrict_scalars_coe_eq_coe' (f : E' →L[𝕜'] F') :
  (f.restrict_scalars 𝕜 : E' → F') = f := rfl

end restrict_scalars

end continuous_linear_map

variables {ι : Type*}

/-- Applying a continuous linear map commutes with taking an (infinite) sum. -/
lemma continuous_linear_map.has_sum {f : ι → E} (φ : E →L[𝕜] F) {x : E} (hf : has_sum f x) :
  has_sum (λ (b:ι), φ (f b)) (φ x) :=
begin
  unfold has_sum,
  convert φ.continuous.continuous_at.tendsto.comp hf,
  ext s, rw [function.comp_app, finset.sum_hom s φ],
end

lemma continuous_linear_map.has_sum_of_summable {f : ι → E} (φ : E →L[𝕜] F) (hf : summable f) :
  has_sum (λ (b:ι), φ (f b)) (φ (∑'b, f b)) :=
continuous_linear_map.has_sum φ hf.has_sum

namespace continuous_linear_equiv

variable (e : E ≃L[𝕜] F)

protected lemma lipschitz : lipschitz_with (nnnorm (e : E →L[𝕜] F)) e :=
(e : E →L[𝕜] F).lipschitz

protected lemma antilipschitz : antilipschitz_with (nnnorm (e.symm : F →L[𝕜] E)) e :=
e.symm.lipschitz.to_right_inverse e.left_inv

theorem is_O_comp {α : Type*} (f : α → E) (l : filter α) :
  asymptotics.is_O (λ x', e (f x')) f l :=
(e : E →L[𝕜] F).is_O_comp f l

theorem is_O_sub (l : filter E) (x : E) :
  asymptotics.is_O (λ x', e (x' - x)) (λ x', x' - x) l :=
(e : E →L[𝕜] F).is_O_sub l x

theorem is_O_comp_rev {α : Type*} (f : α → E) (l : filter α) :
  asymptotics.is_O f (λ x', e (f x')) l :=
(e.symm.is_O_comp _ l).congr_left $ λ _, e.symm_apply_apply _

theorem is_O_sub_rev (l : filter E) (x : E) :
  asymptotics.is_O (λ x', x' - x) (λ x', e (x' - x)) l :=
e.is_O_comp_rev _ _

/-- A continuous linear equiv is a uniform embedding. -/
lemma uniform_embedding : uniform_embedding e :=
e.antilipschitz.uniform_embedding e.lipschitz.uniform_continuous

lemma one_le_norm_mul_norm_symm [nontrivial E] :
  1 ≤ ∥(e : E →L[𝕜] F)∥ * ∥(e.symm : F →L[𝕜] E)∥ :=
begin
  rw [mul_comm],
  convert (e.symm : F →L[𝕜] E).op_norm_comp_le (e : E →L[𝕜] F),
  rw [e.coe_symm_comp_coe, continuous_linear_map.norm_id]
end

lemma norm_pos [nontrivial E] : 0 < ∥(e : E →L[𝕜] F)∥ :=
pos_of_mul_pos_right (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

lemma norm_symm_pos [nontrivial E] : 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
pos_of_mul_pos_left (lt_of_lt_of_le zero_lt_one e.one_le_norm_mul_norm_symm) (norm_nonneg _)

lemma subsingleton_or_norm_symm_pos : subsingleton E ∨ 0 < ∥(e.symm : F →L[𝕜] E)∥ :=
begin
  rcases subsingleton_or_nontrivial E with _i|_i; resetI,
  { left, apply_instance },
  { right, exact e.norm_symm_pos }
end

lemma subsingleton_or_nnnorm_symm_pos : subsingleton E ∨ 0 < (nnnorm $ (e.symm : F →L[𝕜] E)) :=
subsingleton_or_norm_symm_pos e

lemma homothety_inverse (a : ℝ) (ha : 0 < a) (f : E ≃ₗ[𝕜] F) :
  (∀ (x : E), ∥f x∥ = a * ∥x∥) → (∀ (y : F), ∥f.symm y∥ = a⁻¹ * ∥y∥) :=
begin
  intros hf y,
  calc ∥(f.symm) y∥ = a⁻¹ * (a * ∥ (f.symm) y∥) : _
  ... =  a⁻¹ * ∥f ((f.symm) y)∥ : by rw hf
  ... = a⁻¹ * ∥y∥ : by simp,
  rw [← mul_assoc, inv_mul_cancel (ne_of_lt ha).symm, one_mul],
end

variable (𝕜)

/-- A linear equivalence which is a homothety is a continuous linear equivalence. -/
def of_homothety (f : E ≃ₗ[𝕜] F) (a : ℝ) (ha : 0 < a) (hf : ∀x, ∥f x∥ = a * ∥x∥) : E ≃L[𝕜] F :=
{ to_linear_equiv := f,
  continuous_to_fun := f.to_linear_map.continuous_of_bound a (λ x, le_of_eq (hf x)),
  continuous_inv_fun := f.symm.to_linear_map.continuous_of_bound a⁻¹
    (λ x, le_of_eq (homothety_inverse a ha f hf x)) }

lemma to_span_nonzero_singleton_homothety (x : E) (h : x ≠ 0) (c : 𝕜) :
  ∥linear_equiv.to_span_nonzero_singleton 𝕜 E x h c∥ = ∥x∥ * ∥c∥ :=
continuous_linear_map.to_span_singleton_homothety _ _ _

/-- Given a nonzero element `x` of a normed space `E` over a field `𝕜`, the natural
    continuous linear equivalence from `E` to the span of `x`.-/
def to_span_nonzero_singleton (x : E) (h : x ≠ 0) : 𝕜 ≃L[𝕜] (submodule.span 𝕜 ({x} : set E)) :=
of_homothety 𝕜
  (linear_equiv.to_span_nonzero_singleton 𝕜 E x h)
  ∥x∥
  (norm_pos_iff.mpr h)
  (to_span_nonzero_singleton_homothety 𝕜 x h)

/-- Given a nonzero element `x` of a normed space `E` over a field `𝕜`, the natural continuous
    linear map from the span of `x` to `𝕜`.-/
abbreviation coord (x : E) (h : x ≠ 0) : (submodule.span 𝕜 ({x} : set E)) →L[𝕜] 𝕜 :=
  (to_span_nonzero_singleton 𝕜 x h).symm

lemma coord_norm (x : E) (h : x ≠ 0) : ∥coord 𝕜 x h∥ = ∥x∥⁻¹ :=
begin
  have hx : 0 < ∥x∥ := (norm_pos_iff.mpr h),
  refine continuous_linear_map.homothety_norm _ _ (le_of_lt (inv_pos.mpr hx)) _,
  { rw ← finite_dimensional.findim_eq_dim,
    rw ← linear_equiv.findim_eq (linear_equiv.to_span_nonzero_singleton 𝕜 E x h),
    rw finite_dimensional.findim_of_field,
    have : 0 = ((0:nat) : cardinal) := rfl,
    rw this, apply cardinal.nat_cast_lt.mpr, norm_num },
  { intros y,
    have : (coord 𝕜 x h) y = (to_span_nonzero_singleton 𝕜 x h).symm y := rfl,
    rw this, apply homothety_inverse, exact hx, exact to_span_nonzero_singleton_homothety 𝕜 x h, }
end

variable (E)

/-- The continuous linear equivalences from `E` to itself form a group under composition. -/
instance automorphism_group : group (E ≃L[𝕜] E) :=
{ mul          := λ f g, g.trans f,
  one          := continuous_linear_equiv.refl 𝕜 E,
  inv          := λ f, f.symm,
  mul_assoc    := λ f g h, by {ext, refl},
  mul_one      := λ f, by {ext, refl},
  one_mul      := λ f, by {ext, refl},
  mul_left_inv := λ f, by {ext, exact f.left_inv x} }

variables {𝕜 E}

/-- An invertible continuous linear map `f` determines a continuous equivalence from `E` to itself.
-/
def of_unit (f : units (E →L[𝕜] E)) : (E ≃L[𝕜] E) :=
{ to_linear_equiv :=
  { to_fun    := f.val,
    map_add'  := by simp,
    map_smul' := by simp,
    inv_fun   := f.inv,
    left_inv  := λ x, show (f.inv * f.val) x = x, by {rw f.inv_val, simp},
    right_inv := λ x, show (f.val * f.inv) x = x, by {rw f.val_inv, simp}, },
  continuous_to_fun  := f.val.continuous,
  continuous_inv_fun := f.inv.continuous }

/-- A continuous equivalence from `E` to itself determines an invertible continuous linear map. -/
def to_unit (f : (E ≃L[𝕜] E)) : units (E →L[𝕜] E) :=
{ val     := f,
  inv     := f.symm,
  val_inv := by {ext, simp},
  inv_val := by {ext, simp} }

variables (𝕜 E)

/-- The units of the algebra of continuous `𝕜`-linear endomorphisms of `E` is multiplicatively
equivalent to the type of continuous linear equivalences between `E` and itself. -/
def units_equiv : units (E →L[𝕜] E) ≃* (E ≃L[𝕜] E) :=
{ to_fun    := of_unit,
  inv_fun   := to_unit,
  left_inv  := λ f, by {ext, refl},
  right_inv := λ f, by {ext, refl},
  map_mul'  := λ x y, by {ext, refl} }

@[simp] lemma units_equiv_to_continuous_linear_map
  (f : units (E →L[𝕜] E)) :
  (units_equiv 𝕜 E f : E →L[𝕜] E) = f := by {ext, refl}

end continuous_linear_equiv

lemma linear_equiv.uniform_embedding (e : E ≃ₗ[𝕜] F) (h₁ : continuous e) (h₂ : continuous e.symm) :
  uniform_embedding e :=
continuous_linear_equiv.uniform_embedding
{ continuous_to_fun := h₁,
  continuous_inv_fun := h₂,
  .. e }

/-- If a continuous linear map is constructed from a linear map via the constructor `mk_continuous`,
then its norm is bounded by the bound given to the constructor if it is nonnegative. -/
lemma linear_map.mk_continuous_norm_le (f : E →ₗ[𝕜] F) {C : ℝ} (hC : 0 ≤ C) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  ∥f.mk_continuous C h∥ ≤ C :=
continuous_linear_map.op_norm_le_bound _ hC h

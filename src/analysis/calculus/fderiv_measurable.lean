/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import analysis.calculus.fderiv measure_theory.borel_space

/-!
# Measurability of the derivative

Consider a function between `𝕜`-vector spaces, where the target space is complete. We prove that
the set of its differentiability points is Borel-measurable, in `is_measurable_differentiable`.

TODO: show that the derivative itself (defined to be `0` where the function is not differentiable)
is measurable.

## Implementation

We give a proof that avoids second-countability issues, by expressing the differentiability set
as a function of open sets in the following way. Define `A (L, r, ε)` to be the set of points
where, on a ball of radius roughly `r` around `x`, the function is uniformly approximated by the
linear map, up to `ε r`. It is an open set. Let also `B (L, r, s, ε) = A (L, r, ε) ∩ A (L, s, ε)`:
we require that at two possibly different scales `r` and `s`, the function is well approximated by
the linear map.

We claim that the differentiability set of `f` is exactly
`⋂ ε > 0, ⋃ δ > 0, ⋂ r, s < δ, ⋃ L, B (L, r, s, ε)`.
In other words, for any `ε > 0`, there is a size such that, for any two scales below this size, the
function is well approximated by a linear map, common to the two scales.

The set `⋃ L, B (L, r, s, ε)` is open, as a union of open sets. Converting the intersections and
unions to countable ones (using real numbers of the form `2 ^ (-n)`), it follows that the
differentiability set is measurable.

To prove the claim, there are two inclusions. One is trivial: if the function is differentiable
at `x`, then `x` belongs to the above set (just take `L` to be the derivative, and use that the
differentiability exactly says that the map is well approximated by `L`). This is proved in
`mem_A_of_differentiable` and `differentiable_subset_B`.

For the other direction, the difficulty is that `L` in the union may depend on `ε, r, s`. The key
point is that, in fact, it doesn't depend too much on them. First, if `x` belongs both to
`A (L, r, ε)` and `A (L', r, ε)`, then `L` and `L'` have to be close on a shell, and thus
`∥L - L'∥` is bounded by `ε` (see `norm_sub_le_of_mem_A`). If one has two maps `L` and `L'` such
that `x` belongs to `A (L, r, ε)` and to `A (L', r', ε')`, one deduces that `L` is close
to `L'` by arguing as follows. Consider another scale `s` smaller than `r` and `r'`. Take a linear
map `L₁` that approximates `f` around `x` both at scales `r` and `s` w.r.t. `ε` (it exists as
`x` belongs to our set). Take also `L₂` that approximates `f` around `x` both at scales `r'` and `s`
w.r.t. `ε'`. Then `L₁` is close to `L` (as they are close on a shell of radius `r`), and `L₂` is
close to `L₁` (as they are close on a shell of radius `s`), and `L'` is close to `L₂` (as they are
close on a shell of radius `r'`). It follows that `L` is close to `L'`, as we claimed.

It follows that the different approximating linear maps that show up form a Cauchy sequence when
`ε` tends to `0`. When the target space is complete, this sequence converges, to a limit `f'`.
With the same kind of arguments, one checks that `f` is differentiable with derivative `f'`.
-/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variable (f : E → F)

open set metric asymptotics filter continuous_linear_map
open_locale topological_space

namespace fderiv_measurable_aux

/-- The set `A f L r ε` is the set of points `x` around which the function `f` is well approximated
at scale `r` by the linear map `L`, up to an error `ε`. We tweak the definition to make sure that
this is an open set.-/
def A (L : E →L[𝕜] F) (r ε : ℝ) : set E :=
{x | ∃ r' ∈ Ioc (r/2) r, ∀ y z ∈ ball x r', ∥f z - f y - L (z-y)∥ ≤ ε * r}

lemma A_mono (L : E →L[𝕜] F) (r : ℝ) {ε δ : ℝ} (h : ε ≤ δ) :
  A f L r ε ⊆ A f L r δ :=
begin
  rintros x ⟨r', r'r, hr'⟩,
  refine ⟨r', r'r, λ y z hy hz, _⟩,
  apply le_trans (hr' y z hy hz),
  apply mul_le_mul_of_nonneg_right h,
  linarith [mem_ball.1 hy, r'r.2, @dist_nonneg _ _ y x],
end

variable {f}
lemma le_of_mem_A {r ε : ℝ} {L : E →L[𝕜] F} {x : E} (hx : x ∈ A f L r ε)
  {y z : E} (hy : y ∈ closed_ball x (r/2)) (hz : z ∈ closed_ball x (r/2)) :
  ∥f z - f y - L (z-y)∥ ≤ ε * r :=
begin
  rcases hx with ⟨r', r'mem, hr'⟩,
  exact hr' _ _ (lt_of_le_of_lt (mem_closed_ball.1 hy) r'mem.1)
    (lt_of_le_of_lt (mem_closed_ball.1 hz) r'mem.1)
end
variable (f)

lemma is_open_A (L : E →L[𝕜] F) (r ε : ℝ) : is_open (A f L r ε) :=
begin
  rw metric.is_open_iff,
  rintros x ⟨r', r'_mem, hr'⟩,
  obtain ⟨s, s_gt, s_lt⟩ : ∃ (s : ℝ), r / 2 < s ∧ s < r' := exists_between r'_mem.1,
  have : s ∈ Ioc (r/2) r := ⟨s_gt, le_of_lt (s_lt.trans_le r'_mem.2)⟩,
  refine ⟨r' - s, by linarith, λ x' hx', ⟨s, this, _⟩⟩,
  have B : ball x' s ⊆ ball x r' := ball_subset (le_of_lt hx'),
  assume y z hy hz,
  exact hr' y z (B hy) (B hz)
end

variable {f}

lemma mem_A_of_differentiable {ε : ℝ} (hε : 0 < ε) {x : E} (hx : differentiable_at 𝕜 f x) :
  ∃ R > 0, ∀ r ∈ Ioo (0 : ℝ) R, x ∈ A f (fderiv 𝕜 f x) r ε :=
begin
  have := hx.has_fderiv_at,
  simp only [has_fderiv_at, has_fderiv_at_filter, is_o_iff] at this,
  rcases eventually_nhds_iff_ball.1 (this (half_pos hε)) with ⟨R, R_pos, hR⟩,
  refine ⟨R, R_pos, λ r hr, _⟩,
  have : r ∈ Ioc (r/2) r := ⟨half_lt_self hr.1, le_refl _⟩,
  refine ⟨r, this, λ y z hy hz, _⟩,
  calc  ∥f z - f y - (fderiv 𝕜 f x) (z - y)∥
      = ∥(f z - f x - (fderiv 𝕜 f x) (z - x)) - (f y - f x - (fderiv 𝕜 f x) (y - x))∥ :
    by { congr' 1, simp only [continuous_linear_map.map_sub], abel }
  ... ≤ ∥(f z - f x - (fderiv 𝕜 f x) (z - x))∥ + ∥f y - f x - (fderiv 𝕜 f x) (y - x)∥ :
    norm_sub_le _ _
  ... ≤ ε / 2 * ∥z - x∥ + ε / 2 * ∥y - x∥ :
    add_le_add (hR _ (lt_trans (mem_ball.1 hz) hr.2)) (hR _ (lt_trans (mem_ball.1 hy) hr.2))
  ... ≤ ε / 2 * r + ε / 2 * r :
    add_le_add
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hz)) (le_of_lt (half_pos hε)))
      (mul_le_mul_of_nonneg_left (le_of_lt (mem_ball_iff_norm.1 hy)) (le_of_lt (half_pos hε)))
  ... = ε * r : by ring
end

lemma norm_sub_le_of_mem_A {c : 𝕜} (hc : 1 < ∥c∥)
  {r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) {x : E} {L₁ L₂ : E →L[𝕜] F}
  (h₁ : x ∈ A f L₁ r ε) (h₂ : x ∈ A f L₂ r ε) : ∥L₁ - L₂∥ ≤ 4 * ∥c∥ * ε :=
begin
  apply continuous_linear_map.op_norm_le_bound _
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (norm_nonneg _)) (le_of_lt hε)),
  assume y,
  by_cases hy : y = 0, { simp [hy] },
  rcases rescale_to_shell hc (half_pos hr) hy with ⟨d, d_pos, dy_le, le_dy, dinv⟩,
  have M : ∥(L₁ - L₂) (d • y)∥ ≤ 2 * ε * r := calc
    ∥(L₁ - L₂) (d • y)∥
        = ∥(f (x + d • y) - f x - L₂ ((x + d • y) - x))
            - (f (x + d • y) - f x - L₁ ((x + d • y) - x))∥ : by simp
    ... ≤ ∥(f (x + d • y) - f x - L₂ ((x + d • y) - x))∥
          + ∥(f (x + d • y) - f x - L₁ ((x + d • y) - x))∥ : norm_sub_le _ _
    ... ≤ ε * r + ε * r :
      begin
        apply add_le_add,
        { apply le_of_mem_A h₂,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, dy_le] } },
        { apply le_of_mem_A h₁,
          { simp only [le_of_lt (half_pos hr), mem_closed_ball, dist_self] },
          { simp only [dist_eq_norm, add_sub_cancel', mem_closed_ball, dy_le] } },
      end
    ... = 2 * ε * r : by ring,
  calc ∥(L₁ - L₂) y∥
      = ∥(L₁ - L₂) (d⁻¹ • (d • y))∥ : by rw [smul_smul, inv_mul_cancel d_pos, one_smul]
  ... = ∥d∥⁻¹ * ∥(L₁ - L₂) (d • y)∥ :
    by simp [-continuous_linear_map.coe_sub', norm_smul]
  ... ≤ ((r / 2)⁻¹ * ∥c∥ * ∥y∥) * (2 * ε * r) :
    mul_le_mul dinv M (norm_nonneg _) (le_trans (inv_nonneg.2 (norm_nonneg _)) dinv)
  ... = 4 * ∥c∥ * ε * ∥y∥ :
    by { field_simp [ne_of_gt hr], ring }
end

variables (𝕜 f)


/-- The set `B 𝕜 f r s ε` is the set of points `x` around which there exists a continuous linear map
`L` that approximates well the function `f` (up to an error `ε`), simultaneously at scales
`r` and `s`. -/
def B (r s ε : ℝ) : set E := ⋃ (L : E →L[𝕜] F), (A f L r ε) ∩ (A f L s ε)

lemma is_open_B (r s ε : ℝ) : is_open (B 𝕜 f r s ε) :=
by simp [B, is_open_Union, is_open_inter, is_open_A]

/-- Easy inclusion: a differentiability point is included in an explicit set defined in terms
of `B` with countable operations. -/
lemma differentiable_subset_B :
  {x | differentiable_at 𝕜 f x} ⊆
    ⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B 𝕜 f ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e) :=
begin
  assume x hx,
  rw mem_Inter,
  assume e,
  have : (0 : ℝ) < (1/2) ^ e, by { apply pow_pos, norm_num },
  rcases mem_A_of_differentiable this hx with ⟨R, R_pos, hR⟩,
  obtain ⟨n, hn⟩ : ∃ (n : ℕ), (1/2) ^ n < R :=
    exists_nat_pow_lt R_pos (by norm_num : (1 : ℝ)/2 < 1),
  apply mem_Union.2 ⟨n, _⟩,
  simp only [mem_Inter],
  assume p hp q hq,
  apply mem_Union.2 ⟨fderiv 𝕜 f x, _⟩,
  split;
  { refine hR _ ⟨pow_pos (by norm_num) _, lt_of_le_of_lt _ hn⟩,
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by assumption) }
end

/-- Hard inclusion: if a point belongs to an explicit set defined in terms of `B` with countable
operations, then the function `f` is differentiable there. -/
lemma B_subset_differentiable [complete_space F]:
  (⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B 𝕜 f ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e))
    ⊆ {x | differentiable_at 𝕜 f x} :=
begin
  have P : ∀ {n : ℕ}, (0 : ℝ) < (1/2) ^ n := pow_pos (by norm_num),
  rcases normed_field.exists_one_lt_norm 𝕜 with ⟨c, hc⟩,
  have cpos : 0 < ∥c∥ := lt_trans zero_lt_one hc,
  assume x hx,
  have : ∀ (e : ℕ), ∃ (n : ℕ), ∀ p q, n ≤ p → n ≤ q → ∃ (L : E →L[𝕜] F),
    x ∈ A f L ((1/2) ^ p) ((1/2) ^ e) ∩ A f L ((1/2) ^ q) ((1/2) ^ e),
  { assume e,
    have := mem_Inter.1 hx e,
    rcases mem_Union.1 this with ⟨n, hn⟩,
    refine ⟨n, λ p q hp hq, _⟩,
    simp only [mem_Inter, ge_iff_le] at hn,
    exact mem_Union.1 (hn p hp q hq), },
  /- Recast the assumptions: for each `e`, there exist `n e` and linear maps `L e p q`
  such that, for `p, q ≥ n e`, then `f` is well approximated by `L e p q` at scale `2 ^ (-p)` and
  `2 ^ (-q)`, with an error `2 ^ (-e)`. -/
  choose! n L hn using this,
  /- We will show that all the `L e p q` are close to each other when `e` is large enough. For
  definiteness, use `L0 e = L e (n e) (n e)`, to have a single sequence. We claim that this is
  a Cauchy sequence. -/
  let L0 : ℕ → (E →L[𝕜] F) := λ e, L e (n e) (n e),
  have : cauchy_seq L0,
  { rw cauchy_seq_iff',
    assume ε εpos,
    obtain ⟨e, he⟩ : ∃ (e : ℕ), (1/2) ^ e < ε / (12 * ∥c∥):=
      exists_nat_pow_lt (div_pos εpos (mul_pos (by norm_num) cpos)) (by norm_num),
    use e,
    set δ : ℝ := (1/2) ^ e with hδ,
    assume e' he',
    rw [ge_iff_le] at he',
    set δ' : ℝ := (1/2) ^ e' with hδ',
    have δ'le : δ' ≤ δ := pow_le_pow_of_le_one (by norm_num) (by norm_num) he',
    let p := max (n e) (n e'),
    /- To show that `L0 e` and `L0 e'` are close, argue that `L0 e` is close to `L e (n e) p`
    (where `p` is large enough), as both approach `f` at scale `2 ^(- n e)`. And `L e (n e) p`
    is close to `L e' (n e') p` as both approach `f` at scale `2 ^ (-p)`. And `L e' (n e') p` is
    close to `L0 e'` as both approach `f` at scale `2 ^ (- n e')`. -/
    have J1 : ∥L0 e - L e (n e) p∥ ≤ 4 * ∥c∥ * δ,
    { have I1 : x ∈ A f (L0 e) ((1 / 2) ^ (n e)) δ :=
        (hn e (n e) (n e) (le_refl _) (le_refl _)).1,
      have I2 : x ∈ A f (L e (n e) p) ((1 / 2) ^ (n e)) δ :=
        (hn e (n e) p (le_refl _) (le_max_left _ _)).1,
      exact norm_sub_le_of_mem_A hc P P I1 I2 },
    have J2 : ∥L e' (n e') p - L0 e'∥ ≤ 4 * ∥c∥ * δ,
    { have I1 : x ∈ A f (L0 e') ((1 / 2) ^ (n e')) δ' :=
        (hn e' (n e') (n e') (le_refl _) (le_refl _)).1,
      have I2 : x ∈ A f (L e' (n e') p) ((1 / 2) ^ (n e')) δ' :=
        (hn e' (n e') p (le_refl _) (le_max_right _ _)).1,
      exact norm_sub_le_of_mem_A hc P P
        (A_mono _ _ _ δ'le I2) (A_mono _ _ _ δ'le I1) },
    have J3 : ∥L e (n e) p - L e' (n e') p∥ ≤ 4 * ∥c∥ * δ,
    { have I1 : x ∈ A f (L e (n e) p) ((1 / 2) ^ p) δ :=
        (hn e (n e) p (le_refl _) (le_max_left _ _)).2,
      have I2 : x ∈ A f (L e' (n e') p) ((1 / 2) ^ p) δ' :=
        (hn e' (n e') p (le_refl _) (le_max_right _ _)).2,
      exact norm_sub_le_of_mem_A hc P P I1 (A_mono _ _ _ δ'le I2) },
    rw [dist_comm, dist_eq_norm],
    calc
      ∥L0 e - L0 e'∥
          = ∥(L0 e - L e (n e) p) + (L e (n e) p - L e' (n e') p) + (L e' (n e') p - L0 e')∥ :
        by { congr' 1, abel }
      ... ≤ ∥L0 e - L e (n e) p∥ + ∥L e (n e) p - L e' (n e') p∥ + ∥L e' (n e') p - L0 e'∥ :
        le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
      ... ≤ 4 * ∥c∥ * δ + 4 * ∥c∥ * δ + 4 * ∥c∥ * δ :
        by apply_rules [add_le_add]
      ... = 12 * ∥c∥ * δ : by ring
      ... < 12 * ∥c∥ * (ε / (12 * ∥c∥)) :
        mul_lt_mul' (le_refl _) he (le_of_lt P) (mul_pos (by norm_num) cpos)
      ... = ε :
        by { field_simp [(by norm_num : (12 : ℝ) ≠ 0), ne_of_gt cpos], ring } },
  /- As it is Cauchy, the sequence `L0` converges, to a limit `f'`.-/
  obtain ⟨f', hf'⟩ : ∃ f' : E →L[𝕜] F, tendsto L0 at_top (𝓝 f') :=
    cauchy_seq_tendsto_of_complete this,
  /- We will show that `f` has derivative `f'` at `x`. -/
  have : has_fderiv_at f f' x,
  { simp only [has_fderiv_at_iff_is_o_nhds_zero, is_o_iff],
    /- to get an approximation with a precision `ε`, we will use `L0 e` for large enough (but fixed)
    `e`, and then argue that it works as an approximation at any scale `2 ^ (-k)` as it is close to
    `L e (n e) k` which, by definition, is a good approximation at scale `k`. Both linear maps are
    close as they are close on a shell of size `2 ^ (-n e)`, by definition.
    -/
    assume ε εpos,
    have pos : 0 < 8 + 8 * ∥c∥ :=
      add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)),
    obtain ⟨e, he⟩ : ∃ (e : ℕ), ∥L0 e - f'∥ < ε / 2 ∧ (1 / 2) ^ e < ε / (8 + 8 * ∥c∥) :=
    begin
      have E₁ := (tendsto_order.1 (tendsto_iff_norm_tendsto_zero.1 hf')).2 (ε/2) (half_pos εpos),
      have : tendsto (λ (n : ℕ), ((1 : ℝ)/2)^n) at_top (𝓝 0) :=
        tendsto_pow_at_top_nhds_0_of_lt_1 (by norm_num) (by norm_num),
      have E₂ := (tendsto_order.1 this).2 _ (div_pos εpos pos),
      exact (E₁.and E₂).exists
    end,
    rw eventually_nhds_iff_ball,
    refine ⟨(1/2) ^ (n e + 1), P, λ y hy, _⟩,
    -- We need to show that `f (x + y) - f x - f' y` is small. For this, we will work at scale
    -- `k` where `k` is chosen with `∥y∥ ∼ 2 ^ (-k)`.
    by_cases y_pos : y = 0, {simp [y_pos] },
    have yzero : 0 < ∥y∥ := norm_pos_iff.mpr y_pos,
    have y_lt : ∥y∥ < (1/2) ^ (n e + 1), by simpa using mem_ball_iff_norm.1 hy,
    have yone : ∥y∥ ≤ 1 :=
      le_trans (y_lt.le) (pow_le_one _ (by norm_num) (by norm_num)),
    -- define the scale `k`.
    obtain ⟨k, hk, h'k⟩ : ∃ (k : ℕ), (1/2) ^ (k + 1) < ∥y∥ ∧ ∥y∥ ≤ (1/2) ^ k :=
      exists_nat_pow_near_of_lt_one yzero yone (by norm_num : (0 : ℝ) < 1/2)
      (by norm_num : (1 : ℝ)/2 < 1),
    -- the scale is large enough (as `y` is small enough)
    have k_gt : n e < k,
    { have : ((1:ℝ)/2) ^ (k + 1) < (1/2) ^ (n e + 1) := lt_trans hk y_lt,
      rw pow_lt_pow_iff_of_lt_one (by norm_num : (0 : ℝ) < 1/2) (by norm_num) at this,
      linarith },
    set m := k - 1 with hl,
    have m_ge : n e ≤ m := nat.le_pred_of_lt k_gt,
    have km : k = m + 1 := (nat.succ_pred_eq_of_pos (lt_of_le_of_lt (zero_le _) k_gt)).symm,
    rw km at hk h'k,
    -- `f` is well approximated by `L e (n e) k` at the relevant scale
    -- (in fact, we use `m = k - 1` instead of `k` because of the precise definition of `A`).
    have J1 : ∥f (x + y) - f x - L e (n e) m ((x + y) - x)∥ ≤ (1/2) ^ e * (1/2) ^ m,
    { apply le_of_mem_A (hn e (n e) m (le_refl _) m_ge).2,
      { simp only [mem_closed_ball, dist_self],
        exact div_nonneg (le_of_lt P) (zero_le_two) },
      { simp [dist_eq_norm],
        convert h'k,
        field_simp,
        ring_exp } },
    have J2 : ∥f (x + y) - f x - L e (n e) m y∥ ≤ 4 * (1/2) ^ e * ∥y∥ := calc
      ∥f (x + y) - f x - L e (n e) m y∥ ≤ (1/2) ^ e * (1/2) ^ m :
        by simpa only [add_sub_cancel'] using J1
      ... = 4 * (1/2) ^ e * (1/2) ^ (m + 2) : by { field_simp, ring_exp }
      ... ≤ 4 * (1/2) ^ e * ∥y∥ :
        mul_le_mul_of_nonneg_left (le_of_lt hk) (mul_nonneg (by norm_num) (le_of_lt P)),
    -- The operator `L e (n e) m` is close to `L0`, as they are close on a shell of
    -- scale `2 ^ (- n e)`.
    have J3 : ∥L e (n e) m - L0 e∥ ≤ 4 * ∥c∥ * (1/2)^e,
    { have I1 : x ∈ A f (L0 e) ((1 / 2) ^ (n e)) ((1/2)^e) :=
        (hn e (n e) (n e) (le_refl _) (le_refl _)).1,
      have I2 : x ∈ A f (L e (n e) m) ((1 / 2) ^ (n e)) ((1/2)^e) :=
        (hn e (n e) m (le_refl _) m_ge).1,
      exact norm_sub_le_of_mem_A hc P P I2 I1, },
    -- combine all the previous estimates to see that `f (x + y) - f x - f' y` is small.
    calc ∥f (x + y) - f x - f' y∥
    = ∥(f (x + y) - f x - L e (n e) m y) + (L e (n e) m - L0 e) y + (L0 e - f') y∥ :
      by { congr' 1, simp, abel }
    ... ≤ ∥f (x + y) - f x - L e (n e) m y∥ + ∥(L e (n e) m - L0 e) y∥ + ∥(L0 e - f') y∥ :
      le_trans (norm_add_le _ _) (add_le_add_right (norm_add_le _ _) _)
    ... ≤ 4 * (1/2) ^ e * ∥y∥ + 4 * ∥c∥ * (1/2) ^ e * ∥y∥ + (ε / 2) * ∥y∥ :
      begin
        apply add_le_add (add_le_add J2 _) _,
        { exact le_trans (le_op_norm _ _) (mul_le_mul_of_nonneg_right J3 (norm_nonneg _)) },
        { exact le_trans (le_op_norm _ _) (mul_le_mul_of_nonneg_right he.1.le (norm_nonneg _)) }
      end
    ... = (4 + 4 * ∥c∥) * ∥y∥ * (1/2) ^ e + (ε / 2) * ∥y∥ : by ring
    ... ≤ (4 + 4 * ∥c∥) * ∥y∥ * (ε / (8 + 8 * ∥c∥)) + (ε / 2) * ∥y∥ :
      begin
        apply add_le_add_right,
        apply mul_le_mul_of_nonneg_left (le_of_lt he.2),
        exact mul_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) (norm_nonneg _)))
          (norm_nonneg _)
      end
    ... = ε * ∥y∥ : by { field_simp [ne_of_gt pos], ring } },
  exact this.differentiable_at,
end

theorem differentiable_eq_B [complete_space F] :
  {x | differentiable_at 𝕜 f x} =
  ⋂ (e : ℕ), ⋃ (n : ℕ), ⋂ (p ≥ n) (q ≥ n), B 𝕜 f ((1/2) ^ p) ((1/2) ^ q) ((1/2) ^ e) :=
subset.antisymm (differentiable_subset_B _ _) (B_subset_differentiable _ _)

end fderiv_measurable_aux

open fderiv_measurable_aux

/-- The set of differentiability points of a function taking values in a complete space is
Borel-measurable. -/
theorem is_measurable_differentiable
  [complete_space F] [measurable_space E] [opens_measurable_space E] :
  is_measurable {x | differentiable_at 𝕜 f x} :=
begin
  rw differentiable_eq_B,
  refine is_measurable.Inter (λ e, _),
  refine is_measurable.Union (λ n, _),
  refine is_measurable.Inter (λ p, _),
  refine is_measurable.Inter_Prop (λ hp, _),
  refine is_measurable.Inter (λ q, _),
  refine is_measurable.Inter_Prop (λ hq, _),
  apply is_open.is_measurable,
  apply is_open_B
end

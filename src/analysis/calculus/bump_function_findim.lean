/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.bump_function_inner
import analysis.calculus.series
import analysis.convolution

/-!
# Smooth functions with arbitrary supports

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
the support of a smooth function taking values in `[0, 1]`, in `is_open.exists_smooth_support_eq`.

Then we use this construction to construct bump functions with nice behavior, by convolving
the indicator function of `closed_ball 0 1` with a function as above with `s = ball 0 1`, rescaled
so that its support becomes the ball `ball 0 D` for some `0 < D < 1`.
-/

noncomputable theory

open set metric topological_space function asymptotics measure_theory finite_dimensional
continuous_linear_map filter measure_theory.measure
open_locale pointwise topological_space nnreal big_operators convolution

variables {E : Type*} [normed_add_comm_group E]

section

variables [normed_space ℝ E] [finite_dimensional ℝ E]

theorem exists_smooth_support_subset {s : set E} {x : E} (hs : s ∈ 𝓝 x) :
  ∃ (f : E → ℝ), f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1 ∧ f x = 1 :=
begin
  obtain ⟨d, d_pos, hd⟩ : ∃ (d : ℝ) (hr : 0 < d), euclidean.ball x d ⊆ s,
    from euclidean.nhds_basis_ball.mem_iff.1 hs,
  let c : cont_diff_bump (to_euclidean x) :=
  { r := d/2,
    R := d,
    r_pos := half_pos d_pos,
    r_lt_R := half_lt_self d_pos },
  let f : E → ℝ := c ∘ to_euclidean,
  have f_supp : f.support ⊆ euclidean.ball x d,
  { assume y hy,
    have : to_euclidean y ∈ function.support c,
      by simpa only [f, function.mem_support, function.comp_app, ne.def] using hy,
    rwa c.support_eq at this },
  refine ⟨f, f_supp.trans hd, _, _, _, _⟩,
  { refine is_compact_of_is_closed_bounded is_closed_closure _,
    have : bounded (euclidean.closed_ball x d), from euclidean.is_compact_closed_ball.bounded,
    apply this.mono _,
    refine (is_closed.closure_subset_iff euclidean.is_closed_closed_ball).2 _,
    exact f_supp.trans euclidean.ball_subset_closed_ball },
  { apply c.cont_diff.comp,
    exact continuous_linear_equiv.cont_diff _ },
  { rintros t ⟨y, rfl⟩,
    exact ⟨c.nonneg, c.le_one⟩ },
  { apply c.one_of_mem_closed_ball,
    apply mem_closed_ball_self,
    exact (half_pos d_pos).le }
end

theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
  nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
  countably many such functions, say `g i`.
  Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
  tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th derivative
  of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the summability
  of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with rfl|h's,
  { exact ⟨(λ x, 0), function.support_zero, cont_diff_const,
      by simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩ },
  let ι := {f : E → ℝ // f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1},
  obtain ⟨T, T_count, hT⟩ : ∃ T : set ι, T.countable ∧ (⋃ f ∈ T, support (f : E → ℝ)) = s,
  { have : (⋃ (f : ι), (f : E → ℝ).support) = s,
    { refine subset.antisymm (Union_subset (λ f, f.2.1)) _,
      assume x hx,
      rcases exists_smooth_support_subset (hs.mem_nhds hx) with ⟨f, hf⟩,
      let g : ι := ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩,
      have : x ∈ support (g : E → ℝ),
        by simp only [hf.2.2.2.2, subtype.coe_mk, mem_support, ne.def, one_ne_zero, not_false_iff],
      exact mem_Union_of_mem _ this },
    simp_rw ← this,
    apply is_open_Union_countable,
    rintros ⟨f, hf⟩,
    exact hf.2.2.1.continuous.is_open_support },
  obtain ⟨g0, hg⟩ : ∃ (g0 : ℕ → ι), T = range g0,
  { apply countable.exists_eq_range T_count,
    rcases eq_empty_or_nonempty T with rfl|hT,
    { simp only [Union_false, Union_empty] at hT,
      simp only [←hT, not_nonempty_empty] at h's,
      exact h's.elim },
    { exact hT } },
  let g : ℕ → E → ℝ := λ n, (g0 n).1,
  have g_s : ∀ n, support (g n) ⊆ s := λ n, (g0 n).2.1,
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n),
  { assume x hx,
    rw ← hT at hx,
    obtain ⟨i, iT, hi⟩ : ∃ (i : ι) (hi : i ∈ T), x ∈ support (i : E → ℝ),
      by simpa only [mem_Union] using hx,
    rw [hg, mem_range] at iT,
    rcases iT with ⟨n, hn⟩,
    rw ← hn at hi,
    exact ⟨n, hi⟩ },
  have g_smooth : ∀ n, cont_diff ℝ ⊤ (g n) := λ n, (g0 n).2.2.2.1,
  have g_comp_supp : ∀ n, has_compact_support (g n) := λ n, (g0 n).2.2.1,
  have g_nonneg : ∀ n x, 0 ≤ g n x,
    from λ n x, ((g0 n).2.2.2.2 (mem_range_self x)).1,
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
    ∃ (δ : ℕ → ℝ≥0), (∀ (i : ℕ), 0 < δ i) ∧ ∃ (c : nnreal), has_sum δ c ∧ c < 1,
    from nnreal.exists_pos_sum_of_countable one_ne_zero ℕ,
  have : ∀ (n : ℕ), ∃ (r : ℝ),
    0 < r ∧ ∀ i ≤ n, ∀ x, ∥iterated_fderiv ℝ i (r • g n) x∥ ≤ δ n,
  { assume n,
    have : ∀ i, ∃ R, ∀ x, ∥iterated_fderiv ℝ i (λ x, g n x) x∥ ≤ R,
    { assume i,
      have : bdd_above (range (λ x, ∥iterated_fderiv ℝ i (λ (x : E), g n x) x∥)),
      { apply ((g_smooth n).continuous_iterated_fderiv le_top).norm
          .bdd_above_range_of_has_compact_support,
        apply has_compact_support.comp_left _ norm_zero,
        apply (g_comp_supp n).iterated_fderiv },
      rcases this with ⟨R, hR⟩,
      exact ⟨R, λ x, hR (mem_range_self _)⟩ },
    choose R hR using this,
    let M := max (((finset.range (n+1)).image R).max' (by simp)) 1,
    have M_pos : 0 < M := zero_lt_one.trans_le (le_max_right _ _),
    have δnpos : 0 < δ n := δpos n,
    have IR : ∀ i ≤ n, R i ≤ M,
    { assume i hi,
      refine le_trans _ (le_max_left _ _),
      apply finset.le_max',
      apply finset.mem_image_of_mem,
      simp only [finset.mem_range],
      linarith },
    refine ⟨M⁻¹ * δ n, by positivity, λ i hi x, _⟩,
    calc ∥iterated_fderiv ℝ i ((M⁻¹ * δ n) • g n) x∥
        = ∥(M⁻¹ * δ n) • iterated_fderiv ℝ i (g n) x∥ :
      by { rw iterated_fderiv_const_smul_apply, exact (g_smooth n).of_le le_top }
    ... = M⁻¹ * δ n * ∥iterated_fderiv ℝ i (g n) x∥ :
      by { rw [norm_smul, real.norm_of_nonneg], positivity }
    ... ≤ M⁻¹ * δ n * M :
      mul_le_mul_of_nonneg_left ((hR i x).trans (IR i hi)) (by positivity)
    ... = δ n : by field_simp [M_pos.ne'] },
  choose r rpos hr using this,
  have S : ∀ x, summable (λ n, (r n • g n) x),
  { assume x,
    refine summable_of_nnnorm_bounded _ δc.summable (λ n, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm],
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) x },
  refine ⟨λ x, (∑' n, (r n • g n) x), _, _, _⟩,
  { apply subset.antisymm,
    { assume x hx,
      simp only [pi.smul_apply, algebra.id.smul_eq_mul, mem_support, ne.def] at hx,
      contrapose! hx,
      have : ∀ n, g n x = 0,
      { assume n,
        contrapose! hx,
        exact g_s n hx },
      simp only [this, mul_zero, tsum_zero] },
    { assume x hx,
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n), from s_g x hx,
      have I : 0 < r n * g n x,
        from mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (ne.symm hn)),
      exact ne_of_gt (tsum_pos (S x) (λ i, mul_nonneg (rpos i).le (g_nonneg i x)) n I) } },
  { refine cont_diff_tsum_of_eventually (λ n, (g_smooth n).const_smul _)
      (λ k hk, (nnreal.has_sum_coe.2 δc).summable) _,
    assume i hi,
    simp only [nat.cofinite_eq_at_top, pi.smul_apply, algebra.id.smul_eq_mul,
      filter.eventually_at_top, ge_iff_le],
    exact ⟨i, λ n hn x, hr _ _ hn _⟩ },
  { rintros - ⟨y, rfl⟩,
    refine ⟨tsum_nonneg (λ n, mul_nonneg (rpos n).le (g_nonneg n y)), le_trans _ c_lt.le⟩,
    have A : has_sum (λ n, (δ n : ℝ)) c, from nnreal.has_sum_coe.2 δc,
    rw ← A.tsum_eq,
    apply tsum_le_tsum _ (S y) A.summable,
    assume n,
    apply (le_abs_self _).trans,
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) y }
end

end

section

namespace exists_cont_diff_bump_base

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the characteristic function of the closed unit ball. -/
def φ : E → ℝ := (closed_ball (0 : E) 1).indicator (λ y, (1 : ℝ))

variables [normed_space ℝ E]  [finite_dimensional ℝ E]

section helper_definitions

variable (E)
lemma u_exists : ∃ u : E → ℝ, cont_diff ℝ ⊤ u ∧
  (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧ (support u = ball 0 1) ∧ (∀ x, u (-x) = u x) :=
begin
  have A : is_open (ball (0 : E) 1), from is_open_ball,
  obtain ⟨f, f_support, f_smooth, f_range⟩ :
    ∃ (f : E → ℝ), f.support = ball (0 : E) 1 ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1,
    from A.exists_smooth_support_eq,
  have B : ∀ x, f x ∈ Icc (0 : ℝ) 1 := λ x, f_range (mem_range_self x),
  refine ⟨λ x, (f x + f (-x)) / 2, _, _, _, _⟩,
  { exact (f_smooth.add (f_smooth.comp cont_diff_neg)).div_const },
  { assume x,
    split,
    { linarith [(B x).1, (B (-x)).1] },
    { linarith [(B x).2, (B (-x)).2] } },
  { refine support_eq_iff.2 ⟨λ x hx, _, λ x hx, _⟩,
    { apply ne_of_gt,
      have : 0 < f x,
      { apply lt_of_le_of_ne (B x).1 (ne.symm _),
        rwa ← f_support at hx },
      linarith [(B (-x)).1] },
    { have I1 : x ∉ support f, by rwa f_support,
      have I2 : -x ∉ support f,
      { rw f_support,
        simp only at hx,
        simpa using hx },
      simp only [mem_support, not_not] at I1 I2,
      simp only [I1, I2, add_zero, zero_div] } },
  { assume x, simp only [add_comm, neg_neg] }
end

variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, and with support equal to the unit ball. -/
def u (x : E) : ℝ := classical.some (u_exists E) x

variable (E)
lemma u_smooth : cont_diff ℝ ⊤ (u : E → ℝ) := (classical.some_spec (u_exists E)).1

lemma u_continuous : continuous (u : E → ℝ) := (u_smooth E).continuous

lemma u_support : support (u : E → ℝ) = ball 0 1 := (classical.some_spec (u_exists E)).2.2.1

lemma u_compact_support : has_compact_support (u : E → ℝ) :=
begin
  rw [has_compact_support_def, u_support, closure_ball (0 : E) one_ne_zero],
  exact is_compact_closed_ball _ _,
end
variable {E}

lemma u_nonneg (x : E) : 0 ≤ u x := ((classical.some_spec (u_exists E)).2.1 x).1

lemma u_le_one (x : E) : u x ≤ 1 := ((classical.some_spec (u_exists E)).2.1 x).2

lemma u_symm (x : E) : u (-x) = u x := (classical.some_spec (u_exists E)).2.2.2 x

variables [measurable_space E] [borel_space E]

local notation `μ` := measure_theory.measure.add_haar

variable (E)
lemma u_int_pos : 0 < ∫ (x : E), u x ∂μ :=
begin
  refine (integral_pos_iff_support_of_nonneg u_nonneg _).mpr _,
  { exact (u_continuous E).integrable_of_has_compact_support (u_compact_support E) },
  { rw u_support, exact measure_ball_pos _ _ zero_lt_one }
end
variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces,
which is smooth, symmetric, with support equal to the ball of radius `D` and integral `1`. -/
def W (D : ℝ) (x : E) : ℝ := ((∫ (x : E), u x ∂μ) * |D|^(finrank ℝ E))⁻¹ • u (D⁻¹ • x)

lemma W_def (D : ℝ) :
  (W D : E → ℝ) = λ x, ((∫ (x : E), u x ∂μ) * |D|^(finrank ℝ E))⁻¹ • u (D⁻¹ • x) :=
by { ext1 x, refl }

lemma W_mul_φ_nonneg (D : ℝ) (x y : E) : 0 ≤ W D y * φ (x - y) :=
begin
  refine mul_nonneg _ (indicator_nonneg (by simp only [zero_le_one, implies_true_iff]) _),
  apply mul_nonneg _ (u_nonneg _),
  apply inv_nonneg.2,
  apply mul_nonneg (u_int_pos E).le,
  apply pow_nonneg (abs_nonneg D)
end

variable (E)
lemma W_support {D : ℝ} (Dpos : 0 < D) : support (W D : E → ℝ) = ball 0 D :=
begin
  have B : D • ball (0 : E) 1 = ball 0 D,
    by rw [smul_unit_ball Dpos.ne', real.norm_of_nonneg Dpos.le],
  have C : D ^ finrank ℝ E ≠ 0, from pow_ne_zero _ Dpos.ne',
  simp only [W_def, algebra.id.smul_eq_mul, support_mul, support_inv, univ_inter,
    support_comp_inv_smul₀ Dpos.ne', u_support, B, support_const (u_int_pos E).ne',
    support_const C, abs_of_nonneg Dpos.le],
end

lemma W_compact_support {D : ℝ} (Dpos : 0 < D) : has_compact_support (W D : E → ℝ) :=
begin
  rw [has_compact_support_def, W_support E Dpos, closure_ball (0 : E) Dpos.ne'],
  exact is_compact_closed_ball _ _,
end
variable {E}

/-- An auxiliary function to construct partitions of unity on finite-dimensional real vector spaces.
It is the convolution between a smooth function of integral `1` supported in the ball of radius `D`,
with the indicator function of the closed unit ball. Therefore, it is smooth, equal to `1` on the
ball of radius `1 - D`, with support equal to the ball of radius `1 + D`. -/
def Y (D : ℝ) : E → ℝ := W D ⋆[lsmul ℝ ℝ, μ] φ

lemma Y_neg (D : ℝ) (x : E) : Y D (-x) = Y D x :=
begin
  apply convolution_neg_of_neg_eq,
  { apply eventually_of_forall (λ x, _),
    simp only [W_def, u_symm, smul_neg, algebra.id.smul_eq_mul, mul_eq_mul_left_iff,
      eq_self_iff_true, true_or], },
  { apply eventually_of_forall (λ x, _),
    simp only [φ, indicator, mem_closed_ball_zero_iff, norm_neg] },
end

lemma Y_eq_one_of_mem_closed_ball {D : ℝ} {x : E} (Dpos : 0 < D)
  (hx : x ∈ closed_ball (0 : E) (1 - D)) : Y D x = 1 :=
begin
  change (W D ⋆[lsmul ℝ ℝ, μ] φ) x = 1,
  have B : ∀ (y : E), y ∈ ball x D → φ y = 1,
  { have C : ball x D ⊆ ball 0 1,
    { apply ball_subset_ball',
      simp only [mem_closed_ball] at hx,
      linarith only [hx] },
    assume y hy,
    simp only [φ, indicator, mem_closed_ball, ite_eq_left_iff, not_le, zero_ne_one],
    assume h'y,
    linarith only [mem_ball.1 (C hy), h'y] },
  have Bx : φ x = 1, from B _ (mem_ball_self Dpos),
  have B' : ∀ y, y ∈ ball x D → φ y = φ x, by { rw Bx, exact B },
  rw convolution_eq_right' _ (le_of_eq (W_support E Dpos)) B',
  simp only [continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply, lsmul_apply,
    algebra.id.smul_eq_mul, integral_mul_left, integral_mul_right, W_def],
  rw [integral_comp_inv_smul_of_pos μ (u : E → ℝ) Dpos, Bx, mul_one, smul_eq_mul,
      abs_of_nonneg Dpos.le],
  field_simp [Dpos.ne', (u_int_pos E).ne'],
end

lemma Y_eq_zero_of_not_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D)
  (hx : x ∉ ball (0 : E) (1 + D)) : Y D x = 0 :=
begin
  change (W D ⋆[lsmul ℝ ℝ, μ] φ) x = 0,
  have B : ∀ y, y ∈ ball x D →  φ y = 0,
  { assume y hy,
    simp only [φ, indicator, mem_closed_ball_zero_iff, ite_eq_right_iff, one_ne_zero],
    assume h'y,
    have C : ball y D ⊆ ball 0 (1+D),
    { apply ball_subset_ball',
      rw ← dist_zero_right at h'y,
      linarith only [h'y] },
    exact hx (C (mem_ball_comm.1 hy)) },
  have Bx : φ x = 0, from B _ (mem_ball_self Dpos),
  have B' : ∀ y, y ∈ ball x D → φ y = φ x, by { rw Bx, exact B },
  rw convolution_eq_right' _ (le_of_eq (W_support E Dpos)) B',
  simp only [lsmul_apply, algebra.id.smul_eq_mul, Bx, mul_zero, integral_const]
end

lemma Y_nonneg (D : ℝ) (x : E) : 0 ≤ Y D x :=
integral_nonneg (W_mul_φ_nonneg D x)

lemma Y_le_one {D : ℝ} (x : E) (Dpos : 0 < D) : Y D x ≤ 1 :=
begin
  have A := u_int_pos E,
  have C : (W D ⋆[lsmul ℝ ℝ, μ] φ) x ≤ (W D ⋆[lsmul ℝ ℝ, μ] 1) x,
  { refine integral_mono_of_nonneg (eventually_of_forall (W_mul_φ_nonneg D x)) _ _,
    { refine (has_compact_support.convolution_exists_left _ (W_compact_support E Dpos) _ _ _)
        .integrable,
      { exact continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _)) },
      { apply locally_integrable_const (1 : ℝ), apply_instance } },
    { apply eventually_of_forall (λ y, _),
      simp only [continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply,
        lsmul_apply, algebra.id.smul_eq_mul, pi.one_apply, mul_one, W_def],
      refine mul_le_of_le_one_right (mul_nonneg (by positivity) (u_nonneg _)) _,
      apply indicator_le_self' (λ x hx, zero_le_one),
      apply_instance } },
  have D : (W D ⋆[lsmul ℝ ℝ, μ] (λ y, (1 : ℝ))) x = 1,
  { simp only [convolution, continuous_linear_map.map_smul, mul_inv_rev, coe_smul', pi.smul_apply,
      lsmul_apply, algebra.id.smul_eq_mul, mul_one, integral_mul_left, W_def],
    rw [integral_comp_inv_smul_of_pos μ (u : E → ℝ) Dpos, smul_eq_mul, abs_of_nonneg Dpos.le],
    field_simp [Dpos.ne', A.ne'], },
  exact C.trans (le_of_eq D)
end

lemma Y_pos_of_mem_ball {D : ℝ} {x : E} (Dpos : 0 < D) (D_lt_one : D < 1)
  (hx : x ∈ ball (0 : E) (1 + D)) : 0 < Y D x :=
begin
  simp only [mem_ball_zero_iff] at hx,
  refine (integral_pos_iff_support_of_nonneg (W_mul_φ_nonneg D x) _).2 _,
  { have F_comp : has_compact_support (W D),
      from W_compact_support E Dpos,
    have B : locally_integrable (φ : E → ℝ) μ,
      from (locally_integrable_const _).indicator measurable_set_closed_ball,
    have C : continuous (W D : E → ℝ),
      from continuous_const.mul ((u_continuous E).comp (continuous_id.const_smul _)),
    exact (has_compact_support.convolution_exists_left (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
      F_comp C B x).integrable },
  { set z := (D / (1 + D)) • x with hz,
    have B : 0 < 1 + D, by linarith,
    have C : ball z (D * (1 + D- ∥x∥) / (1 + D)) ⊆ support (λ (y : E), W D y * φ (x - y)),
    { assume y hy,
      simp only [support_mul, W_support E Dpos],
      simp only [φ, mem_inter_iff, mem_support, ne.def, indicator_apply_eq_zero,
        mem_closed_ball_zero_iff, one_ne_zero, not_forall, not_false_iff, exists_prop, and_true],
      split,
      { apply ball_subset_ball' _ hy,
        simp only [z, norm_smul, abs_of_nonneg Dpos.le, abs_of_nonneg B.le, dist_zero_right,
          real.norm_eq_abs, abs_div],
        simp only [div_le_iff B] with field_simps,
        ring_nf },
      { have ID : ∥D / (1 + D) - 1∥ = 1 / (1 + D),
        { rw real.norm_of_nonpos,
          { simp only [B.ne', ne.def, not_false_iff, mul_one, neg_sub, add_tsub_cancel_right]
              with field_simps},
          { simp only [B.ne', ne.def, not_false_iff, mul_one] with field_simps,
            apply div_nonpos_of_nonpos_of_nonneg _ B.le,
            linarith only, } },
        rw ← mem_closed_ball_iff_norm',
        apply closed_ball_subset_closed_ball' _ (ball_subset_closed_ball hy),
        rw [← one_smul ℝ x, dist_eq_norm, hz, ← sub_smul, one_smul, norm_smul, ID],
        simp only [-one_div, -mul_eq_zero, B.ne', div_le_iff B] with field_simps,
        simp only [mem_ball_zero_iff] at hx,
        nlinarith only [hx, D_lt_one] } },
    apply lt_of_lt_of_le _ (measure_mono C),
    apply measure_ball_pos,
    exact div_pos (mul_pos Dpos (by linarith only [hx])) B }
end

lemma Y_smooth {D : ℝ} (Dpos : 0 < D) : cont_diff ℝ ⊤ (Y D : E → ℝ) :=
begin
  apply has_compact_support.cont_diff_convolution_left,
  { apply W_compact_support E Dpos },
  { exact (cont_diff.comp (u_smooth E) (cont_diff_id.const_smul _)).const_smul _ },
  { exact (locally_integrable_const _).indicator measurable_set_closed_ball }
end


variable (E)

lemma Y_support {D : ℝ} (Dpos : 0 < D) (D_lt_one : D < 1) :
  support (Y D : E → ℝ) = ball (0 : E) (1 + D) :=
support_eq_iff.2 ⟨λ x hx, (Y_pos_of_mem_ball Dpos D_lt_one hx).ne',
  λ x hx, Y_eq_zero_of_not_mem_ball Dpos hx⟩

variable {E}

end helper_definitions

@[priority 100]
instance {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E] :
  has_cont_diff_bump E :=
begin
  refine ⟨⟨_⟩⟩,
  borelize E,
  have IR : ∀ (R : ℝ), 1 < R → 0 < (R - 1) / (R + 1),
  { assume R hR, apply div_pos; linarith },
  exact
  { to_fun := λ R x, if 1 < R then Y ((R - 1) / (R + 1)) (((R + 1) / 2)⁻¹ • x) else 0,
    mem_Icc := λ R x, begin
      split_ifs,
      { refine ⟨Y_nonneg _ _, Y_le_one _ (IR R h)⟩ },
      { simp only [pi.zero_apply, left_mem_Icc, zero_le_one] }
    end,
    symmetric := λ R x, begin
      split_ifs,
      { simp only [Y_neg, smul_neg] },
      { refl },
    end,
    smooth := λ R hR, begin
      simp only [hR, if_true],
      exact (Y_smooth (IR _ hR)).comp (cont_diff_id.const_smul _),
    end,
    eq_one := λ R hR x hx, begin
      have A : 0 < R + 1, by linarith,
      simp only [hR, if_true],
      apply Y_eq_one_of_mem_closed_ball (IR R hR),
      simp only [norm_smul, inv_div, mem_closed_ball_zero_iff, real.norm_eq_abs, abs_div,
                 abs_two, abs_of_nonneg A.le],
      calc 2 / (R + 1) * ∥x∥ ≤ 2 / (R + 1) * 1 :
        mul_le_mul_of_nonneg_left hx (div_nonneg zero_le_two A.le)
      ... = 1 - (R - 1) / (R + 1) : by { field_simp [A.ne'], ring }
    end,
    support := λ R hR, begin
      have A : 0 < (R + 1) / 2, by linarith,
      have A' : 0 < R + 1, by linarith,
      have C :  (R - 1) / (R + 1) < 1, by { apply (div_lt_one _ ).2; linarith },
      simp only [hR, if_true, support_comp_inv_smul₀ A.ne', Y_support _ (IR R hR) C,
        smul_ball A.ne', real.norm_of_nonneg A.le, smul_zero],
      congr' 1,
      field_simp [A'.ne'],
      ring,
    end },
end

end exists_cont_diff_bump_base

end

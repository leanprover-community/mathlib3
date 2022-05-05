/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.complex.abs_max
import analysis.asymptotics.superpolynomial_decay

/-!
-/

open set function filter asymptotics metric complex
open_locale topological_space filter real

local notation `expR` := real.exp

namespace phragmen_lindelof

variables {E : Type*} [normed_group E] [normed_space ℂ E] {a b C : ℝ} {f : ℂ → E} {z : ℂ}

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `∥f z∥` is bounded from above by a constant `C` on the boundary of `U`.

Then `∥f z∥` is bounded by the same constant on the closed strip
`{z : ℂ | a ≤ im z ≤ b}`. Moreover, it suffices to verify the second assumption
only for sufficiently large values of `|re z|`.
-/
lemma horizontal_strip (hfd : diff_cont_on_cl ℂ f (im ⁻¹' Ioo a b))
  (hB : ∃ (c < π / (b - a)) B, is_O f (λ z, expR (B * expR (c * |z.re|)))
    (comap (has_abs.abs ∘ re) at_top ⊓ 𝓟 (im ⁻¹' Ioo a b)))
  (hle_a : ∀ z : ℂ, im z = a → ∥f z∥ ≤ C) (hle_b : ∀ z, im z = b → ∥f z∥ ≤ C)
  (hz : im z ∈ Icc a b) :
  ∥f z∥ ≤ C :=
begin
  -- If `im z = a` or `im z = b`, then we apply `hle_a` or `hle_b`, otherwise `im z ∈ Ioo a b`.
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hz with rfl|rfl|hz',
  { exact hle_a _ rfl }, { exact hle_b _ rfl }, clear hz, rename hz' hz,
  -- WLOG, `0 < C`.
  suffices : ∀ C' : ℝ, 0 < C' → (∀ w : ℂ, im w = a → ∥f w∥ ≤ C') →
    (∀ w : ℂ, im w = b → ∥f w∥ ≤ C') → ∥f z∥ ≤ C',
  { refine le_of_forall_le_of_dense (λ C' hC', this C' _ (λ w hw, _) (λ w hw, _)),
    { refine ((norm_nonneg (f (a * I))).trans (hle_a _ _)).trans_lt hC',
      rw [mul_I_im, of_real_re] },
    exacts [(hle_a _ hw).trans hC'.le, (hle_b _ hw).trans hC'.le] },
  clear_dependent C, intros C hC₀ hle_a hle_b,
  -- After a change of variables, we deal with an interval `(a - b, a + b)` instead of `(a, b)`
  obtain ⟨a, b, rfl, rfl⟩ : ∃ a' b', a = a' - b' ∧ b = a' + b',
  { refine ⟨(a + b) / 2, (b - a) / 2, _, _⟩,
    { rw [← sub_div, ← sub_add, add_sub_cancel, ← two_mul, mul_div_cancel_left a two_ne_zero] },
    { rw [← add_div, add_comm (a + b), ← add_assoc, sub_add_cancel, ← two_mul,
        mul_div_cancel_left b two_ne_zero] } },
  have hab : a - b < a + b, from hz.1.trans hz.2,
  have hb : 0 < b,
    by simpa only [sub_eq_add_neg, add_lt_add_iff_left, neg_lt_self_iff] using hab,
  rw [add_sub_sub_cancel, ← two_mul, ← div_div_eq_div_mul] at hB,
  have hπb : 0 < π / 2 / b, from div_pos real.pi_div_two_pos hb,
  -- Choose some `c B : ℝ` satisfying `hB`, then choose `max c 0 < r < π / (b - a)`.
  rcases hB with ⟨c, hc, B, hO⟩,
  obtain ⟨d, ⟨hcd, hd₀⟩, hd⟩ : ∃ d, (c < d ∧ 0 < d) ∧ d < π / 2 / b,
    by simpa only [max_lt_iff] using exists_between (max_lt hc hπb),
  have hb' : d * b < π / 2, from (lt_div_iff hb).1 hd,
  set aff : ℂ → ℂ := λ w, d * (w - a * I),
  set g : ℝ → ℂ → ℂ := λ ε w, exp (ε * (exp (aff w) + exp (-aff w))),
  /- Since `g ε z → 1` as `ε → 0⁻`, it suffices to prove that `∥g ε z • f z∥ ≤ C`
  for all negative `ε`. -/
  suffices : ∀ᶠ ε : ℝ in 𝓝[<] 0, ∥g ε z • f z∥ ≤ C,
  { refine le_of_tendsto (tendsto.mono_left _ nhds_within_le_nhds) this,
    apply ((continuous_of_real.mul continuous_const).cexp.smul continuous_const).norm.tendsto',
    simp, apply_instance },
  filter_upwards [self_mem_nhds_within] with ε ε₀, change ε < 0 at ε₀,
  -- An upper estimate on `∥g ε w∥` that will be used in two branches of the proof.
  obtain ⟨δ, δ₀, hδ⟩ : ∃ δ : ℝ, δ < 0 ∧ ∀ ⦃w⦄, im w ∈ Icc (a - b) (a + b) →
    abs (g ε w) ≤ expR (δ * expR (d * |re w|)),
  { have H : ε * real.cos (d * b) < 0,
      from mul_neg_of_neg_of_pos ε₀ (real.cos_pos_of_mem_Ioo $ abs_lt.1 $
        (abs_of_pos (mul_pos hd₀ hb)).symm ▸ hb'),
    refine ⟨_, H, λ w hw, _⟩,
    replace hw : |im (aff w)| ≤ d * b,
    { rw [← real.closed_ball_eq_Icc] at hw,
      rwa [of_real_mul_im, sub_im, mul_I_im, of_real_re, _root_.abs_mul, abs_of_pos hd₀,
        mul_le_mul_left hd₀] },
    simpa only [of_real_mul_re, _root_.abs_mul, abs_of_pos hd₀, sub_re, mul_I_re, of_real_im,
      zero_mul, neg_zero, sub_zero]
      using abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le ε₀.le hw hb'.le },
  -- `abs (g ε w) ≤ 1` on the lines `w.im = ±π` (actually, it holds everywhere in the strip)
  have hg₁ : ∀ w, (im w = a - b ∨ im w = a + b) → abs (g ε w) ≤ 1,
  { intros w hw,
    refine (hδ $ hw.by_cases _ _).trans (real.exp_le_one_iff.2 _),
    exacts [λ h, h.symm ▸ left_mem_Icc.2 hab.le, λ h, h.symm ▸ right_mem_Icc.2 hab.le,
      mul_nonpos_of_nonpos_of_nonneg δ₀.le (real.exp_pos _).le] },
  /- Our apriori estimate on `f` implies that `g ε w • f w → 0` as `|w.re| → ∞`. In particular,
  its norm is less than or equal to `C` for sufficiently large `|w.re|`. -/
  obtain ⟨R, hzR, hR⟩ : ∃ R : ℝ, |z.re| < R ∧ ∀ w, |re w| = R → im w ∈ Ioo (a - b) (a + b) →
    ∥g ε w • f w∥ ≤ C,
  { refine ((eventually_gt_at_top _).and _).exists,
    rcases hO.exists_pos with ⟨A, hA₀, hA⟩,
    simp only [is_O_with_iff, eventually_inf_principal, eventually_comap, mem_Ioo, ← abs_lt,
      mem_preimage, (∘), real.norm_eq_abs, abs_of_pos (real.exp_pos _)] at hA,
    suffices : tendsto (λ R, expR (δ * expR (d * R) + B * expR (c * R) + real.log A)) at_top (𝓝 0),
    { filter_upwards [this.eventually (ge_mem_nhds hC₀), hA] with R hR Hle w hre him,
      calc ∥g ε w • f w∥ ≤ expR (δ * expR (d * R) + B * expR (c * R) + real.log A) : _
      ... ≤ C : hR,
      rw [norm_smul, real.exp_add, ← hre, real.exp_add, real.exp_log hA₀, mul_assoc, mul_comm _ A],
      exact mul_le_mul (hδ $ Ioo_subset_Icc_self him) (Hle _ hre him) (norm_nonneg _)
        (real.exp_pos _).le },
    refine real.tendsto_exp_at_bot.comp _,
    suffices H : tendsto (λ R, δ + B * (expR ((d - c) * R))⁻¹) at_top (𝓝 (δ + B * 0)),
    { rw [mul_zero, add_zero] at H,
      refine tendsto.at_bot_add _ tendsto_const_nhds,
      simpa only [id, (∘), add_mul, mul_assoc, ← div_eq_inv_mul, ← real.exp_sub,
        ← sub_mul, sub_sub_cancel]
        using H.neg_mul_at_top δ₀ (real.tendsto_exp_at_top.comp $
          tendsto_const_nhds.mul_at_top hd₀ tendsto_id) },
    refine tendsto_const_nhds.add (tendsto_const_nhds.mul _),
    exact tendsto_inv_at_top_zero.comp (real.tendsto_exp_at_top.comp $
      tendsto_const_nhds.mul_at_top (sub_pos.2 hcd) tendsto_id) },
  have hR₀ : 0 < R, from (_root_.abs_nonneg _).trans_lt hzR,
  /- Finally, we apply the bounded version of the maximum modulus principle to the rectangle
  `(-R, R) × (-π / 2, π / 2)`. The function is bounded by `C` on the horizontal sides by assumption
  (and because `∥g ε w∥ ≤ 1`) and on the vertical sides by the choice of `R`. -/
  have hgd : differentiable ℂ (g ε),
    by convert ((((differentiable_id.sub_const _).const_mul _).cexp.add
      ((differentiable_id.sub_const _).const_mul _).neg.cexp).const_mul _).cexp,
  replace hd : diff_cont_on_cl ℂ (λ w, g ε w • f w) (Ioo (-R) R ×ℂ Ioo (a - b) (a + b)),
    from (hgd.diff_cont_on_cl.smul hfd).mono (λ w hw, hw.2),
  convert norm_le_of_forall_mem_frontier_norm_le ((bounded_Ioo _ _).re_prod_im (bounded_Ioo _ _))
    hd (λ w hw, _) _,
  { have hwc := frontier_subset_closure hw,
    rw [frontier_re_prod_im, closure_Ioo (neg_lt_self hR₀).ne, frontier_Ioo hab,
      closure_Ioo hab.ne, frontier_Ioo (neg_lt_self hR₀)] at hw,
    by_cases him : w.im = a - b ∨ w.im = a + b,
    { rw [closure_re_prod_im, closure_Ioo (neg_lt_self hR₀).ne] at hwc,
      rw [norm_smul, ← one_mul C],
      exact mul_le_mul (hg₁ _ him) (him.by_cases (hle_a _) (hle_b _)) (norm_nonneg _) zero_le_one },
    { replace hw : w ∈ {-R, R} ×ℂ Icc (a - b) (a + b), from hw.resolve_left (λ h, him h.2),
      have hw' := eq_endpoints_or_mem_Ioo_of_mem_Icc hw.2, rw ← or.assoc at hw',
      exact hR _ ((abs_eq hR₀.le).2 hw.1.symm) (hw'.resolve_left him) } },
  { rw [closure_re_prod_im, closure_Ioo hab.ne, closure_Ioo (neg_lt_self hR₀).ne],
    exact ⟨abs_le.1 hzR.le, Ioo_subset_Icc_self hz⟩ }
end

/-- **Phragmen-Lindelöf principle** in a strip `U = {z : ℂ | a < im z < b}`.
Let `f : ℂ → E` be a function such that

* `f` is differentiable on `U` and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * exp(c * |re z|))` on `U` for some `c < π / (b - a)`;
* `f z = 0` on the boundary of `U`.

Then `f` is equal to zero on the closed strip `{z : ℂ | a ≤ im z ≤ b}`.
-/
lemma eq_zero_on_horizontal_strip (hd : diff_cont_on_cl ℂ f (im ⁻¹' Ioo a b))
  (hB : ∃ (c < π / (b - a)) B, is_O f (λ z, expR (B * expR (c * |z.re|)))
    (comap (has_abs.abs ∘ re) at_top ⊓ 𝓟 (im ⁻¹' Ioo a b)))
  (ha : ∀ z : ℂ, z.im = a → f z = 0) (hb : ∀ z : ℂ, z.im = b → f z = 0) :
  eq_on f 0 (im ⁻¹' Icc a b) :=
λ z hz, norm_le_zero_iff.1 $ horizontal_strip hd hB
  (λ z hz, (ha z hz).symm ▸ norm_zero.le) (λ z hz, (hb z hz).symm ▸ norm_zero.le) hz

/-- **Phragmen-Lindelöf principle** in the first quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open first quadrant and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open first quadrant
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the boundary of the first quadrant.

Then `∥f z∥` is bounded from above by the same constant on the closed first quadrant. -/
lemma quadrant_I (hd : diff_cont_on_cl ℂ f (Ioi 0 ×ℂ Ioi 0))
  (hB : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 (Ioi 0 ×ℂ Ioi 0)))
  (hre : ∀ x : ℝ, 0 ≤ x → ∥f x∥ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ∥f (x * I)∥ ≤ C)
  (hz : 0 ≤ z.re ∧ 0 ≤ z.im) :
  ∥f z∥ ≤ C :=
begin
  rcases eq_or_ne z 0 with rfl|hzne, { exact hre 0 le_rfl },
  obtain ⟨z, hz, rfl⟩ : ∃ ζ : ℂ, ζ.im ∈ Icc 0 (π / 2) ∧ exp ζ = z,
  { refine ⟨log z, _, exp_log hzne⟩,
    rw log_im,
    exact ⟨arg_nonneg_iff.2 hz.2, arg_le_pi_div_two_iff.2 (or.inl hz.1)⟩ },
  clear hz hzne,
  change ∥(f ∘ exp) z∥ ≤ C,
  have : maps_to exp (im ⁻¹' Ioo 0 (π / 2)) (Ioi 0 ×ℂ Ioi 0),
  { intros z hz,
    rw [mem_re_prod_im, exp_re, exp_im, mem_Ioi, mem_Ioi],
    refine ⟨mul_pos (real.exp_pos _)
      (real.cos_pos_of_mem_Ioo ⟨(neg_lt_zero.2 $ div_pos real.pi_pos two_pos).trans hz.1, hz.2⟩),
      mul_pos (real.exp_pos _)
        (real.sin_pos_of_mem_Ioo ⟨hz.1, hz.2.trans (half_lt_self real.pi_pos)⟩)⟩ },
  refine horizontal_strip (hd.comp differentiable_exp.diff_cont_on_cl this) _ _ _ hz,
  { rw [sub_zero, div_div_cancel' real.pi_pos.ne'],
    rcases hB with ⟨c, hc, B, hO⟩,
    refine ⟨c, hc, max B 0, _⟩,
    rw [← comap_comap, comap_abs_at_top, comap_sup, inf_sup_right],
    refine is_O.join _ ((hO.comp_tendsto $ tendsto_exp_comap_re_at_top.inf this.tendsto).trans $
      is_O.of_bound 1 _),
    { have hc : continuous_within_at f (Ioi 0 ×ℂ Ioi 0) 0,
      { refine (hd.continuous_on _ _).mono subset_closure,
        simp [closure_re_prod_im, mem_re_prod_im] },
      refine (is_O_one_of_tendsto ℝ (hc.tendsto.comp $ tendsto_exp_comap_re_at_bot.inf
        this.tendsto)).trans (is_O_of_le _ (λ w, _)),
      rw [norm_one, real.norm_of_nonneg (real.exp_pos _).le, real.one_le_exp_iff],
      exact mul_nonneg (le_max_right _ _) (real.exp_pos _).le },
    { simp only [eventually_inf_principal, eventually_comap, comp_app, one_mul,
        real.norm_of_nonneg (real.exp_pos _).le, abs_exp, ← real.exp_mul, real.exp_le_exp],
      refine (eventually_ge_at_top 0).mono (λ x hx z hz hz', _),
      rw [hz, _root_.abs_of_nonneg hx, mul_comm _ c],
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (real.exp_pos _).le } },
  { intros w hw, lift w to ℝ using hw,
    rw [comp_app, ← of_real_exp],
    exact hre _ (real.exp_pos _).le },
  { rintro ⟨x, y⟩ (rfl : y = π / 2),
    rw [mk_eq_add_mul_I, comp_app, exp_add_mul_I, ← of_real_cos, ← of_real_sin, real.cos_pi_div_two,
      real.sin_pi_div_two, of_real_zero, of_real_one, one_mul, zero_add, ← of_real_exp],
    exact him _ (real.exp_pos _).le }
end

/-- **Phragmen-Lindelöf principle** in the second quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open second quadrant and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open second quadrant
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the boundary of the second quadrant.

Then `∥f z∥` is bounded from above by the same constant on the closed second quadrant. -/
lemma quadrant_II (hd : diff_cont_on_cl ℂ f (Iio 0 ×ℂ Ioi 0))
  (hB : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 (Iio 0 ×ℂ Ioi 0)))
  (hre : ∀ x : ℝ, x ≤ 0 → ∥f x∥ ≤ C) (him : ∀ x : ℝ, 0 ≤ x → ∥f (x * I)∥ ≤ C)
  (hz : z.re ≤ 0 ∧ 0 ≤ z.im) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', z' * I = z, from ⟨z / I, div_mul_cancel _ I_ne_zero⟩,
  rw [mul_I_re, mul_I_im, neg_nonpos] at hz,
  change ∥(f ∘ (* I)) z∥ ≤ C,
  have H : maps_to (* I) (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Ioi 0),
  { intros w hw,
    simpa only [mem_re_prod_im, mul_I_re, mul_I_im, neg_lt_zero, mem_Iio] using hw.symm },
  refine quadrant_I (hd.comp (differentiable_id.mul_const _).diff_cont_on_cl H)
    (Exists₃.imp (λ c hc B hO, _) hB) him (λ x hx, _) hz.symm,
  { simpa only [(∘), complex.abs_mul, abs_I, mul_one]
      using hO.comp_tendsto ((tendsto_mul_right_cobounded I_ne_zero).inf H.tendsto) },
  { rw [comp_app, mul_assoc, I_mul_I, mul_neg_one, ← of_real_neg],
    exact hre _ (neg_nonpos.2 hx) }
end

/-- **Phragmen-Lindelöf principle** in the third quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open third quadrant and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open third quadrant
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the boundary of the third quadrant.

Then `∥f z∥` is bounded from above by the same constant on the closed third quadrant. -/
lemma quadrant_III (hd : diff_cont_on_cl ℂ f (Iio 0 ×ℂ Iio 0))
  (hB : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 (Iio 0 ×ℂ Iio 0)))
  (hre : ∀ x : ℝ, x ≤ 0 → ∥f x∥ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ∥f (x * I)∥ ≤ C)
  (hz : z.re ≤ 0 ∧ z.im ≤ 0) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z, from ⟨-z, neg_neg z⟩,
  rw [neg_re, neg_im, neg_nonpos, neg_nonpos] at hz,
  change ∥(f ∘ has_neg.neg) z∥ ≤ C,
  have H : maps_to has_neg.neg (Ioi 0 ×ℂ Ioi 0) (Iio 0 ×ℂ Iio 0),
  { intros w hw,
    simpa only [mem_re_prod_im, neg_re, neg_im, neg_lt_zero, mem_Iio] using hw },
  refine quadrant_I (hd.comp differentiable_neg.diff_cont_on_cl H) _ (λ x hx, _) (λ x hx, _) hz,
  { refine Exists₃.imp (λ c hc B hO, _) hB,
    simpa only [(∘), complex.abs_neg]
      using hO.comp_tendsto (tendsto_neg_cobounded.inf H.tendsto) },
  { rw [comp_app, ← of_real_neg],
    exact hre (-x) (neg_nonpos.2 hx) },
  { rw [comp_app, ← neg_mul, ← of_real_neg],
    exact him (-x) (neg_nonpos.2 hx) }
end

/-- **Phragmen-Lindelöf principle** in the fourth quadrant. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open fourth quadrant and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open fourth quadrant
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the boundary of the fourth quadrant.

Then `∥f z∥` is bounded from above by the same constant on the closed fourth quadrant. -/
lemma quadrant_IV (hd : diff_cont_on_cl ℂ f (Ioi 0 ×ℂ Iio 0))
  (hB : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 (Ioi 0 ×ℂ Iio 0)))
  (hre : ∀ x : ℝ, 0 ≤ x → ∥f x∥ ≤ C) (him : ∀ x : ℝ, x ≤ 0 → ∥f (x * I)∥ ≤ C)
  (hz : 0 ≤ z.re ∧ z.im ≤ 0) :
  ∥f z∥ ≤ C :=
begin
  obtain ⟨z, rfl⟩ : ∃ z', -z' = z, from ⟨-z, neg_neg z⟩,
  rw [neg_re, neg_im, neg_nonpos, neg_nonneg] at hz,
  change ∥(f ∘ has_neg.neg) z∥ ≤ C,
  have H : maps_to has_neg.neg (Iio 0 ×ℂ Ioi 0) (Ioi 0 ×ℂ Iio 0),
  { intros w hw,
    simpa only [mem_re_prod_im, neg_re, neg_im, neg_lt_zero, neg_pos, mem_Ioi, mem_Iio] using hw },
  refine quadrant_II (hd.comp differentiable_neg.diff_cont_on_cl H) _ (λ x hx, _) (λ x hx, _) hz,
  { refine Exists₃.imp (λ c hc B hO, _) hB,
    simpa only [(∘), complex.abs_neg]
      using hO.comp_tendsto (tendsto_neg_cobounded.inf H.tendsto) },
  { rw [comp_app, ← of_real_neg],
    exact hre (-x) (neg_nonneg.2 hx) },
  { rw [comp_app, ← neg_mul, ← of_real_neg],
    exact him (-x) (neg_nonpos.2 hx) }
end

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the imaginary axis;
* `f x → 0` as `x : ℝ` tends to infinity.

Then `∥f z∥` is bounded from above by the same constant on the closed right half-plane.
See also `phragmen_lindelof.right_half_plane_of_bounded_on_real` for a stronger version. -/
lemma right_half_plane_of_tendsto_zero_on_real (hd : diff_cont_on_cl ℂ f {z | 0 < z.re})
  (hexp : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 {z | 0 < z.re}))
  (hre : tendsto (λ x : ℝ, f x) at_top (𝓝 0)) (him : ∀ x : ℝ, ∥f (x * I)∥ ≤ C) (hz : 0 ≤ z.re) :
  ∥f z∥ ≤ C :=
begin
  revert z,
  have hle : ∀ C', (∀ x : ℝ, 0 ≤ x → ∥f x∥ ≤ C') → ∀ z : ℂ, 0 ≤ z.re → ∥f z∥ ≤ max C C',
  { intros C' hC' z hz,
    cases le_total z.im 0,
    { refine quadrant_IV (hd.mono $ λ _, and.left) (Exists₃.imp (λ c hc B hO, _) hexp)
        (λ x hx, (hC' x hx).trans $ le_max_right _ _) (λ x hx, (him x).trans (le_max_left _ _))
        ⟨hz, h⟩,
      exact hO.mono (inf_le_inf_left _ $ principal_mono.2 $ λ _, and.left) },
    { refine quadrant_I (hd.mono $ λ _, and.left) (Exists₃.imp (λ c hc B hO, _) hexp)
        (λ x hx, (hC' x hx).trans $ le_max_right _ _) (λ x hx, (him x).trans (le_max_left _ _))
        ⟨hz, h⟩,
      exact hO.mono (inf_le_inf_left _ $ principal_mono.2 $ λ _, and.left) } },
  obtain ⟨x, hx₀, hx⟩ : ∃ x : ℝ, 0 ≤ x ∧ ∀ y : ℝ, 0 ≤ y → ∥f y∥ ≤ ∥f x∥,
  { have hfc : continuous_on (λ x : ℝ, f x) (Ici 0),
    { refine hd.continuous_on.comp continuous_of_real.continuous_on (λ x hx, _),
      rwa closure_set_of_lt_re },
    by_cases h₀ : ∀ x : ℝ, 0 ≤ x → f x = 0,
    { refine ⟨0, le_rfl, λ y hy, _⟩, rw [h₀ y hy, h₀ 0 le_rfl] },
    push_neg at h₀,
    rcases h₀ with ⟨x₀, hx₀, hne⟩,
    have hlt : ∥(0 : E)∥ < ∥f x₀∥, by rwa [norm_zero, norm_pos_iff],
    simpa only [exists_prop]
      using hfc.norm.exists_forall_ge' is_closed_Ici hx₀ _,
    rw [real.cocompact_eq, inf_sup_right, (disjoint_at_bot_principal_Ici (0 : ℝ)).eq_bot,
      bot_sup_eq],
    exact (hre.norm.eventually $ ge_mem_nhds hlt).filter_mono inf_le_left },
  cases le_or_lt (∥f x∥) C,
  { simpa only [max_eq_left h] using hle _ hx },
  { have : is_max_on (norm ∘ f) {z | 0 < z.re} x,
    { rintros z (hz : 0 < z.re),
      simpa [max_eq_right h.le] using hle _ hx _ hz.le },
    have : ∥f 0∥ = ∥f x∥,
    { apply norm_eq_norm_of_is_max_on_of_closed_ball_subset hd this,
      -- move to a lemma?
      intros z hz,
      rw [mem_ball, dist_zero_left, dist_eq, norm_eq_abs, complex.abs_of_nonneg hx₀] at hz,
      rw mem_set_of_eq,
      contrapose! hz,
      calc x ≤ x - z.re : (le_sub_self_iff _).2 hz
      ... ≤ |x - z.re| : le_abs_self _
      ... = |(z - x).re| : by rw [sub_re, of_real_re, _root_.abs_sub_comm]
      ... ≤ abs (z - x) : abs_re_le_abs _ },
    { refine (h.not_le $ this ▸ _).elim,
      simpa using him 0 } }
end

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant `C` on the imaginary axis;
* `∥f x∥` is bounded from above by a constant for large real values of `x`.

Then `∥f z∥` is bounded from above by `C` on the closed right half-plane.
See also `phragmen_lindelof.right_half_plane_of_tendsto_zero_on_real` for a weaker version. -/
lemma right_half_plane_of_bounded_on_real (hd : diff_cont_on_cl ℂ f {z | 0 < z.re})
  (hexp : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 {z | 0 < z.re}))
  (hre : is_bounded_under (≤) at_top (λ x : ℝ, ∥f x∥))
  (him : ∀ x : ℝ, ∥f (x * I)∥ ≤ C) (hz : 0 ≤ z.re) :
  ∥f z∥ ≤ C :=
begin
  suffices : ∀ᶠ ε : ℝ in 𝓝[<] 0, ∥exp (ε * z) • f z∥ ≤ C,
  { refine le_of_tendsto (tendsto.mono_left _ nhds_within_le_nhds) this,
    apply ((continuous_of_real.mul continuous_const).cexp.smul continuous_const).norm.tendsto',
    simp, apply_instance },
  filter_upwards [self_mem_nhds_within] with ε ε₀, change ε < 0 at ε₀,
  set g : ℂ → E := λ z, exp (ε * z) • f z, change ∥g z∥ ≤ C,
  replace hd : diff_cont_on_cl ℂ g {z : ℂ | 0 < z.re},
    from (differentiable_id.const_mul _).cexp.diff_cont_on_cl.smul hd,
  have hgn : ∀ z, ∥g z∥ = expR (ε * z.re) * ∥f z∥,
  { intro z, rw [norm_smul, norm_eq_abs, abs_exp, of_real_mul_re] },
  refine right_half_plane_of_tendsto_zero_on_real hd _ _ (λ y, _) hz,
  { refine Exists₃.imp (λ c hc B hO, (is_O.of_bound 1  _).trans hO) hexp,
    refine (eventually_inf_principal.2 $ eventually_of_forall $ λ z hz, _),
    rw [hgn, one_mul],
    refine mul_le_of_le_one_left (norm_nonneg _) (real.exp_le_one_iff.2 _),
    exact mul_nonpos_of_nonpos_of_nonneg ε₀.le (le_of_lt hz) },
  { simp_rw [g, ← of_real_mul, ← of_real_exp, coe_smul],
    have h₀ : tendsto (λ x : ℝ, expR (ε * x)) at_top (𝓝 0),
      from real.tendsto_exp_at_bot.comp (tendsto_const_nhds.neg_mul_at_top ε₀ tendsto_id),
    exact h₀.zero_smul_is_bounded_under_le hre },
  { rw [hgn, of_real_mul_re, I_re, mul_zero, mul_zero, real.exp_zero, one_mul],
    exact him y }
end

/-- **Phragmen-Lindelöf principle** in the right half-plane. Let `f : ℂ → E` be a function such that

* `f` is differentiable in the open right half-plane and is continuous on its closure;
* `∥f z∥` is bounded from above by `A * exp(B * (abs z) ^ c)` on the open right half-plane
  for some `c < 2`;
* `∥f z∥` is bounded from above by a constant on the imaginary axis;
* `f x`, `x : ℝ`, tends to zero superexponentially fast as `x → ∞`:
  for any natural `n`, `exp (n * x) * ∥f x∥` tends to zero as `x → ∞`.

Then `f` is equal to zero on the closed right half-plane. -/
lemma eq_zero_on_right_half_plane_of_superexponential_decay
  (hd : diff_cont_on_cl ℂ f {z | 0 < z.re})
  (hexp : ∃ (c < (2 : ℝ)) B, is_O f (λ z, expR (B * (abs z) ^ c))
    (comap abs at_top ⊓ 𝓟 {z | 0 < z.re}))
  (hre : superpolynomial_decay at_top expR (λ x, ∥f x∥))
  (him : ∃ C, ∀ x : ℝ, ∥f (x * I)∥ ≤ C) (hz : 0 ≤ z.re) :
  f z = 0 :=
begin
  rcases him with ⟨C, hC⟩,
  revert z,
  suffices : ∀ z : ℂ, 0 < z.re → f z = 0,
  { simpa only [closure_set_of_lt_re] using eq_on.of_subset_closure this hd.continuous_on
      continuous_on_const subset_closure subset.rfl },
  set g : ℕ → ℂ → E := λ n z, (exp z) ^ n • f z,
  have hg : ∀ n z, ∥g n z∥ = (expR z.re) ^ n * ∥f z∥,
  { intros n z, simp only [norm_smul, norm_eq_abs, complex.abs_pow, abs_exp] },
  intros z hz,
  suffices H : ∀ n : ℕ, ∥g n z∥ ≤ C,
  { contrapose! H,
    simp only [hg],
    exact (((tendsto_pow_at_top_at_top_of_one_lt (real.one_lt_exp_iff.2 hz)).at_top_mul
      (norm_pos_iff.2 H) tendsto_const_nhds).eventually (eventually_gt_at_top C)).exists },
  intro n,
  refine right_half_plane_of_tendsto_zero_on_real (differentiable_exp.pow.diff_cont_on_cl.smul hd)
    _ _ (λ y, _) hz.le,
  { rcases hexp with ⟨c, hc, B, hO⟩,
    refine ⟨max c 1, max_lt hc one_lt_two, n + max B 0, is_O.of_norm_left _⟩,
    simp only [hg],
    refine ((is_O_refl (λ z : ℂ, expR z.re ^ n) _).mul hO.norm_left).trans (is_O.of_bound 1 _),
    simp only [← real.exp_nat_mul, ← real.exp_add, real.norm_of_nonneg (real.exp_pos _).le,
      real.exp_le_exp, add_mul, eventually_inf_principal, eventually_comap, one_mul],
    filter_upwards [eventually_ge_at_top (1 : ℝ)] with r hr z hzr hre, subst r,
    refine add_le_add (mul_le_mul_of_nonneg_left _ n.cast_nonneg) _,
    { calc z.re ≤ abs z : re_le_abs _
      ... = abs z ^ (1 : ℝ) : (real.rpow_one _).symm
      ... ≤ abs z ^ (max c 1) : real.rpow_le_rpow_of_exponent_le hr (le_max_right _ _) },
    { exact mul_le_mul (le_max_left _ _) (real.rpow_le_rpow_of_exponent_le hr (le_max_left _ _))
        (real.rpow_nonneg_of_nonneg (abs_nonneg _) _) (le_max_right _ _) } },
  { rw tendsto_zero_iff_norm_tendsto_zero, simp only [hg],
    exact hre n },
  { rw [hg, of_real_mul_re, I_re, mul_zero, real.exp_zero, one_pow, one_mul],
    exact hC y }
end

end phragmen_lindelof

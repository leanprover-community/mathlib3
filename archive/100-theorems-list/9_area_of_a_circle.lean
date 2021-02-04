/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import measure_theory.interval_integral
import analysis.special_functions.trigonometric
import analysis.mean_inequalities

/-!
# Freek № 9: The Area of a Circle

The area of a disc with radius `r` is `π * r^2`.

Skip to line 160.
-/

open set interval_integral real measure_theory filter
open_locale classical
variables {α β : Type*} [measurable_space α] [measurable_space β] {μ : measure α} {ν : measure β}
  [sigma_finite μ] [sigma_finite ν] {f g : α → ℝ} {s t : set α}

lemma measure.eq_restrict_of_measurable_subset (ht : is_measurable t) (t_subset : t ⊆ s) :
  μ t = μ.restrict s t :=
by rw [measure.restrict_apply ht, set.inter_eq_self_of_subset_left t_subset]

lemma measure.restrict_apply' (hs : is_measurable s) : μ.restrict s t = μ (t ∩ s) :=
by rw [← coe_to_outer_measure, measure.restrict_to_outer_measure_eq_to_outer_measure_restrict hs,
      outer_measure.restrict_apply s t _, coe_to_outer_measure]

lemma measure.eq_restrict_of_subset_of_measurable (hs : is_measurable s) (t_subset : t ⊆ s) :
  μ t = μ.restrict s t :=
by rwa [measure.restrict_apply', set.inter_eq_self_of_subset_left t_subset]

lemma measure.restrict_prod_eq_prod_univ {s : set α} (hs : is_measurable s) :
  (μ.restrict s).prod ν = (μ.prod ν).restrict (s.prod univ) :=
begin
  have : ν = ν.restrict set.univ := measure.restrict_univ.symm,
  rwa [this, measure.prod_restrict, ← this],
  exact is_measurable.univ,
end

def region_between (f g : α → ℝ) (s : set α) : set (α × ℝ) :=
{p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Ioo (f p.1) (g p.1)}

lemma region_between_subset (f g : α → ℝ) (s : set α) : region_between f g s ⊆ s.prod univ :=
by simpa only [prod_univ, region_between, set.preimage, set_of_subset_set_of] using λ a, and.left

lemma is_measurable_region_between (hf : measurable f) (hg: measurable g) (hs : is_measurable s) :
  is_measurable (region_between f g s) :=
begin
  dsimp only [region_between, Ioo, mem_set_of_eq, set_of_and],
  refine is_measurable.inter _ ((is_measurable_lt (hf.comp measurable_fst) measurable_snd).inter
    (is_measurable_lt measurable_snd (hg.comp measurable_fst))),
  convert hs.prod is_measurable.univ,
  simp only [and_true, mem_univ],
end

theorem volume_region_between_eq_lintegral'
  (hf : measurable f) (hg : measurable g) (hs : is_measurable s) :
  μ.prod volume (region_between f g s) = ∫⁻ y in s, ennreal.of_real ((g - f) y) ∂μ :=
begin
  rw measure.prod_apply,
  { have h : (λ x, volume {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)})
            = s.indicator (λ x, ennreal.of_real (g x - f x)),
    { funext x,
      rw indicator_apply,
      split_ifs,
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = Ioo (f x) (g x) := by simp [h, Ioo],
        simp only [hx, real.volume_Ioo, sub_zero] },
      { have hx : {a | x ∈ s ∧ a ∈ Ioo (f x) (g x)} = ∅ := by simp [h],
        simp only [hx, measure_empty] } },
    dsimp only [region_between, preimage_set_of_eq],
    rw [h, lintegral_indicator];
    simp only [hs, pi.sub_apply] },
  { exact is_measurable_region_between hf hg hs },
end

theorem volume_region_between_eq_lintegral
  (hf : ae_measurable f (μ.restrict s)) (hg : ae_measurable g (μ.restrict s))
  (hs : is_measurable s) :
  μ.prod volume (region_between f g s) = ∫⁻ y in s, ennreal.of_real ((g - f) y) ∂μ :=
begin
  have h₁ : (λ y, ennreal.of_real ((g - f) y))
          =ᵐ[μ.restrict s]
              λ y, ennreal.of_real ((ae_measurable.mk g hg - ae_measurable.mk f hf) y) :=
    eventually_eq.fun_comp (eventually_eq.sub hg.ae_eq_mk hf.ae_eq_mk) _,
  have h₂ : (μ.restrict s).prod volume (region_between f g s) =
    (μ.restrict s).prod volume (region_between (ae_measurable.mk f hf) (ae_measurable.mk g hg) s),
  { apply measure_congr,
    apply eventually_eq.inter, { refl },
    exact eventually_eq.inter
            (eventually_eq.comp₂ (ae_eq_comp' measurable_fst hf.ae_eq_mk
              measure.prod_fst_absolutely_continuous) _ eventually_eq.rfl)
            (eventually_eq.comp₂ eventually_eq.rfl _
              (ae_eq_comp' measurable_fst hg.ae_eq_mk measure.prod_fst_absolutely_continuous)) },
  rw [lintegral_congr_ae h₁,
      ← volume_region_between_eq_lintegral' hf.measurable_mk hg.measurable_mk hs],
  convert h₂ using 1,
  { rw measure.restrict_prod_eq_prod_univ,
    exacts [measure.eq_restrict_of_subset_of_measurable (hs.prod is_measurable.univ)
      (region_between_subset f g s), hs] },
  { rw measure.restrict_prod_eq_prod_univ,
    exacts [measure.eq_restrict_of_subset_of_measurable (hs.prod is_measurable.univ)
      (region_between_subset (ae_measurable.mk f hf) (ae_measurable.mk g hg) s), hs] },
  { apply_instance },
end

theorem volume_region_between_eq_integral
  (hf : integrable_on f s μ) (hg : integrable_on g s μ)
  (hs : is_measurable s) (hfg : ∀ x ∈ s, f x ≤ g x) : -- (hfg : f ≤ᵐ[μ.restrict s] g)
  μ.prod volume (region_between f g s) = ennreal.of_real (∫ y in s, (g - f) y ∂μ) :=
begin
  have h : g - f =ᵐ[μ.restrict s] λ y, (λ x, nnreal.of_real (g x - f x)) y,
  { rw eventually_eq_iff_exists_mem,
    use s,
    simpa only [measure.ae, mem_set_of_eq, filter.mem_mk, measure.restrict_apply hs.compl,
                measure_empty, compl_inter_self, eq_self_iff_true, true_and] using
      λ x hx, (nnreal.coe_of_real _ (sub_nonneg.mpr (hfg x hx))).symm },
  rw [volume_region_between_eq_lintegral hf.ae_measurable hg.ae_measurable hs,
      integral_congr_ae h, lintegral_congr_ae,
      lintegral_coe_eq_integral _ ((integrable_congr h).mp (hg.sub hf))],
  simpa only,
end

lemma sqrt_ne_zero {x : ℝ} (hlt : 0 < x) : sqrt x ≠ 0 :=
(sqrt_pos.mpr hlt).ne.symm

@[simp] lemma div_sqrt {x : ℝ} : x / sqrt x = sqrt x :=
begin
  cases le_or_lt x 0,
  { rw [sqrt_eq_zero'.mpr h, div_zero] },
  { rw [div_eq_iff (sqrt_ne_zero h), mul_self_sqrt h.le] },
end

lemma sqr_abs {a : ℝ} : (abs a) ^ 2 = a ^ 2 :=
by rw [← sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg a)]

lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), pow_two, mul_self_sqrt hy]

theorem sqr_lt {a b : ℝ} : a^2 < b ↔ -sqrt b < a ∧ a < sqrt b :=
begin
  split,
  { simpa only [← sqrt_lt (pow_two_nonneg a), sqrt_sqr_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sqr_abs],
    exact λ h, (lt_sqrt (abs_nonneg a) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg a) h)).le).mp h },
end

lemma neg_sqrt_lt_of_sqr_lt {a b : ℝ} (h : a^2 < b) : -sqrt b < a := (sqr_lt.mp h).1

lemma lt_sqrt_of_sqr_lt {a b : ℝ} (h : a^2 < b) : a < sqrt b := (sqr_lt.mp h).2

lemma sqr_lt_sqr {x y : ℝ} (h : abs x < y) : x ^ 2 < y ^ 2 :=
by simpa only [sqr_abs] using pow_lt_pow_of_lt_left h (abs_nonneg x) zero_lt_two

lemma sqr_lt_sqr' {x y : ℝ} (h1 : -y < x) (h2 : x < y) : x ^ 2 < y ^ 2 :=
sqr_lt_sqr (abs_lt.mpr ⟨h1, h2⟩)

/-- A disc of radius `r` is defined as the collection of points `(p.1, p.2)` in `ℝ × ℝ` such that
    `p.1 ^ 2 + p.2 ^ 2 < r ^ 2`. -/
def disc {r : ℝ} (h : 0 < r) := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < r ^ 2}

/-- The area of a disc with radius `r`, which can be represented as the region between the two
    curves `λ x, - sqrt (r ^ 2 - x ^ 2)` and `λ x, sqrt (r ^ 2 - x ^ 2)`, is `π * r ^ 2`. -/
theorem volume_disc {r : ℝ} (hr : 0 < r) :
  volume.prod volume (disc hr) = ennreal.of_real (pi * r ^ 2) :=
begin
  have : disc hr = region_between (λ x, -sqrt (r^2 - x^2)) (λ x, sqrt (r^2 - x^2)) (Ioc (-r) r),
  { ext p,
    simp only [disc, region_between, mem_set_of_eq, mem_Ioo, mem_Ioc, pi.neg_apply],
    split;
    intro h,
    { split,
      { rw ← sqrt_sqr hr.le,
        have h' : p.1^2 < r^2 := by linarith [pow_two_nonneg p.2],
        exact ⟨neg_sqrt_lt_of_sqr_lt h', (lt_sqrt_of_sqr_lt h').le⟩ },
      { rw [add_comm, ← lt_sub_iff_add_lt] at h,
        exact sqr_lt.mp h} },
    { rw [add_comm, ← lt_sub_iff_add_lt],
      exact sqr_lt.mpr h.2 } },
  have H : ∀ {f : ℝ → ℝ}, continuous f → integrable_on f (Ioc (-r) r) :=
    λ f hc, (hc.integrable_on_compact compact_Icc).mono_set Ioc_subset_Icc_self,
  obtain ⟨hc1, hc2⟩ := ⟨(continuous_const.sub (continuous_pow 2)).sqrt, continuous_const.mul hc1⟩,
  convert volume_region_between_eq_integral (H hc1.neg) (H hc1) is_measurable_Ioc
    --(eventually_of_forall (λ u, neg_le_self (sqrt_nonneg _))),
    (λ x hx, neg_le_self (sqrt_nonneg _)),
  simp only [pi.sub_apply, sub_neg_eq_add, ← two_mul],
  rw [← integral_of_le, integral_eq_sub_of_has_deriv_at'_of_le (neg_le_self hr.le)
      (((continuous_const.mul (continuous_arcsin.comp (continuous_id.div continuous_const
        (λ x, hr.ne.symm)))).add (continuous_id.mul hc1)).continuous_on) _ hc2.continuous_on],
  { simp only [id.def, add_zero, sqrt_zero, arcsin_neg, pi.div_apply, function.comp_app,
              neg_square, mul_zero, sub_self, neg_div, div_self hr.ne.symm, arcsin_one],
    rw [mul_neg_eq_neg_mul_symm, sub_neg_eq_add, ← mul_div_assoc, add_halves', mul_comm] },
  { rintros x ⟨hx1, hx2⟩,
    convert ((has_deriv_at_const x (r^2)).mul ((has_deriv_at_arcsin _ _).comp x
      ((has_deriv_at_id' x).div (has_deriv_at_const x r) hr.ne.symm))).add
        ((has_deriv_at_id' x).mul (((has_deriv_at_id' x).pow.const_sub (r^2)).sqrt _)),
    { have h : sqrt (1 - x ^ 2 / r ^ 2) * r ^ 2 = r * sqrt (r ^ 2 - x ^ 2),
      { rw [← sqrt_sqr (pow_nonneg hr.le 2), ← sqrt_mul, sub_mul, sqrt_sqr (pow_nonneg hr.le 2),
            div_mul_eq_mul_div_comm, pow_two, mul_div_cancel_left _ (pow_ne_zero 2 hr.ne.symm),
            ← mul_assoc, ← sub_mul, mul_comm, sqrt_mul (pow_nonneg hr.le 2), sqrt_sqr hr.le,
            one_mul],
        simpa only [sub_nonneg, sqrt_sqr (pow_nonneg hr.le 2), div_le_one (pow_pos hr 2)] using
          (sqr_lt_sqr' hx1 hx2).le },
      field_simp,
      rw [h, mul_div_assoc, ← div_div_eq_div_mul, div_self hr.ne.symm, mul_one_div, mul_left_comm,
          ← pow_two, neg_div, mul_div_mul_left (x^2) (sqrt (r^2-x^2)) two_ne_zero, ← add_assoc,
          add_right_comm, tactic.ring.add_neg_eq_sub, div_sub_div_same, div_sqrt, two_mul] },
    { by_contra hnot,
      rw [not_not, eq_neg_iff_eq_neg, ← div_neg, eq_comm,
          div_eq_one_iff_eq (neg_ne_zero.mpr hr.ne.symm)] at hnot,
      exact hx1.ne.symm hnot },
    { by_contra hnot,
      rw [not_not, div_eq_one_iff_eq hr.ne.symm] at hnot,
      exact hx2.ne hnot },
    { simpa only [sub_ne_zero] using (sqr_lt_sqr' hx1 hx2).ne.symm } },
  { exact neg_le_self hr.le },
end

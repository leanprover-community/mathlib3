import taoziegler.tomathlib.infinite_prod
import taoziegler.tomathlib.finset.image
import analysis.special_functions.log.deriv

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

lemma proddable_of_summable_log (f : β → ℝ) (hf : ∀ᶠ b in cofinite, -1 < f b)
  (h : summable (real.log ∘ f)) : proddable f :=
begin
  by_cases H : ∃ x : β, f x = 0,
  { refine proddable_of_zero _ H },
  push_neg at H,
  set s := {b | f b ≤ -1} with hs,
  have hsf : s.finite,
  { convert hf,
    ext,
    simp },
  have hsp : hsf.to_finset.prod f =
    (- 1) ^ hsf.to_finset.card * real.exp (hsf.to_finset.sum (real.log ∘ f)),
  sorry { simp_rw [real.exp_sum, ←prod_const, ←prod_mul_distrib],
    rw prod_congr rfl,
    simp only [set.finite.mem_to_finset, set.mem_set_of_eq, neg_mul, one_mul],
    intros b hb,
    rw [real.exp_log_of_neg, neg_neg],
    exact hb.trans_lt neg_one_lt_zero },
  have hneg := h.subtype {b | -1 < f b ∧ f b < 0},
  have hpos := h.subtype {b | 0 < f b},
  obtain ⟨nx, hneg⟩ := hneg,
  obtain ⟨x, hpos⟩ := hpos,
  refine ⟨hsf.to_finset.prod f * real.exp nx * real.exp x, _⟩, -- real.exp nx isn't the right thing likely
  suffices : tendsto (λ (s : finset β), (∏ (b : β) in s.filter (λ x, f x ≤ -1), f b) *
    (∏ (b : β) in s.filter (λ x, -1 < f x ∧ f x < 0), f b) *
    ∏ (b : β) in s.filter (λ x, 0 < f x), f b) at_top
      (𝓝 (hsf.to_finset.prod f * real.exp nx * real.exp x)),
  sorry { rw has_prod,
    convert this,
    ext s,
    rw [prod_filter, prod_filter, prod_filter, ←prod_mul_distrib, ←prod_mul_distrib,
        prod_congr rfl],
    intros b hb,
    cases le_or_lt (f b) (-1) with h1 h1,
    { simp [h1, h1.not_lt, (h1.trans neg_one_lt_zero.le).not_lt] },
    cases lt_or_le (f b) 0 with h2 h2,
    { simp [h1, h1.not_le, h2, h2.not_lt] },
    { specialize H b,
      simp [h1, h1.not_le, lt_of_le_of_ne h2 H.symm, h2.not_lt] } },
  refine tendsto.mul _ _,
  convert tendsto.mul _ _,
  sorry { apply_instance },
  sorry { rw tendsto_nhds,
    -- how to use tendsto relating to a finite set?
    intros t ht hmt,
    simp only [mem_at_top_sets, ge_iff_le, le_eq_subset, set.mem_preimage],
    refine ⟨hsf.to_finset, λ s' hs', _⟩,
    rw ←prod_subset (monotone_filter_left _ hs'),
    { simp [hmt] },
    { simp [not_le_of_lt] { contextual := tt } } },
  {
    -- sorry, -- what do?,
    rw has_sum at hneg,
    rw tendsto_at_top_nhds at hneg,
    simp only [comp_app, le_eq_subset] at hneg,
    -- obtain ⟨U, hU⟩ := hneg (set.Ioo (nx - 1) (nx + 1)) (by simp) (is_open_Ioo),
    rw tendsto_at_top_nhds,
    intros V hV hV',
    specialize hneg (real.exp ⁻¹' V) _ _,


    -- rw continuous.tendsto

    -- rw map_le_iff_le_comap at hneg,
    -- rw ←real.log_prod,
  },
  sorry { have := (real.continuous_exp.tendsto _).comp hpos,
    -- how to use tendsto relating to (co)mapping with `finset.image coe`?
    rw tendsto_at_top_nhs at this ⊢,
    intros t ht hmt,
    specialize this t ht hmt,
    simp only [mem_at_top_sets, ge_iff_le, le_eq_subset, set.mem_preimage, comp_app] at this ⊢,
    obtain ⟨u, hu⟩ := this,
    refine ⟨u.map (function.embedding.subtype _), λ v hv, _⟩,
    convert hu (v.subtype _) _,
    { rw real.exp_sum,
      convert (prod_subtype_mem {b : β | 0 < f b} _ _).symm,
      ext ⟨b, posb⟩,
      exact real.exp_log posb },
    { convert subtype_mono hv,
      rw map_subtype } },
end
#exit

lemma has_sum.has_prod_exp {f : β → ℝ} {x : ℝ} (h : has_sum f x) :
  has_prod (real.exp ∘ f) (real.exp x) :=
begin
  refine ((real.continuous_exp.tendsto _).comp h).congr _,
  simp [real.exp_sum]
end

lemma summable.proddable_exp {f : β → ℝ} (h : summable f) : proddable (real.exp ∘ f) :=
let ⟨x, h⟩ := h in ⟨_, h.has_prod_exp⟩

lemma summable_log_one_add_of_summable (s : β → ℝ) (hs : ∀ᶠ i in cofinite, 0 ≤ s i)
  (h : summable s) : summable (λ i, real.log (1 + s i)) :=
begin
  rw ←(@summable_subtype_and_compl _ _ _ _ _ _ _ {b | 0 ≤ s b}) at h ⊢,
  any_goals { apply_instance },
  split,
  { refine summable_of_nonneg_of_le (λ b, real.log_nonneg _)
      (λ b, (real.log_le_sub_one_of_pos _).trans _) h.left,
    { simpa only [le_add_iff_nonneg_right] using b.prop },
    { refine zero_lt_one.trans_le _,
      simpa only [le_add_iff_nonneg_right] using b.prop, },
    { simp } },
  { exact (@has_sum_fintype _ _ _ _ (set.finite.fintype hs) _).summable }
end

lemma proddable_one_add_of_summable (s : β → ℝ) (hs : ∀ᶠ i in cofinite, 0 ≤ s i) (h : summable s) :
  proddable (λ i, 1 + s i) :=
proddable_of_summable_log _ (hs.mono (λ x hx, zero_le_one.trans (le_add_of_nonneg_right hx)))
  (summable_log_one_add_of_summable _ hs h)

-- /-- Expansion of `log (1 - a⁻¹)` as a series in powers of `1 / a`. -/
-- theorem has_sum_log_one_add_inv {a : ℝ} (h : 1 < a) :
--   has_sum (λ (n : ℕ), a⁻¹ ^ (n + 1) / - (n + 1)) (real.log (1 - a⁻¹)) :=
-- begin
--   have : |a⁻¹| < 1,
--   convert (real.has_sum_pow_div_log_of_abs_lt_1 _).neg,
--   -- have h₁ : |1 / (2 * a)| < 1,
--   -- { rw [abs_of_pos, div_lt_one],
--   --   { linarith, },
--   --   { linarith, },
--   --   { exact div_pos one_pos (by linarith), }, },
--   -- convert real.has_sum_log_sub_log_of_abs_lt_1 h₁,
--   -- have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith,
--   -- have h₃ := h.ne',
--   -- rw ← real.log_div,
--   -- { congr,
--   --   field_simp,
--   --   linarith, },
--   -- { field_simp,
--   --   linarith } ,
--   -- { field_simp },
-- end
-- theorem has_sum_log_one_add_inv {a : ℝ} (h : 0 < a) :
--   has_sum (λ k : ℕ, (2 : ℝ) * (1 / (2 * k + 1)) * (1 / (2 * a + 1)) ^ (2 * k + 1))
--   (real.log (1 - a⁻¹)) :=
-- begin
--   refine has_sum.sub
--   -- have h₁ : |1 / (2 * a + 1)| < 1,
--   -- { rw [abs_of_pos, div_lt_one],
--   --   { linarith, },
--   --   { linarith, },
--   --   { exact div_pos one_pos (by linarith), }, },
--   -- convert real.has_sum_log_sub_log_of_abs_lt_1 h₁,
--   -- have h₂ : (2 : ℝ) * a + 1 ≠ 0 := by linarith,
--   -- have h₃ := h.ne',
--   -- rw ← real.log_div,
--   -- { congr,
--   --   field_simp,
--   --   linarith, },
--   -- { field_simp,
--   --   linarith } ,
--   -- { field_simp },
-- end

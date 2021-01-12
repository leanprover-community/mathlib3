/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: James Arthur, Benjamin Davidson, Andrew Souther
-/
import measure_theory.interval_integral
import data.real.sqrt
import data.real.pi
import measure_theory.measure_space
import topology.metric_space.basic

open set interval_integral metric real

-- # Andrew's work

--Def'n and alternate def'n of the unit disc
def unit_disc := {point : ℝ × ℝ | (point.1)^2 + (point.2)^2 < 1 }

def unit_disc_alt := {point : ℝ × ℝ | -1 * sqrt (1 - (point.1)^2) < point.2 ∧
                                       point.2 < sqrt (1 - (point.1)^2)}

--Andrew's work , lemma helpful for first step (unfinished)
lemma unit_disc_open : is_open unit_disc :=
begin
  unfold unit_disc,
  rw is_open_iff,
  intros p hp,
  use (1/2) * (1 - sqrt ((p.1) ^ 2 + (p.2) ^ 2)),
  split,
  { norm_num,
    rw ← sqrt_one,
    exact (sqrt_lt (add_nonneg (pow_two_nonneg p.1) (pow_two_nonneg p.2))).2 hp },
  { intros q hq,
    simp only [dist, mem_ball, mem_set_of_eq, max_lt_iff] at *,
    sorry },
end

-- Added by Ben: Once we have the fact that the unit disc is open, we know it is measurable
lemma unit_disc_measurable : is_measurable unit_disc :=
unit_disc_open.is_measurable

-- Added by Ben: A stronger version of Andrew's `lt_sqrt`
lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), pow_two, mul_self_sqrt hy]

-- Ben's golfed version of `lt_sqrt_of_sqr_lt`
lemma lt_sqrt_of_sqr_lt  {a b : ℝ} (h : a^2 < b) : a < sqrt b :=
begin
  by_contra hnot,
  rw not_lt at hnot,
  have := le_antisymm (le_sqrt_of_sqr_le h.le) hnot,
  rw [this, sqr_sqrt] at h,
  exacts [has_lt.lt.false h, (lt_of_le_of_lt (pow_two_nonneg _) h).le],
end

--Andrew's work : lemma for set eq'ty in second step
lemma lt_sqrt_of_sqr_lt'  {a b : ℝ} (h : a^2 < b) : a < sqrt b :=
begin
  have hb : 0 ≤ b := by linarith [pow_two_nonneg a],
  have := le_sqrt_of_sqr_le (le_of_lt h),
  by_contradiction hyp,
  push_neg at hyp,
  have heq : a = sqrt b := by linarith,
  rw heq at h,
  rw sqr_sqrt hb at h,
  linarith,
end

--Andrew's work : another lemma for set eq'ty in second step
lemma opposite_sqrt_lt_of_sqr_lt {a b : ℝ} (h : a^2 < b) : - sqrt b < a :=
begin
  have hb : 0 ≤ b := by linarith [pow_two_nonneg a],
  by_contradiction hyp,
  push_neg at hyp,
  by_cases ha : a = 0,
  { by_cases hb' : b = 0,
    { rw [ha, hb'] at h, linarith },
    { rw ← ne.def at hb',
      replace hb' := ne.symm hb',
      replace hb' : 0 < b := lt_iff_le_and_ne.2 ⟨hb, hb'⟩,
      have hsqrtb := sqrt_nonneg b,
      have : (-1) * sqrt b ≤ 0 := by linarith,
      rw ha at hyp,
      replace hyp : (-1) * sqrt b = 0 := by linarith,
      replace hyp :  sqrt b = 0 := by linarith,
      replace hyp : b = 0 := (sqrt_eq_zero hb).1 hyp,
      linarith }  },
  { replace ha : a ≠ 0 := by assumption,
    by_cases ha' : a < 0,
    { let c := - a,
      have hc : c = -a := rfl,
      replace hc : a = -c := by linarith,
      rw hc at hyp,
      have hbc : sqrt b ≤ c := by linarith,
      have := (sqrt_le_iff.1 hbc).2,
      replace hc : c = -a := rfl,
      rw hc at this,
      have hsqrtb := sqrt_nonneg b,
      rw neg_square a at this,
      linarith },
    { push_neg at ha',
      replace ha : 0 ≠ a := ne.symm ha,
      have a_pos : 0 < a := lt_iff_le_and_ne.2 ⟨ha', ha⟩,
      have hsqrtb := sqrt_nonneg b,
      have : (-1) * sqrt b ≤ 0 := by linarith,
      linarith }  },
end

--Andrew's work : final lemma for set eq'ty in second step
lemma lt_sqrt' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (le_of_lt (sqrt_pos.2 hy)), pow_two, mul_self_sqrt (le_of_lt hy)]

--Andrew's work, set equality for the second step
lemma second_step : unit_disc  = unit_disc_alt :=
begin
  unfold unit_disc, unfold unit_disc_alt,
  apply set.ext,
  intro point, split,

  { intro hp,
    simp only [neg_one_mul],
    have h₁ : (point.1)^2 + (point.2)^2 < 1 := hp,
    have h₂ : (point.2)^2 < 1 - (point.1)^2 := by linarith,
    exact ⟨opposite_sqrt_lt_of_sqr_lt h₂, lt_sqrt_of_sqr_lt h₂⟩ },

  { intro hp,
    cases hp with hp₁ hp₂,
    have h₁ : 0 ≤ sqrt (1 - point.fst ^ 2) := sqrt_nonneg (1 - point.fst ^ 2),
    have term_pos : (1 - point.fst ^ 2) > 0,
      {by_contradiction hyp,
      push_neg at hyp,
      have := sqrt_eq_zero_of_nonpos hyp,
      rw this at hp₁, rw this at hp₂,
      simp at hp₁,
      linarith },
    by_cases hyp : 0 ≤ point.snd,

    { have h₁ := (lt_sqrt hyp (by linarith)).1 hp₂,
      have h₂ : (point.1)^2 + (point.2)^2 < 1 := by linarith,
      exact h₂ },

    { push_neg at hyp,
      have h₁ :  - point.snd < sqrt (1 - point.fst ^ 2) := by linarith,
      have neg_point_pos : 0 < - point.snd := by linarith,
      have h₂ := (lt_sqrt (le_of_lt neg_point_pos) (by linarith)).1 h₁,
      rw neg_square point.snd at h₂,
      have h₃ : (point.1)^2 + (point.2)^2 < 1 := by linarith,
      exact h₃ } },
end

-- # Ben's work:

variables {β E F : Type*} [measurable_space E] [normed_group E] {f : ℝ → E}
  {c ca cb : E} {a b z : ℝ} {u v ua ub va vb : β → ℝ} {f' : ℝ → E} [normed_space ℝ E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]

-- James' original FTC-2 for open set lemma. Filled in by Ben where able.
-- Note: I believe measurability assumption will drop when we merge master
theorem integral_eq_sub_of_has_deriv_at'_mem_Ioo (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_at f (f' x) x)
  (hcont' : continuous_on f' (interval a b)) (hmeas' : ae_measurable f') :
  ∫ y in a..b, f' y = f b - f a :=
begin
  refine integral_eq_sub_of_has_deriv_right hcont _ hcont' hmeas',
  intros y hy,
  rw [Ico, mem_set_of_eq, le_iff_lt_or_eq, or_and_distrib_right, ← mem_Ioo] at hy,
  cases hy,
  { exact (hderiv y hy).has_deriv_within_at },
  { refine has_deriv_at_interval_left_endpoint_of_tendsto_deriv
      (λ x hx, (hderiv x hx).has_deriv_within_at.differentiable_within_at)
        ((hcont y (Ico_subset_Icc_self
        (mem_Ico.mpr ⟨le_of_eq hy.1, hy.2⟩))).mono Ioo_subset_Icc_self)
          _ _,
    --{ exact Ioo (min a b) (max a b) },
    --{ simpa only [differentiable_on] using λ x hx,
    --(hderiv x hx).has_deriv_within_at.differentiable_within_at },
    --{ simpa only [continuous_on] using (hcont y (Ico_subset_Icc_self
    --(mem_Ico.mpr ⟨le_of_eq hy.1, hy.2⟩))).mono Ioo_subset_Icc_self },
    { rw [hy.1, ← nhds_within_Ioc_eq_nhds_within_Ioi hy.2],
      rw mem_nhds_within_iff_exists_mem_nhds_inter,
      use Ico (y-1) (max a b),
      split,
      { exact Ico_mem_nhds (by linarith) hy.2 },
      { assume c,
        rw [inter_def, Ioc, Ico, mem_set_of_eq],
        intro hc,
        exact mem_Ioo.mpr ⟨hc.2.1, hc.1.2⟩ } },
    { rw tendsto_nhds_within_nhds,
      intros ε hε,
      use ε,
      split,
      exact hε,
      intros x hx hdist,
      sorry } } -- show `dist (deriv f x) (f' y) < ε` from `dist x y < ε`
  end

-- Added by Ben: New version of FTC-2 for open set as per Heather's suggestion. One sorry remaining.
-- Note: I believe measurability assumption will drop when we merge master
theorem integral_eq_sub_of_has_deriv_right_of_mem_Ioo (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_within_at f (f' x) (Ici (min a b)) x)
  (hcont' : continuous_on f' (interval a b)) (hmeas' : ae_measurable f') :
  ∫ y in a..b, f' y = f b - f a :=
begin
  refine integral_eq_sub_of_has_deriv_right hcont _ hcont' hmeas',
  intros y hy,
  rw [Ico, mem_set_of_eq, le_iff_lt_or_eq, or_and_distrib_right, ← mem_Ioo] at hy,
  cases hy,
  { exact (hderiv y hy).mono (Ici_subset_Ici.mpr (le_of_lt hy.1)) },
  { refine has_deriv_at_interval_left_endpoint_of_tendsto_deriv
      (λ x hx, (hderiv x hx).differentiable_within_at.mono (subset.trans Ioo_subset_Ico_self
      Ico_subset_Ici_self))
        ((hcont y (Ico_subset_Icc_self
        (mem_Ico.mpr ⟨le_of_eq hy.1, hy.2⟩))).mono Ioo_subset_Icc_self)
          _ _,
    { rw [hy.1, ← nhds_within_Ioc_eq_nhds_within_Ioi hy.2],
      rw mem_nhds_within_iff_exists_mem_nhds_inter,
      use Ico (y-1) (max a b),
      split,
      { exact Ico_mem_nhds (by linarith) hy.2 },
      { assume c,
        rw [inter_def, Ioc, Ico, mem_set_of_eq],
        intro hc,
        exact mem_Ioo.mpr ⟨hc.2.1, hc.1.2⟩ } },
    -- The remainder of the proof is a WIP
    { simp only,
      convert (continuous_at_iff_continuous_left'_right'.mp
        ((hcont'.continuous_within_at _).continuous_at _)).2.tendsto,
      have := λ u, ((hderiv u _).has_deriv_at _).deriv,

      rw tendsto_nhds_within_nhds,
      intros ε hε,
      use ε,
      split,
      exact hε,
      intros x hx hdist,
      --rw dist_eq_norm,
      --have H := metric.eventually_nhds_iff.mpr (by use ε) hε,
      -- rw [← ((hderiv _ _).has_deriv_at _).deriv],
      sorry } },
end

lemma sqrt_ne_zero {x : ℝ} (hle : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 :=
by rw [not_iff_not, sqrt_eq_zero hle]

lemma div_sqrt {x : ℝ} (hle : 0 ≤ x) : x / sqrt x = sqrt x :=
begin
  by_cases h : x = 0,
  { rw [h, sqrt_zero, zero_div] },
  { rw [div_eq_iff ((sqrt_ne_zero hle).mpr h), mul_self_sqrt hle] },
end

lemma step5_1 : deriv (λ x : ℝ, 1/2 * (arcsin x + x * sqrt(1 - x^2) ) ) = λ x, sqrt(1 - x^2) :=
begin
  ext x,
  have hx : x ≠ -1 ∧ x ≠ 1 := sorry, -- potentially tricky part
  rw [deriv_const_mul, deriv_add (differentiable_at_arcsin.mpr hx), deriv_mul],
  rw [differentiable_at_id', deriv_sqrt, deriv_arcsin],
  simp only [one_mul, deriv_id'', differentiable_at_const, mul_one, zero_sub, deriv_sub,
    differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'', deriv_const', pow_one,
    differentiable_at.pow, nat.cast_one, neg_div],
  rw mul_div_mul_left,
  field_simp,
  rw [add_left_comm, div_add_div_same, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt, ← two_mul,
  rw mul_comm,
  { sorry }, -- show `0 ≤ 1 - x^2`
  { exact two_ne_zero },
  { apply differentiable_at.sqrt,
    { simp},
    { -- 1 - x^2 ≠ 0
      sorry
    }}, -- show `differentiable_at ℝ (λ y, 1 - y ^ 2) x`
  { sorry }, -- show `1 - x^2 ≠ 0`
  { sorry }, -- show `differentiable_at ℝ (λ y, sqrt(1 - y ^ 2)) x`
  { sorry }, -- show `differentiable_at ℝ (λ y, y * sqrt(1 - y ^ 2)) x`
  { sorry }, -- show `differentiable_at ℝ (λ y, arcsin y + y * sqrt(1 - y ^ 2)) x`
end

lemma step5_2 :
    ∫ (x : ℝ) in (-1)..1, 2 * deriv (λ y:ℝ, 1/2 * (arcsin y + y * sqrt (1-y^2))) x = pi :=
begin
  have H : ∀ (x : ℝ), x ∈ interval (-(1:ℝ)) 1 →
      differentiable_at ℝ (λ y:ℝ, arcsin y + y * sqrt (1-y^2)) x,
    sorry,
  have := H _ _,
  simp only [deriv_const_mul ((1:ℝ)/2) this, ← mul_assoc, mul_div_cancel' (1:ℝ) two_ne_zero],
  rw one_mul,
  convert integral_deriv_eq_sub H _,
  { rw [arcsin_one, arcsin_neg_one, one_pow, neg_one_pow_eq_pow_mod_two, nat.bit0_mod_two, pow_zero,
        sub_self, sqrt_zero, mul_zero, mul_zero, add_zero, add_zero, sub_neg_eq_add, add_halves'] },
  { sorry } -- show `continuous_on (deriv (λ y, arcsin y + y * sqrt (1 - y ^ 2))) (interval (-1) 1)`

  -- How we resolve the rest of this proof will depend on how we decide to integrate these substeps
  -- into the final proof. Accordingly, I am leaving it for a later date.
end

-- # James' work:

lemma aux_sqrt_lemma (x : ℝ) (h : 0 < x) : x / real.sqrt x = real.sqrt x :=
begin
  rw div_eq_iff,
  exact (real.mul_self_sqrt (le_of_lt h)).symm,
  { intro Hx,
    rw real.sqrt_eq_zero' at Hx,
    linarith }
end

example : 4 * ∫ (x : ℝ) in (0:ℝ)..1, sqrt(1 - x^2) = pi :=
begin
  have derivH : deriv (λ x : ℝ, 1/2 * (arcsin x + x * sqrt(1 - x^2) ) ) = λ x, sqrt(1 - x^2),
  { ext,
    rw deriv_const_mul,
    rw deriv_add,
    simp only [one_div, deriv_arcsin],
    rw deriv_mul,
    simp only [one_mul, deriv_id''],
    rw deriv_sqrt,
    simp only [differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id',
      deriv_pow'', nat.cast_bit0, deriv_id'', deriv_const', pow_one, differentiable_at.pow],
      rw nat.cast_one,
    rw neg_div,
    rw mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0, by norm_num),
    field_simp,
    rw add_left_comm,
    rw div_add_div_same,
    rw ← pow_two,
    rw tactic.ring.add_neg_eq_sub,
    rw aux_sqrt_lemma,
    rw ← two_mul,
    rw mul_comm,
    { -- 0 < 1 - x^2
      sorry
    },
    { -- differentiable_at ℝ (λ (x : ℝ), 1 - x ^ 2) x
      simp,
    },
    { -- 1 - x^2 ≠ 0
      sorry
    },
    { simp},
    { -- differentiable_at ℝ (λ (y : ℝ), real.sqrt (1 - y ^ 2)) x
      apply differentiable_at.sqrt,
      { simp},
      { -- 1 - x^2 ≠ 0
        sorry
      },
    },
    { -- differentiable_at ℝ (λ (y : ℝ), real.arcsin y) x
      sorry
    },
    { apply differentiable_at.mul,
      { simp},
      { apply differentiable_at.sqrt,
        simp,
        { -- 1 - x^2 ≠ 0
          sorry
        },
      },
    },
    { apply differentiable_at.add,
      { -- differentiable_at ℝ (λ (y : ℝ), real.arcsin y) x
        sorry
      },
      { apply differentiable_at.mul,
        { simp},
        { apply differentiable_at.sqrt,
          simp,
          { -- 1 - x^2 ≠ 0
            sorry
          },
        },
      },
    },
  },
  { -- the actual goal
    --apply integral_deriv_eq_sub,
    sorry
  }
end

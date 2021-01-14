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

open set interval_integral metric real filter


-- # Ben's assorted sqrt, sqr, and abs lemmas

-- A stronger version of Andrew's `lt_sqrt`.
lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (sqrt_nonneg y), pow_two, mul_self_sqrt hy]

lemma lt_sqrt_of_sqr_lt  {a b : ℝ} (h : a^2 < b) : a < sqrt b :=
begin
  by_contra hnot,
  rw [le_antisymm (le_sqrt_of_sqr_le _) (not_lt.mp hnot), sqr_sqrt] at h,
  exacts [h.false, (lt_of_le_of_lt (pow_two_nonneg _) h).le, h.le],
end

lemma sqrt_ne_zero {x : ℝ} (hle : 0 ≤ x) : sqrt x ≠ 0 ↔ x ≠ 0 :=
by rw [not_iff_not, sqrt_eq_zero hle]

-- A stronger version of James' `aux_sqrt_lemma`.
lemma div_sqrt {x : ℝ} (hle : 0 ≤ x) : x / sqrt x = sqrt x :=
begin
  by_cases h : x = 0,
  { rw [h, sqrt_zero, zero_div] },
  { rw [div_eq_iff ((sqrt_ne_zero hle).mpr h), mul_self_sqrt hle] },
end

lemma add_sqr {a b : ℝ} : (a + b)^2 = a^2 + b^2 + 2*a*b := by ring

lemma sqr_add_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a^2 + b^2 ≤ (a+b)^2 :=
by simp only [add_sqr, add_mul, add_le_add_iff_right, ← pow_two, le_add_iff_nonneg_right,
  mul_nonneg (mul_nonneg zero_le_two ha) hb]

lemma sqr_add_le_of_nonpos {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) : a^2 + b^2 ≤ (a+b)^2 :=
by simp only [add_sqr, add_mul, add_le_add_iff_right, ← pow_two, le_add_iff_nonneg_right,
  mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos zero_le_two ha) hb]

lemma sqr_abs {a : ℝ} : (abs a) ^ 2 = a ^ 2 :=
by rw [← sqrt_sqr_eq_abs, sqr_sqrt (pow_two_nonneg a)]

-- Monotocity of the `L^p` norm for 2 summands.
lemma sqr_add_le_add_abs_sqr (a b : ℝ) : a^2 + b^2 ≤ (abs a + abs b)^2 :=
by simpa only [sqr_abs] using sqr_add_le_of_nonneg (abs_nonneg a) (abs_nonneg b)

lemma abs_le_left {a b : ℝ} (h : abs a ≤ b) : -b ≤ a := (abs_le.mp h).1

lemma abs_le_right {a b : ℝ} (h : abs a ≤ b) : a ≤ b := (abs_le.mp h).2

lemma abs_lt_left {a b : ℝ} (h : abs a < b) : -b < a := (abs_lt.mp h).1

lemma abs_lt_right {a b : ℝ} (h : abs a < b) : a < b := (abs_lt.mp h).2

-- For Andrew:
theorem sqr_le {a b : ℝ} : a^2 ≤ b → -sqrt b ≤ a ∧ a ≤ sqrt b :=
begin
  intro h,
  have := sqrt_le_sqrt h,
  rw sqrt_sqr_eq_abs a at this,
  exact abs_le.1 this,
end

-- For Andrew:
theorem sqr_lt {a b : ℝ} : a^2 < b ↔ -sqrt b < a ∧ a < sqrt b :=
begin
  split,
  {intro h,
   rw [← sqrt_lt (pow_two_nonneg a), sqrt_sqr_eq_abs a] at h,
   exact abs_lt.1 (h),},
  {intro h,
   rw ← abs_lt at h,
   rw ← sqr_abs,
   exact (lt_sqrt (abs_nonneg a) (sqrt_pos.1 (lt_of_le_of_lt (abs_nonneg a) h)).le).1 h,},
end



lemma sqr_le_left {a b : ℝ} (h : a^2 ≤ b) : -sqrt b ≤ a := (sqr_le h).1

lemma sqr_le_right {a b : ℝ} (h : a^2 ≤ b) : a ≤ sqrt b := (sqr_le h).2

-- For Andrew for use in step 2:
-- (originally Andrew's `opposite_sqrt_lt_of_sqr_lt`)
lemma sqr_lt_left {a b : ℝ} (h : a^2 < b) : -sqrt b < a := (sqr_lt.mp h).1

lemma sqr_lt_right {a b : ℝ} (h : a^2 < b) : a < sqrt b := (sqr_lt.mp h).2


-- # Andrew's work

--Def'n and alternate def'n of the unit disc
def unit_disc := {point : ℝ × ℝ | (point.1)^2 + (point.2)^2 < 1 }

def unit_disc_alt := {point : ℝ × ℝ | -1 * sqrt (1 - (point.1)^2) < point.2 ∧
                                       point.2 < sqrt (1 - (point.1)^2)}

--version of the triangle inequality, still need to prove
lemma real.Lp_add_two_le (f g : ℝ × ℝ) (p : ℝ) (hp : 1 ≤ p) :
(abs (f.1 + g.1) ^ p + abs (f.2 + g.2) ^ p) ^ (1 / p)
≤ (abs f.1 ^ p + abs f.2 ^ p) ^ (1 / p) + (abs g.1 ^ p + abs g.2 ^ p) ^ (1 / p) := sorry

--alternate version of triangle inequality, handles p : ℕ
lemma real.Lp_add_two_le' (f g : ℝ × ℝ) (p : ℕ) (hp : 1 ≤ p) :
  (abs (f.1 + g.1) ^ p + abs (f.2 + g.2) ^ p) ^ (1 / (p:ℝ))
  ≤ (abs f.1 ^ p + abs f.2 ^ p) ^ (1 / (p:ℝ)) + (abs g.1 ^ p + abs g.2 ^ p) ^ (1 / (p:ℝ)) :=
begin
  have hp' : 1 ≤ (p:ℝ) := by { norm_cast, linarith },
  convert real.Lp_add_two_le f g p hp' using 3;
  simp,
end

/-Lemma helpful for first step.
Still runs a bit slow. We can probably get it cleaner. -/
lemma is_open_unit_disc : is_open unit_disc :=
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
    simp only [dist, mem_ball, mem_set_of_eq, max_lt_iff] at hp hq ⊢,
    rw [← sqrt_lt (add_nonneg (pow_two_nonneg q.1) (pow_two_nonneg q.2)), sqrt_one],
    calc sqrt (q.fst ^ 2 + q.snd ^ 2) ≤ sqrt ((q.1 - p.1)^2 + (q.2 - p.2)^2) + sqrt (p.1^2 + p.2^2) :
      by { have := real.Lp_add_two_le' (q.1 - p.1, q.2 - p.2) p 2 one_le_two,
          simp only [sub_add_cancel] at this,
          rw [sqrt_eq_rpow,
              ← abs_of_nonneg (pow_two_nonneg q.1), ← abs_of_nonneg (pow_two_nonneg q.2),
              ← abs_of_nonneg (pow_two_nonneg (q.1 - p.1)),
              ← abs_of_nonneg (pow_two_nonneg (q.2 - p.2)),
              ← abs_of_nonneg (pow_two_nonneg p.1), ← abs_of_nonneg (pow_two_nonneg p.2),
              abs_pow q.1 2, abs_pow q.2 2, abs_pow p.1 2, abs_pow p.2 2,
              abs_pow (q.1 - p.1) 2, abs_pow (q.2 - p.2) 2],
          exact_mod_cast this }
    ... ≤ abs (q.1 - p.1) + abs (q.2 - p.2) + sqrt (p.1^2 + p.2^2) :
      add_le_add_right (by rw sqrt_le_iff; exact ⟨add_nonneg (abs_nonneg _) (abs_nonneg _),
        sqr_add_le_add_abs_sqr (q.1 - p.1) (q.2 - p.2)⟩) (sqrt (p.fst ^ 2 + p.snd ^ 2))
    ... < 1 : by linarith [add_lt_add hq.1 hq.2] },
end

-- Added by Ben: Once we have the fact that the unit disc is open, we know it is measurable.
lemma is_measurable_unit_disc : is_measurable unit_disc :=
is_open_unit_disc.is_measurable

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

open_locale topological_space

variables {β E F : Type*} [measurable_space E] [normed_group E] {f : ℝ → E}
  {c ca cb : E} {a b z : ℝ} {u v ua ub va vb : β → ℝ} {f' : ℝ → E} [normed_space ℝ E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]

-- FTC-2 for the open set (original version). One sorry remaining.
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
        ((hcont y (Ico_subset_Icc_self (mem_Ico.mpr ⟨le_of_eq hy.1, hy.2⟩))).mono Ioo_subset_Icc_self)
          _ _,
    { rw [hy.1, ← nhds_within_Ioc_eq_nhds_within_Ioi hy.2, mem_nhds_within_iff_exists_mem_nhds_inter],
      use Ico (y-1) (max a b),
      split,
      { exact Ico_mem_nhds (by linarith) hy.2 },
      { assume c hc,
        simpa only [inter_def, Ioc, Ico, mem_set_of_eq] using mem_Ioo.mpr ⟨hc.2.1, hc.1.2⟩ } },
    { have : ∀ x ∈ Ioo (min a b) (max a b), deriv f x = f' x := λ x hx, (hderiv x hx).deriv, -- currently unused
      have hcongr : deriv f =ᶠ[𝓝[Ioi y] y] f',
      { sorry },
      have hf := (hcont'.continuous_within_at (left_mem_Icc.mpr min_le_max)),
      rw [interval, hy.1] at hf,
      have hf' : tendsto f' (𝓝[Ici y] y) (𝓝 (f' y)) :=
        by convert hf using 1; rw ← nhds_within_Icc_eq_nhds_within_Ici hy.2,
      simpa only [tendsto_congr' hcongr] using hf'.mono_left (nhds_within_mono y Ioi_subset_Ici_self) } },
  end

-- Added by Ben: New version of FTC-2 for open set as per Heather's suggestion. One sorry remaining.
-- Note: I believe measurability assumption will drop when we merge master
-- Ignore this proof for now
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

lemma step5_1 {x : ℝ} : deriv (λ y : ℝ, 1/2 * (arcsin y + y * sqrt (1 - y^2))) x = sqrt (1 - x^2) :=
begin
  have hx : x ∈ Ioo (-(1:ℝ)) 1 := sorry, -- must assume this to be true, leave alone for now
  have hlt : 0 < 1 - x^2,
    sorry, -- show `0 < 1 - x^2`
  have h1 : differentiable_at ℝ (λ y:ℝ, 1 - y ^ 2) x,
    sorry, -- show `differentiable_at ℝ (λ y, 1 - y ^ 2) x`
  have h2 : differentiable_at ℝ (λ y:ℝ, sqrt(1 - y ^ 2)) x := h1.sqrt hlt.ne.symm,
  have h3 : differentiable_at ℝ (λ y:ℝ, y * sqrt(1 - y ^ 2)) x,
    sorry, -- show `differentiable_at ℝ (λ y, y * sqrt(1 - y ^ 2)) x`
  have h4 : differentiable_at ℝ (λ y:ℝ, arcsin y + y * sqrt(1 - y ^ 2)) x,
    sorry, -- show `differentiable_at ℝ (λ y, arcsin y + y * sqrt(1 - y ^ 2)) x`
  rw [deriv_const_mul _ h4, deriv_add (differentiable_at_arcsin.mpr ⟨hx.1.ne.symm, hx.2.ne⟩) h3,
      deriv_mul differentiable_at_id' h2, deriv_sqrt h1 hlt.ne.symm, deriv_arcsin],
  simp only [one_mul, deriv_id'', differentiable_at_const, mul_one, zero_sub, deriv_sub,
    differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'', deriv_const', pow_one,
    differentiable_at.pow, nat.cast_one, neg_div],
  rw mul_div_mul_left,
  field_simp,
  rw [add_left_comm, div_add_div_same, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt hlt.le,
      ← two_mul, mul_comm],
  exact two_ne_zero,
end

lemma step5_2 : ∫ (x : ℝ) in (-1)..1, 2 * deriv (λ y:ℝ, 1/2 * (arcsin y + y * sqrt (1-y^2))) x = pi :=
begin
  have H : ∀ (x : ℝ), x ∈ interval (-(1:ℝ)) 1 → differentiable_at ℝ (λ y:ℝ, arcsin y + y * sqrt (1-y^2)) x,
    intros x hx,
    sorry,
  have H' := H _ _,
  simp only [deriv_const_mul _ H', ← mul_assoc, mul_div_cancel' (1:ℝ) two_ne_zero, one_mul],
  convert integral_deriv_eq_sub H _,
  { rw [arcsin_one, arcsin_neg_one, one_pow, neg_one_pow_eq_pow_mod_two, nat.bit0_mod_two, pow_zero,
        sub_self, sqrt_zero, mul_zero, mul_zero, add_zero, add_zero, sub_neg_eq_add, add_halves'] },
  -- show `continuous_on (deriv (λ y, arcsin y + y * sqrt (1 - y ^ 2))) (interval (-1) 1)`:
  { have : (deriv (λ (y : ℝ), arcsin y + y * sqrt (1 - y ^ 2))) = (λ y, sqrt(1 - y^2)) * λ y, 2,
    { sorry }, -- temporary, hope to replace with following lines
    -- have s1 := step5_1,
    -- rw [deriv_const_mul ((1:ℝ)/2) H', mul_comm, ← div_eq_mul_one_div, div_eq_iff] at s1,
    simp only [this],
    exact λ x hx, (continuous_within_at_const.sub (continuous_pow 2).continuous_within_at).sqrt.mul
      continuous_within_at_const },
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

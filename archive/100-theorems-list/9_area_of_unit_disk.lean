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
import analysis.mean_inequalities
import measure_theory.prod
import measure_theory.lebesgue_measure

open set interval_integral metric real filter measure_theory


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

theorem sqr_le {a b : ℝ} (h : a^2 ≤ b) : -sqrt b ≤ a ∧ a ≤ sqrt b :=
abs_le.mp (by simpa [← sqrt_sqr_eq_abs] using sqrt_le_sqrt h)

-- For Andrew:
theorem sqr_le_of_nonneg {a b : ℝ} (h : 0 ≤ b) : a^2 ≤ b ↔ -sqrt b ≤ a ∧ a ≤ sqrt b :=
begin
  split,
  { exact sqr_le },
  { sorry },
end

lemma sqr_le_left {a b : ℝ} (h : a^2 ≤ b) : -sqrt b ≤ a := (sqr_le h).1

lemma sqr_le_right {a b : ℝ} (h : a^2 ≤ b) : a ≤ sqrt b := (sqr_le h).2

theorem sqr_lt {a b : ℝ} : a^2 < b ↔ -sqrt b < a ∧ a < sqrt b :=
begin
  split,
  { simpa only [← sqrt_lt (pow_two_nonneg a), sqrt_sqr_eq_abs] using abs_lt.mp },
  { rw [← abs_lt, ← sqr_abs],
    exact λ h, (lt_sqrt (abs_nonneg a) (sqrt_pos.mp (lt_of_le_of_lt (abs_nonneg a) h)).le).mp h },
end

-- For Andrew for use in step 2:
-- (originally Andrew's `opposite_sqrt_lt_of_sqr_lt`)
lemma sqr_lt_left {a b : ℝ} (h : a^2 < b) : -sqrt b < a := (sqr_lt.mp h).1

lemma sqr_lt_right {a b : ℝ} (h : a^2 < b) : a < sqrt b := (sqr_lt.mp h).2


-- # Andrew's work

--Def'n and alternate def'n of the unit disc
def unit_disc := {point : ℝ × ℝ | (point.1)^2 + (point.2)^2 < 1 }

def unit_disc_alt := {point : ℝ × ℝ | -sqrt (1 - (point.1)^2) < point.2 ∧ point.2 < sqrt (1 - (point.1)^2)}

/--goofy function, turns term of type ℝ × ℝ into term of type fin 2 → ℝ.
used in Minkowski's inequality below-/
def fin_from_prod (p : ℝ × ℝ) : fin 2 → ℝ := λ (a : fin 2),
  if h : (a = 0) then p.1 else p.2

-- Minkowski's inequality for two summands.
lemma real.Lp_add_two_le (f g : ℝ × ℝ) (p : ℝ) (hp : 1 ≤ p) :
(abs (f.1 + g.1) ^ p + abs (f.2 + g.2) ^ p) ^ (1 / p)
≤ (abs f.1 ^ p + abs f.2 ^ p) ^ (1 / p) + (abs g.1 ^ p + abs g.2 ^ p) ^ (1 / p) :=
by simpa [fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod f i + fin_from_prod g i) ^ p),
          fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod f i) ^ p),
          fin.sum_univ_succ (λ (i : fin 2), abs (fin_from_prod g i) ^ p),
          univ_unique, finset.sum_singleton]
    using real.Lp_add_le (finset.univ : finset (fin 2)) (fin_from_prod f) (fin_from_prod g) hp


--alternate version of Minkowski's inequality, handles p : ℕ
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
  rw is_open_iff,
  intros p hp,
  use (1/2) * (1 - sqrt ((p.1) ^ 2 + (p.2) ^ 2)),
  split,
  { norm_num,
    rw ← sqrt_one,
    exact (sqrt_lt (add_nonneg (pow_two_nonneg p.1) (pow_two_nonneg p.2))).2 hp },
  { intros q hq,
    let h := real.Lp_add_two_le' (q.1 - p.1, q.2 - p.2) p 2 one_le_two,
    simp only [unit_disc, dist, mem_ball, mem_set_of_eq, max_lt_iff, sqrt_one, sub_add_cancel,
              ← sqrt_lt (add_nonneg (pow_two_nonneg q.1) (pow_two_nonneg q.2))] at hp hq h ⊢,
    calc sqrt (q.fst ^ 2 + q.snd ^ 2) ≤ sqrt ((q.1 - p.1)^2 + (q.2 - p.2)^2) + sqrt (p.1^2 + p.2^2) :
      by rw [sqrt_eq_rpow, ← abs_of_nonneg (pow_two_nonneg q.1), ← abs_of_nonneg (pow_two_nonneg q.2),
            ← abs_of_nonneg (pow_two_nonneg (q.1 - p.1)), ← abs_of_nonneg (pow_two_nonneg (q.2 - p.2)),
            ← abs_of_nonneg (pow_two_nonneg p.1), ← abs_of_nonneg (pow_two_nonneg p.2),
            abs_pow q.1 2, abs_pow q.2 2, abs_pow p.1 2, abs_pow p.2 2,
            abs_pow (q.1 - p.1) 2, abs_pow (q.2 - p.2) 2];
          exact_mod_cast h
    ... ≤ abs (q.1 - p.1) + abs (q.2 - p.2) + sqrt (p.1^2 + p.2^2) :
      add_le_add_right (by rw sqrt_le_iff; exact ⟨add_nonneg (abs_nonneg _) (abs_nonneg _),
        sqr_add_le_add_abs_sqr (q.1 - p.1) (q.2 - p.2)⟩) (sqrt (p.fst ^ 2 + p.snd ^ 2))
    ... < 1 : by linarith [add_lt_add hq.1 hq.2] },
end

-- Added by Ben: Once we have the fact that the unit disc is open, we know it is measurable.
lemma is_measurable_unit_disc : is_measurable unit_disc :=
is_open_unit_disc.is_measurable

--Andrew's work, set equality for the second step
lemma second_step : unit_disc = unit_disc_alt :=
begin
  unfold unit_disc, unfold unit_disc_alt,
  apply set.ext,
  intro point, split,
  { intro hp,
    have h₁ : (point.1)^2 + (point.2)^2 < 1 := hp,
    have h₂ : (point.2)^2 < 1 - (point.1)^2 := by linarith,
    exact ⟨sqr_lt_left h₂, lt_sqrt_of_sqr_lt h₂⟩ },
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

-- FTC-2 for the open set. **(PR #5733)**
-- Note: Measurability assumption will drop when we merge master
theorem integral_eq_sub_of_has_deriv_at'_of_mem_Ioo (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_at f (f' x) x)
  (hcont' : continuous_on f' (interval a b)) (hmeas' : ae_measurable f') :
  ∫ y in a..b, f' y = f b - f a :=
begin
  refine integral_eq_sub_of_has_deriv_right hcont _ hcont' hmeas',
  intros y hy',
  obtain (hy | hy) : y ∈ Ioo (min a b) (max a b) ∨ min a b = y ∧ y < max a b :=
    by simpa only [le_iff_lt_or_eq, or_and_distrib_right, mem_Ioo, mem_Ico] using hy',
  { exact (hderiv y hy).has_deriv_within_at },
  { have : tendsto f' (𝓝[Ioi y] y) (𝓝 (f' y)) :=
      tendsto.mono_left (by simpa only [← nhds_within_Icc_eq_nhds_within_Ici hy.2, interval, hy.1]
                          using hcont'.continuous_within_at (left_mem_Icc.mpr min_le_max))
        (nhds_within_mono y Ioi_subset_Ici_self),
    exact has_deriv_at_interval_left_endpoint_of_tendsto_deriv
      (λ x hx, (hderiv x hx).has_deriv_within_at.differentiable_within_at)
        ((hcont y (Ico_subset_Icc_self hy')).mono Ioo_subset_Icc_self) (Ioo_mem_nhds_within_Ioi hy')
          (by rwa tendsto_congr' (eventually_of_mem (Ioo_mem_nhds_within_Ioi hy') (λ x hx, (hderiv x hx).deriv))) },
  end

lemma step5_1 {x : ℝ} : deriv (λ y : ℝ, 1/2 * (arcsin y + y * sqrt (1 - y^2))) x = sqrt (1 - x^2) :=
begin
  have hx : x ∈ Ioo (-(1:ℝ)) 1 := sorry, -- must assume this to be true, leave alone for now
  have hlt : 0 < 1 - x^2,
    { rw mem_Ioo at hx,
      nlinarith}, -- (SOLVED BY JAMES)
  have h1 : differentiable_at ℝ (λ y:ℝ, 1 - y ^ 2) x,
      { simp only [differentiable_at_id', differentiable_at.pow, differentiable_at_const_sub_iff] },
   -- show `differentiable_at ℝ (λ y, 1 - y ^ 2) x` (SOLVED BY JAMES)
  have h2 : differentiable_at ℝ (λ y:ℝ, sqrt(1 - y ^ 2)) x := h1.sqrt hlt.ne.symm,
  have h3 : differentiable_at ℝ (λ y:ℝ, y * sqrt(1 - y ^ 2)) x := differentiable_at.mul differentiable_at_id' h2,
    -- show `differentiable_at ℝ (λ y, y * sqrt(1 - y ^ 2)) x` (SOLVED BY JAMES)
  have h4 : differentiable_at ℝ (λ y:ℝ, arcsin y + y * sqrt(1 - y ^ 2)) x,
      { apply differentiable_at.add _ h3,
        rw differentiable_at_arcsin,
        rw mem_Ioo at hx,
        cases hx with hnx hpx,
        split,
        { linarith },
        { linarith } }, -- show `differentiable_at ℝ (λ y, arcsin y + y * sqrt(1 - y ^ 2)) x` (SOLVED BY JAMES)
  rw [deriv_const_mul _ h4, deriv_add (differentiable_at_arcsin.mpr ⟨hx.1.ne.symm, hx.2.ne⟩) h3,
      deriv_mul differentiable_at_id' h2, deriv_sqrt h1 hlt.ne.symm, deriv_arcsin],
  simp only [one_mul, deriv_id'', differentiable_at_const, mul_one, zero_sub, deriv_sub,
    differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'', deriv_const', pow_one,
    differentiable_at.pow, nat.cast_one, neg_div],
  rw mul_div_mul_left;
  field_simp [add_left_comm, ← pow_two, tactic.ring.add_neg_eq_sub, div_sqrt hlt.le],
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


-- # The Grand Finale!!!!!

lemma s_eq : (λ x y, set.indicator  unit_disc_alt                       (λ p, 1) (x, y))
            = λ x y, set.indicator (Ioo (-sqrt (1-x^2)) (sqrt (1-x^2))) (λ t, 1)     y  :=
by ring

example [normed_group (ℝ → ℝ)]: (volume unit_disc).to_real = pi :=
begin
  have h1 := integral_indicator_const (1:ℝ) is_measurable_unit_disc,
  rw [algebra.id.smul_eq_mul, mul_one] at h1,
  rw [← h1, second_step],
  let χ₁ := set.indicator unit_disc_alt (λ p, (1:ℝ)),
  let χ₂ := λ x, set.indicator (Ioo (-sqrt (1-x^2)) (sqrt (1-x^2))) (λ t, (1:ℝ)),
  have χ_eq : (λ x y, χ₁ (x, y)) = λ y, χ₂ y := by ring,
  ring at χ_eq,
  simp only [← χ₁, χ_eq],
  have hintg : integrable χ₂ _ := sorry,
  have := integral_prod χ₂ hintg,
  --have hintg : integrable (set.indicator s (λ (x : ℝ), (1:ℝ))) (volume) := sorry,
  --convert integral_prod (set.indicator s (λ (x : ℝ), (1:ℝ))) hintg,
  have hmeas : is_measurable {x : ℝ | x ∈ Ioo (-sqrt (1-x^2)) (sqrt (1-x^2))} := sorry,
  have := integral_indicator_const (1:ℝ) hmeas,

  sorry,
end


#check volume_Ioo -- for step 4(ii)

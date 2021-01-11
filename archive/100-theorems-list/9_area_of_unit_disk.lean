import measure_theory.interval_integral
import data.real.sqrt
import measure_theory.measure_space
import topology.metric_space.basic

open_locale real

open set interval_integral metric real

--Def'n and alternate def'n of the unit disc
def unit_disc := {point : ℝ × ℝ | (point.1)^2 + (point.2)^2 < 1 }

def unit_disc_alt := {point : ℝ × ℝ | -1 * sqrt (1 - (point.1)^2) < point.2 ∧
                                       point.2 < sqrt (1 - (point.1)^2)}


--Andrew's work (unfinished), lemma helpful for first step
lemma unit_disc_open : is_open unit_disc :=
begin
  unfold unit_disc,
  rw is_open_iff,
  intros p p_in,
  let ε := (1/2) * (1 - sqrt ((p.1) ^ 2 + (p.2) ^ 2) ),
  use ε, split,
  { norm_num,
    rw ← sqrt_one,
    exact (sqrt_lt (add_nonneg (pow_two_nonneg p.1) (pow_two_nonneg p.2))).2 p_in, },

  { intros q hq,
    simp * at *,
    have ε_def : ε = 1 / 2 * (1 - sqrt (p.fst ^ 2 + p.snd ^ 2)) := rfl,
    rw ε_def at hq,
    sorry,
     },
end




--Andrew's work : lemma for set eq'ty in second step
lemma lt_sqrt_of_sqr_lt  {a b : ℝ} : a^2 < b → a < sqrt b :=
begin
  intro h,
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
lemma opposite_sqrt_lt_of_sqr_lt {a b : ℝ} : a^2 < b → (-1) * sqrt b < a :=
begin
  intro h,
  have hb : 0 ≤ b := by linarith [pow_two_nonneg a],
  by_contradiction hyp,
  push_neg at hyp,
  by_cases ha : a = 0,
  {by_cases hb' : b = 0,
   {  rw [ha, hb'] at h, linarith },
   {  rw ← ne.def at hb',
      replace hb' := ne.symm hb',
      replace hb' : 0 < b := lt_iff_le_and_ne.2 ⟨hb, hb'⟩,
      have hsqrtb := sqrt_nonneg b,
      have : (-1) * sqrt b ≤ 0 := by linarith,
      rw ha at hyp,
      replace hyp : (-1) * sqrt b = 0 := by linarith,
      replace hyp :  sqrt b = 0 := by linarith,
      replace hyp : b = 0 := (sqrt_eq_zero hb).1 hyp,
      linarith,  }  },
  {replace ha : a ≠ 0 := by assumption,
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
      linarith,  },
    { push_neg at ha',
      replace ha : 0 ≠ a := ne.symm ha,
      have a_pos : 0 < a := lt_iff_le_and_ne.2 ⟨ha', ha⟩,
      have hsqrtb := sqrt_nonneg b,
      have : (-1) * sqrt b ≤ 0 := by linarith,
      linarith,  },  },
end

--Andrew's work : final lemma for set eq'ty in second step
lemma lt_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) : x < sqrt y ↔ x ^ 2 < y :=
by rw [mul_self_lt_mul_self_iff hx (le_of_lt (sqrt_pos.2 hy)), pow_two, mul_self_sqrt (le_of_lt hy)]



--Andrew's work, set equality for the second step
lemma second_step : unit_disc  = unit_disc_alt :=
begin
  unfold unit_disc, unfold unit_disc_alt,
  apply set.ext,
  intro point, split,

  { intro hp,
    have h₁ : (point.1)^2 + (point.2)^2 < 1 := hp,
    have h₂ : (point.2)^2 < 1 - (point.1)^2 := by linarith,
    exact ⟨opposite_sqrt_lt_of_sqr_lt h₂, lt_sqrt_of_sqr_lt h₂⟩, },

  { intro hp,
    cases hp with hp₁ hp₂,
    have h₁ : 0 ≤ sqrt (1 - point.fst ^ 2) := sqrt_nonneg (1 - point.fst ^ 2),
    have term_pos : (1 - point.fst ^ 2) > 0,
      {by_contradiction hyp,
      push_neg at hyp,
      have := sqrt_eq_zero_of_nonpos hyp,
      rw this at hp₁, rw this at hp₂,
      simp at hp₁,
      linarith,},
    by_cases hyp : 0 ≤ point.snd,

    { have h₁ := (lt_sqrt hyp (by linarith)).1 hp₂,
      have h₂ : (point.1)^2 + (point.2)^2 < 1 := by linarith,
      exact h₂, },

    { push_neg at hyp,
      have h₁ :  - point.snd < sqrt (1 - point.fst ^ 2) := by linarith,
      have neg_point_pos : 0 < - point.snd := by linarith,
      have h₂ := (lt_sqrt (le_of_lt neg_point_pos) (by linarith)).1 h₁,
      rw neg_square point.snd at h₂,
      have h₃ : (point.1)^2 + (point.2)^2 < 1 := by linarith,
      exact h₃, }, },
end




variables {β E F : Type*} [measurable_space E] [normed_group E] {f : ℝ → E}
  {c ca cb : E} {a b z : ℝ} {u v ua ub va vb : β → ℝ} {f' : ℝ → E} [normed_space ℝ E]
  [borel_space E] [complete_space E] [topological_space.second_countable_topology E]

theorem FTC_but_with_open_set (hcont : continuous_on f (interval a b))
  (hderiv : ∀ x ∈ Ioo (min a b) (max a b), has_deriv_at f (f' x) x)
  (hcont' : continuous_on f' (interval a b)) (hmeas' : ae_measurable f') :
  ∫ y in a..b, f' y = f b - f a :=
  begin
    sorry
  end

---

lemma aux_sqrt_lemma (x : ℝ) (h : 0 < x) : x / real.sqrt x = real.sqrt x :=
begin
  rw div_eq_iff,
  exact (real.mul_self_sqrt (le_of_lt h)).symm,
  { intro Hx,
    rw real.sqrt_eq_zero' at Hx,
    linarith }
end

example : 4 * ∫ (x : ℝ) in (0:ℝ)..1, real.sqrt(1 - x^2) = π :=
begin
  have derivH : deriv (λ x : ℝ, 1/2 * (real.arcsin x + x * real.sqrt(1 - x^2) ) ) = λ x, real.sqrt(1 - x^2),
  { ext,
    rw deriv_const_mul,
    rw deriv_add,
    simp only [one_div, real.deriv_arcsin],
    rw deriv_mul,
    simp only [one_mul, deriv_id''],
    rw deriv_sqrt,
    simp only [differentiable_at_const, mul_one, zero_sub, deriv_sub, differentiable_at_id', deriv_pow'', nat.cast_bit0, deriv_id'',
  deriv_const', pow_one, differentiable_at.pow, nat.cast_one],
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

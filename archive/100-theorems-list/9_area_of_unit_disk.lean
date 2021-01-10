import measure_theory.interval_integral
open_locale real

open set interval_integral

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

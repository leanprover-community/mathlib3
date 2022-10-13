import probability.gaussian

open_locale ennreal
open_locale nnreal ennreal probability_theory measure_theory real

open measure_theory filter real

namespace measure_theory

open real


open probability_theory measure


variables {μ : measure ℝ} {m s : ℝ}

/-
namespace measure_theory

open filter measure probability_theory real
variables {μ : measure ℝ} {s m : ℝ} {E : Type u_1} {F : Type u_2} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E] [normed_add_comm_group F] [normed_space ℝ F]
-/

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]

/-- A real-valued random variable is a Gaussian if its push-forward measure is a Gaussian measure
on ℝ. -/

variables {f g : Ω → ℝ} {m₁ s₁ m₂ s₂ : ℝ}






lemma gaussian_rv_add (hf : gaussian_rv f m₁ s₁) (hg : gaussian_rv g m₂ s₂)
  (hfmeas : measurable f) (hgmeas : measurable g) (hfg : indep_fun f g) :
  gaussian_rv (f + g) (m₁ + m₂) (sqrt (s₁^2 + s₂^2)) :=
begin
  unfold gaussian_rv at *,
  unfold real_gaussian at *,
  ---split_ifs,
  by_cases h1: s₁=0,
  {by_cases h2: s₂=0,
  {
    rw [h1, h2],
    simp,
    simp [h1] at hf,
    simp [h2] at hg,
    rw pushmea_of_func_plus_const_func f g m₁ hfmeas hgmeas hf,
    have h_const_mea : measurable (λ (x : Ω), m₁),
    {measurability,},
    {
      rw pushmea_of_func_plus_const_func g (λ (x : Ω), m₁) m₂ hgmeas h_const_mea hg,
      simp,
      sorry
    },

  },
  {

      simp [(sq_pos_iff s₂).mpr h2, sq_nonneg s₁, lt_add_of_le_of_pos, ne_of_gt],
      simp [h1, h2] at hf hg ⊢,
      rw pushmea_of_func_plus_const_func f g m₁ hfmeas hgmeas hf,
      unfold gaussian_density,
      /-let h : ℝ → ℝ := λ x, x + m₁,
      have h_f_plus_const_eq_comb : (f + g) = h ∘ g,
      {
        ext x,
        simp [h],
      },
      -- rw ← measure.map_map h_hmeas hfmeas,-/


      ---WE ARE AIMING TO SOLVE THIS BRACKET
      ---WE ARE AIMING TO SOLVE THIS BRACKET
      ---WE ARE AIMING TO SOLVE THIS BRACKET
      ---WE ARE AIMING TO SOLVE THIS BRACKET
      ---WE ARE AIMING TO SOLVE THIS BRACKET
      sorry,

      },
  },
  {by_cases h2: s₂=0,
  {sorry},
  {sorry},

  },



end

lemma mgf_gaussian_rv  (hf : gaussian_rv f m s) (hfmeas : measurable f) (t : ℝ) :
  mgf f volume t = exp (m * t + s^2 * t^2 / 2) :=
begin
  unfold mgf,
  unfold gaussian_rv real_gaussian at hf,
  by_cases hs : s = 0;
  {simp [hs] at *,
  sorry,
  },
end

end measure_theory

/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import measure_theory.regular
import topology.semicontinuous
import measure_theory.bochner_integration
import topology.instances.ereal

open_locale ennreal nnreal

open measure_theory measure_theory.measure

variables {α : Type*} [topological_space α] [measurable_space α] [borel_space α] {μ : measure α}
  [weakly_regular μ]

/-- Given an integrable function `f`, there exists a lower semicontinuous function `g ≥ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_le_lower_semicontinuous
  (f : α → ℝ≥0∞) (hf : measurable f) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, f x ≤ g x) ∧ lower_semicontinuous g ∧ (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, le_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere. -/
lemma exists_integrable_pos_of_sigma_finite [sigma_finite μ] (ε : ℝ≥0) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ measurable g ∧ (∫⁻ x, g x ∂μ ≤ ε) :=
begin
  set δ := ε / 2 with hδ,
  have δpos : 0 < δ := nnreal.half_pos εpos,
  let a : ℝ≥0 := 2⁻¹,
  have a_pos : 0 < a, by simp [a],
  have a_lt_one : a < 1 := nnreal.two_inv_lt_one,
  set s := spanning_sets μ with hs,
  have : ∀ n, μ (s n) * ↑(δ * a ^ n / max 1 (μ (s n)).to_nnreal) ≤ ↑δ * ↑a ^ n,
  { assume n,

  }

end

  let g := λ x, ∑' n, (set.indicator (s n) (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x),
  have A : summable (λ (n : ℕ), δ * a^n) := (nnreal.summable_geometric a_lt_one).mul_left _,
  have B : summable (λ (n : ℕ), δ * a^n / (max 1 (μ (s n)).to_nnreal)),
  { apply nnreal.summable_of_le (λ n, _) A,
    rw nnreal.div_le_iff (ne_of_gt (zero_lt_one.trans_le (le_max_left _ _))),
    conv_lhs { rw ← mul_one (δ * a^n) },
    exact mul_le_mul (le_refl _) (le_max_left _ _) bot_le bot_le },
  have C : ∀ x, summable (λ n, set.indicator (s n) (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x),
  { assume x,
    apply nnreal.summable_of_le (λ n, _) B,
    simp only [set.indicator],
    split_ifs,
    { exact le_refl _ },
    { exact bot_le } },
  have M : ∀ n, measurable (set.indicator (s n) (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal))) :=
    λ n, measurable_const.indicator (measurable_spanning_sets μ n),
  refine ⟨g, λ x, _, measurable.nnreal_tsum M, _⟩,
  { have : x ∈ (⋃ n, s n), by { rw [hs, Union_spanning_sets], exact set.mem_univ _ },
    rcases set.mem_Union.1 this with ⟨n, hn⟩,
    apply nnreal.tsum_pos (C x) n,
    simp only [hn, set.indicator_of_mem],
    exact nnreal.div_pos (mul_pos δpos (pow_pos a_pos _))
      (zero_lt_one.trans_le (le_max_left _ _)) },
  { calc ∫⁻ (x : α), (g x) ∂μ
    = ∫⁻ x, ∑' n,
        (((s n).indicator (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x : ℝ≥0) : ℝ≥0∞) ∂μ :
      by { apply lintegral_congr (λ x, _), simp_rw [g, ennreal.coe_tsum (C x)] }
    ... = ∑' n, ∫⁻ x,
        (((s n).indicator (λ x, δ * a^n / (max 1 (μ (s n)).to_nnreal)) x : ℝ≥0) : ℝ≥0∞) ∂μ :
      lintegral_tsum (λ n, (M n).ennreal_coe)
    ... = ∑' n, μ (s n) * (δ * a^n / (max 1 (μ (s n)).to_nnreal) : ℝ≥0) :
      begin
        congr' 1,
        ext1 n,
        simp only [measurable_spanning_sets μ n, lintegral_const, measurable_set.univ, mul_comm,
          lintegral_indicator, inv_pow', restrict_apply, set.univ_inter, ennreal.coe_indicator],
      end
    ... ≤ ∑' n, δ * a ^ n :
      begin
        apply ennreal.tsum_le_tsum (λ n, _),

      end
    ... ≤ ε : sorry

 --   simp [g],
 --   have Z := λ x, ennreal.coe_tsum (C x),

  }
end

#exit

/-- Given an integrable function `f` in a sigma-finite space, there exists a lower semicontinuous
function `g > f` with integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_lt_lower_semicontinuous [sigma_finite μ]
  (f : α → ℝ≥0) (hf : measurable f) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, (f x : ℝ≥0∞) < g x) ∧ lower_semicontinuous g ∧
    (∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ + ε) :=
begin
  by_cases int_f : ∫⁻ x, f x ∂μ = ∞,
  { refine ⟨λ x, ∞, λ x, ennreal.coe_lt_top, lower_semicontinuous_const, by simp [int_f]⟩ },
  sorry
end


/-- Given an integrable function `f`, there exists an upper semicontinuous function `g ≤ f` with
integral arbitrarily close to that of `f`. -/
lemma ennreal.exists_upper_semicontinuous_le
  (f : α → ℝ≥0∞) (hf : measurable f) (int_f : ∫⁻ x, f x ∂μ < ∞) (ε : ℝ≥0∞) (εpos : 0 < ε) :
  ∃ g : α → ℝ≥0∞, (∀ x, g x ≤ f x) ∧ lower_semicontinuous g ∧ (∫⁻ x, f x ∂μ ≤ ∫⁻ x, g x ∂μ + ε) :=
begin
  sorry
end

lemma real.exists_le_lower_semicontinuous
  (f : α → ℝ) (hf : integrable f μ) (ε : ℝ) (εpos : 0 < ε) :
  ∃ g : α → ereal, (∀ x, (f x : ereal) ≤ g x) ∧ lower_semicontinuous g ∧
  (∀ᵐ x ∂ μ, g x < ⊤) ∧
  (∫ x, ereal.to_real (g x) ∂μ ≤ ∫ x, f x ∂μ + ε) :=
begin
  sorry
end



end measure_theory

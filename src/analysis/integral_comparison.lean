import measure_theory.integral_eq_improper

open measure_theory set

open_locale nnreal ennreal big_operators

variables {f : ℝ → ℝ} (hpos : 0 ≤ᵐ[volume.restrict (Ici 0)] f) (hmono : ∀ x y, 0 ≤ x → 0 ≤ y → x ≤ y → f y ≤ f x)

lemma integral_le (n : ℕ) : ∫ (x : ℝ) in n..(n+1), f x ≤ f n :=
calc ∫ (x : ℝ) in n..(n+1), f x
      ≤ ∫ (x : ℝ) in n..(n+1), f n : by {exact interval_integral.integral_mono sorry sorry (λ x, _) }
  ... = f n : sorry

theorem goal : summable (λ (n : ℕ), f n) ↔ integrable_on f (Ici 0) :=
begin
  sorry
end

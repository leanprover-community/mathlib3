import data.real.irrational
import analysis.special_functions.pow

open real

lemma foo {x : ℝ} (h : 0 ≤ x) :
  sqrt x ^ (2 : ℝ) = x :=
by exact_mod_cast sq_sqrt h

theorem algebra_others_exirrpowirrrat :
  ∃ a b, irrational a ∧ irrational b ∧ ¬ irrational (a^b) :=
begin
  by_cases irrational (sqrt 2^sqrt 2),
  { have h': ¬ irrational ((sqrt 2^sqrt 2)^sqrt 2),
    { rw ←real.rpow_mul (real.sqrt_nonneg 2),
      simp only [foo, irrational_iff_ne_rational, mul_self_sqrt, zero_le_bit0, zero_le_one,
        not_forall, not_not],
      refine ⟨2, 1, _⟩,
      rw [int.cast_bit0, int.cast_one, div_one] },
    exact ⟨(sqrt 2^sqrt 2), sqrt 2, h, irrational_sqrt_two, h'⟩, },
  { exact ⟨sqrt 2, sqrt 2, irrational_sqrt_two, irrational_sqrt_two, h⟩, }
end

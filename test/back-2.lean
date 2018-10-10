import data.nat.prime
import measure_theory.lebesgue_measure
import data.zmod.quadratic_reciprocity
import ring_theory.polynomial
import tactic.back

set_option profiler true

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  back? with _,
end

lemma div_dvd_of_dvd {a b : ℕ} (h : b ∣ a) : (a / b) ∣ a :=
-- The mathlib proof is: `⟨b, (nat.div_mul_cancel h).symm⟩`
by back? [-nat.div_dvd_of_dvd] with _

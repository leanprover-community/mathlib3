import number_theory.multiplicity
import number_theory.cyclotomic.basic
import ring_theory.polynomial.cyclotomic.eval

open polynomial

lemma cyclotomic_mul_of_div_eq {p n : ℕ} {hp : prime p} (hnp : p ∣ n) :
  cyclotomic (p * n) ℂ = (cyclotomic n ℂ).comp (X ^ p) := sorry

lemma cyclotomic_mul_of_not_div_eq {p n : ℕ} {hp : prime p} (hnp : ¬ p ∣ n) :
  cyclotomic (p * n) ℂ = (cyclotomic n ℂ).comp (X ^ p) / (cyclotomic n ℂ) := sorry


-- how do I lift a polynomial to a mv_polynomial for homogenisations

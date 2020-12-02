import number_theory.bernoulli
import data.nat.basic
import analysis.complex.roots_of_unity
import data.complex.exponential

noncomputable theory
def bernoulli_polynomial (n : ℕ) : ℂ → ℂ := λ X, ∑' i : fin (n+1), (bernoulli n)*(nat.choose n i)*(X^(n-i))

lemma one_sub_eq_neg : ∀ n : ℕ, ∀ X : ℂ, bernoulli_polynomial n (1 - X) = (-1)^n * bernoulli_polynomial n X :=
begin
  sorry
end

lemma exp_bernoulli : ∀ t : ℕ, ∀ X : ℕ, ∑' i : ℕ, (bernoulli_polynomial i X) * t^i / (nat.factorial i) = (t * real.exp (X * t))/(real.exp t - 1) :=
begin
  sorry
end

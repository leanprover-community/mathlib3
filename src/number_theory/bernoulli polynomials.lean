import number_theory.bernoulli
import data.nat.basic
import analysis.complex.roots_of_unity
import data.complex.exponential
import topology.algebra.infinite_sum
import data.real.ereal

noncomputable theory
open_locale big_operators

instance : has_mul ereal :=
{
  mul := begin
          rintros a b,
          rcases a,
          exact ⊤,
          cases a,
          exact ⊥,
          cases b,
          exact ⊤,
          cases b,
          exact ⊥,
          exact (a*b : ℝ),
          end
}

instance : has_div ereal :=
{
  div := begin
          rintros a b,
          rcases b,
          exact 0,
          rcases b,
          exact 0,
          by_cases b = 0,
          {
            by_cases 0 ≤ a,
            by_cases a = 0,
            exact 0,
            exact ⊤,
            exact ⊥,
          },
          cases a,
          exact ⊤,
          cases a,
          exact ⊥,
          exact (a/b : ℝ),
          end
}

instance : add_comm_monoid ereal :=
begin
  exact with_top.add_comm_monoid,
end

instance A : ordered_add_comm_monoid ereal :=
begin
  exact with_top.ordered_add_comm_monoid,
end

instance B : order_bot ereal :=
begin
  apply_instance,
end

instance : canonically_ordered_add_monoid ereal :=
begin
  fconstructor,
  use has_add.add,
  exact add_assoc,
  exact 0,
  simp,
  simp,
  exact add_comm,
  exact order_bot.le,
  exact le_refl,
  {
    rintros a b c,
    refine le_trans,
  },
  {
    rintros a b,
    exact le_antisymm,
  },
  sorry,
  sorry,
  use has_bot.bot,
  simp,
  sorry,
end

class ber (bernoulli_polynomial : ℕ → ℕ → ℚ) :=
(ber :  ∀ t : ℕ, ∀ X : ℕ, ( ∑' i : ℕ, ((bernoulli_polynomial i X) * t^i / (nat.factorial i) ) = (t * real.exp (X * t)/(real.exp t - 1) ) ) )

namespace bernoulli_polynomial

variables (B : ℕ → ℕ → ℚ) [ber B]
--def bernoulli_polynomial (n : ℕ) : ℚ → ℚ := λ X, ∑' i : fin (n+1), (bernoulli n)*(nat.choose n i)*(X^(n-i))
--def bernoulli_polynomial (n : ℕ) : ℚ → ℚ := B n

lemma exp_bernoulli_poly : ∀ t : ℚ, ∀ X : ℚ, (∑' i : ℕ, (B i X) * t^i / (nat.factorial i)) = (t * real.exp (X * t)/(real.exp t - 1) ) :=
ber.ber

lemma exp_bernoulli : ∀ t : ℚ, (∑' i : ℕ, ((bernoulli i) : ℚ) * t^i / (nat.factorial i)) = (t/(real.exp t - 1) ) :=
sorry

lemma ber_poly_zero : ∀ X, (bernoulli_polynomial 0 X) = 1 :=
begin
  sorry
end

lemma ber_poly_one : ∀ X, (bernoulli_polynomial 1 X) = X - 1/2 :=
begin
  sorry
end

lemma bernoulli_polynomial_eq_sum (n : ℕ) (X : ℚ) : B n X = ∑' i : fin (n+1), (bernoulli n)*(nat.choose n i)*(X^(n-i)) :=
begin
  sorry
end

lemma bernoulli_polynomial_eq_sum (n : ℕ) (X Y : ℚ) : B n (X + Y) = ∑' i : fin (n+1), (nat.choose n i)* (bernoulli_polynomial i Y) * (X^(n-i)) :=
begin
  sorry
end

lemma bernoulli_polynomial_recursive (n : ℕ) (X : ℚ) : B n X = X^n - 1/(n + 1) * (∑' i : fin n, (nat.choose (n + 1) i)* (bernoulli_polynomial i X) ) :=
begin
  sorry
end

lemma one_sub_eq_neg : ∀ n : ℕ, ∀ X : ℚ, (B n) ((1: ℚ) - X) = (-1)^n * B n X :=
begin
  rintros n X,
  have h := exp_bernoulli_poly B 1 (1 - X),
  simp at h,
  have h' := exp_bernoulli_poly B (-1) X,
  simp at h',
  have f : real.exp (1 - X) / (real.exp 1 - 1) = -real.exp (-X) / (real.exp (-1) - 1),
  sorry,
  rw f at h,
  rw <-h' at h,
  rw <-sub_eq_zero_iff_eq at h,
  rw <-tsum_sub at h,
  let g : ℕ → ℚ := λ b, (B b (1 - X) / ↑(b.factorial) - B b X * (-1) ^ b / ↑(b.factorial)),
  have g' : (∑' b, g b) = 0,
  exact h,
  have g'' : summable g,
  sorry,
  have f' := @tsum_eq_zero_iff _ _ _ _ _ g,
  sorry
end

end bernoulli_polynomial

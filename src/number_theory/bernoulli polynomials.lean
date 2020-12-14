import number_theory.bernoulli
import data.nat.basic
import analysis.complex.roots_of_unity
import data.complex.exponential
import topology.algebra.infinite_sum
import data.real.ereal
import data.finset.basic
import tactic.linarith
import algebra.big_operators.intervals
import data.set.intervals.basic

noncomputable theory
open_locale big_operators

open nat

def delta_function (i j : ℕ) : ℕ := if i = j then 1 else 0

def bernoulli_neg : ℕ → ℚ :=
well_founded.fix nat.lt_wf
  (λ n bernoulli_neg, (delta_function n 0) - ∑ k : fin n, (n.choose k) * bernoulli_neg k k.2 / (n + 1 - k))

lemma bernoulli_neg_def' (n : ℕ) :
  bernoulli_neg n = (delta_function n 0) - ∑ k : fin n, (n.choose k) * (bernoulli_neg k) / (n + 1 - k) :=
well_founded.fix_eq _ _ _

lemma bernoulli_neg_def (n : ℕ) :
  bernoulli_neg n = (delta_function n 0) - ∑ k in finset.range n, (n.choose k) * (bernoulli_neg k) / (n + 1 - k) :=
by { rw [bernoulli_neg_def', ← fin.sum_univ_eq_sum_range], refl }

@[simp] lemma bernoulli_neg_zero  : bernoulli_neg 0 = 1   := rfl

@[simp] lemma bernoulli_neg_one   : bernoulli_neg 1 = -1/2 :=
begin
  rw [bernoulli_neg_def],
  try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] }, simp, norm_num1,
  rw delta_function, simp,
end

lemma choose_succ_div_eq (n k : ℕ) (h : k ≤ n) : (n.choose k : ℚ) / (n + 1 - k) = n.succ.choose k / (n + 1) :=
begin
  sorry
end

@[simp] lemma sum_bernoulli_neg (n : ℕ) ( h : 1 ≤ n ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli_neg k = 0 :=
begin
  induction n with n ih, { simp },
  rw [finset.sum_range_succ],
  rw [nat.choose_succ_self_right],
  rw [bernoulli_neg_def, mul_sub, sub_add_eq_add_sub, sub_eq_iff_eq_add],
  rw [finset.mul_sum, finset.sum_congr rfl],
  have f : delta_function n 0 = 0,
  sorry,
  rw f, simp,
  intros k hk, rw finset.mem_range at hk,
  rw [mul_div_right_comm, ← mul_assoc],
  congr' 1,
  rw [← mul_div_assoc, eq_div_iff], norm_cast,
  simp_rw [mul_comm, choose_mul_succ_eq n k], norm_num, left, sorry,
  { contrapose! hk with H, rw sub_eq_zero at H, norm_cast at H, linarith }
end

def bernoulli_poly (n : ℕ) : ℚ → ℚ := λ X, ∑ i in finset.range (n+1),
  (bernoulli_neg i)*(nat.choose n i)*(X^(n-i))

namespace bernoulli_poly

lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1),
  (bernoulli_neg (n - i))*(nat.choose n i)*(X^i) :=
begin
sorry,
end

--lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1), (bernoulli_neg i)*(nat.choose n i)*(X^(n-i)) :=
--by { rw [bernoulli_poly, ← fin.sum_univ_eq_sum_range] }

@[simp] lemma bernoulli_poly_zero (X : ℚ) : bernoulli_poly 0 X = 1 := rfl

@[simp] lemma bernoulli_poly_zero' (n : ℕ) : bernoulli_poly n 0 = bernoulli_neg n :=
begin
  sorry,
end

@[simp] lemma bernoulli_poly_one (X : ℚ) : bernoulli_poly 1 X = X -1/2 :=
begin
  rw [bernoulli_poly_def],
  try { rw [finset.sum_range_succ] }, try { rw [nat.choose_succ_succ] },
  simp, norm_num1, ring,
end

lemma choose_mul (n k s : ℕ) (hn : k ≤ n) (hs : s ≤ k) : (n.choose k : ℚ) * k.choose s = n.choose s * (n - s).choose (k - s) :=
sorry

namespace finset

lemma dependent_double_sum {M : Type*} [add_comm_monoid M]
  (a b : ℕ) (f : ℕ → ℕ → M) :
  ∑ i in finset.Ico a b, ∑ j in finset.Ico i b, f i j =
  ∑ j in finset.Ico a b, ∑ i in finset.Ico a (j+1), f i j :=
begin
  rw ← @@finset.sum_sigma _ _ (λ i, finset.Ico i b) (λ x, f x.1 x.2),
  rw ← @@finset.sum_sigma _ _ (λ j, finset.Ico a (j+1)) (λ x, f x.2 x.1),
  refine finset.sum_bij'
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _ (λ _ _, rfl)
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _
    (by rintro ⟨⟩ _; refl) (by rintro ⟨⟩ _; refl);
  simp only [finset.Ico.mem, sigma.forall, finset.mem_sigma];
  rintros a b ⟨⟨h₁,h₂⟩, ⟨h₃, h₄⟩⟩; refine ⟨⟨_, _⟩, ⟨_, _⟩⟩; linarith
end

end finset

@[simp] theorem sum_bernoulli_poly (n : ℕ) (X : ℚ) :
  ∑ k in finset.range (n + 1), ((n + 1).choose k : ℚ) * bernoulli_poly k X = (n + 1) * X^n :=
begin
  cases n, simp,
  simp_rw [bernoulli_poly_def],
  simp_rw [finset.mul_sum],
  suffices f :
  ∑ (s : ℕ) in finset.range (n.succ + 1),
    ((n.succ + 1).choose s : ℚ) *  X ^ s *
      ∑ (y : ℕ) in finset.range (n.succ + 1 - s),
        ((n.succ + 1 - s).choose y : ℚ) * bernoulli_neg y =
          (n.succ + 1) * X ^ (n.succ),
  {
    simp_rw [finset.range_eq_Ico],
    rw <-finset.dependent_double_sum,
    simp_rw [finset.range_eq_Ico] at f,
    conv_lhs
    {
      congr,
      skip,
      funext,
      rw [finset.sum_Ico_eq_sum_range, finset.range_eq_Ico],
    },
    rw <-f,
    rw <-sub_eq_zero_iff_eq,
    rw <-finset.sum_sub_distrib,
    rw finset.sum_eq_zero,
    rintros x hx,
    rw mul_comm,
    rw finset.sum_mul,
    rw <-finset.sum_sub_distrib,
    rw finset.sum_eq_zero,
    rintros y hy,
    rw sub_eq_zero_iff_eq,
    simp, rw mul_comm, rw mul_comm ((n.succ + 1 - x).choose y : ℚ) (bernoulli_neg y),
    rw mul_assoc, rw mul_assoc, rw mul_assoc,
    rw mul_eq_mul_left_iff,
    left, rw mul_comm, rw mul_comm ((n.succ + 1 - x).choose y : ℚ) (((n.succ + 1).choose x : ℚ) * X^x),
    rw mul_comm ((n.succ + 1).choose x : ℚ) (X^x),
    rw mul_assoc, rw mul_assoc,
    rw mul_eq_mul_left_iff,
    left,
    rw choose_mul, simp,
    {
      simp at hx, simp at hy,
      have h:= nat.add_lt_add_left hy x,
      have h' : x + (n.succ + 1 - x) = n.succ + 1,
      rw nat.add_sub_cancel',
      exact le_of_lt hx,
      rw h' at h,
      exact le_of_lt h,
    },
    simp,
  },
  rw [finset.sum_range_succ], simp,
  rw [finset.sum_range_succ], simp,
  have g : ↑((n.succ + 1).choose n) * X ^ n * ∑ (y : ℕ) in finset.range (n.succ + 1 - n),
    ↑((n.succ + 1 - n).choose y) * bernoulli_neg y = 0,
  {
    simp,
    right,
    have h : n.succ + 1 - n = 2,
    rw succ_add, rw succ_sub, simp, simp,
    rw h, simp,
  },
  rw g, simp,
  rw [finset.sum_eq_zero],
  rintros x hx,
  rw sum_bernoulli_neg, simp,
  simp at hx,
  rw succ_add, rw succ_sub,
  rw succ_le_succ_iff,
  simp, simp, apply le_succ_of_le,
  exact le_of_lt hx,
end

lemma exp_bernoulli_neg : ∀ t : ℚ, ((∑' i : ℕ, ((bernoulli i) : ℚ) * t^i / (nat.factorial i)) : ℝ) * (real.exp t - 1) = t :=
sorry

lemma exp_bernoulli_poly : ∀ t : ℚ, ∀ X : ℚ, (∑' i : ℕ, (bernoulli_poly i X) * t^i / (nat.factorial i) : ℝ) * (real.exp t - 1) = t * real.exp (X * t) :=
sorry

lemma one_sub_eq_neg : ∀ n : ℕ, ∀ X : ℚ, (bernoulli_poly n) ((1: ℚ) - X) = (-1)^n * bernoulli_poly n X :=
begin
  rintros n X,
  have h := exp_bernoulli_poly 1 (1 - X),
  simp at h,
  have h' := exp_bernoulli_poly (-1) X,
  simp at h',
  have f : real.exp (1 - X) = (real.exp 1 - 1) * -real.exp (-X) / (real.exp (-1) - 1),
  sorry,
  rw f at h,
  rw <-h' at h,
  rw <-sub_eq_zero_iff_eq at h,
  rw mul_comm at h,
--  rw <-tsum_sub at h,
--  let g : ℕ → ℚ := λ b, (bernoulli_poly b (1 - X) / ↑(b.factorial) - bernoulli_poly b X * (-1) ^ b / ↑(b.factorial)),
--  have g' : (∑' b, g b) = 0,
--  exact h,
--  have g'' : summable g,
  sorry,
--  have f' := @tsum_eq_zero_iff _ _ _ _ _ g,
--  sorry
end

end bernoulli_poly

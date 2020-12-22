import number_theory.bernoulli
import data.nat.basic
import analysis.complex.roots_of_unity
import topology.algebra.infinite_sum
import data.real.ereal
import data.finset.basic
import tactic.linarith
import algebra.big_operators.intervals
import data.set.intervals.basic
import ring_theory.power_series

noncomputable theory
open_locale big_operators

open nat

def delta_function (i j : ℕ) : ℕ := if i = j then 1 else 0

lemma delta_function_zero (n : ℕ) (h : n ≠ 0) : delta_function n 0 = 0 :=
begin
  rw delta_function,
  split_ifs,
  exfalso, apply h, exact h_1,
  refl,
end

lemma delta_function_zero' (n : ℕ) (h : n ≠ 0) : delta_function 0 n = 0 :=
begin
  rw delta_function,
  split_ifs,
  exfalso, apply h, exact eq.symm h_1,
  refl,
end

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

@[simp] lemma sum_bernoulli_neg (n : ℕ) ( h : 2 ≤ n ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli_neg k = 0 :=
begin
  induction n with n ih, { simp },
  rw [finset.sum_range_succ],
  rw [nat.choose_succ_self_right],
  rw [bernoulli_neg_def, mul_sub, sub_add_eq_add_sub, sub_eq_iff_eq_add],
  rw [finset.mul_sum, finset.sum_congr rfl],
  have f : delta_function n 0 = 0,
  {
    apply delta_function_zero, rintros f, rw f at h, norm_num at *,
  },
  rw f, simp,
  intros k hk, rw finset.mem_range at hk,
  rw [mul_div_right_comm, ← mul_assoc],
  congr' 1,
  rw [← mul_div_assoc, eq_div_iff], norm_cast,
  simp_rw [mul_comm, choose_mul_succ_eq n k], norm_num, left, norm_cast, rw <-cast_sub, have h:= le_of_lt hk, apply le_trans h (le_succ n),
  { contrapose! hk with H, rw sub_eq_zero at H, norm_cast at H, linarith }
end

def bernoulli_poly (n : ℕ) : ℚ → ℚ := λ X, ∑ i in finset.range (n+1),
  (bernoulli_neg i)*(nat.choose n i)*(X^(n-i))

namespace bernoulli_poly

lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1),
  (bernoulli_neg (n - i))*(nat.choose n i)*(X^i) :=
begin
  rw <-finset.sum_flip,
  rw bernoulli_poly, simp,
  rw <-sub_eq_zero_iff_eq,
  rw <-finset.sum_sub_distrib,
  apply finset.sum_eq_zero,
  rintros,
  rw sub_eq_zero_iff_eq,
  rw nat.sub_sub_self,
  rw choose_symm,
  {
    rw finset.mem_range at H,
    rw <-lt_succ_iff,
    exact H,
  },
  {
    rw finset.mem_range at H,
    rw <-lt_succ_iff,
    exact H,
  },
end

--lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1), (bernoulli_neg i)*(nat.choose n i)*(X^(n-i)) :=
--by { rw [bernoulli_poly, ← fin.sum_univ_eq_sum_range] }

@[simp] lemma bernoulli_poly_zero (X : ℚ) : bernoulli_poly 0 X = 1 := rfl

@[simp] lemma bernoulli_poly_zero' (n : ℕ) : bernoulli_poly n 0 = bernoulli_neg n :=
begin
  induction n with d hd,
  simp,
  rw [bernoulli_poly],  simp,
  try { rw [finset.sum_range_succ] },
  rw nat.sub_self,
  rw pow_zero,
  rw choose_self,
  rw mul_one, norm_cast, rw mul_one, apply add_eq_of_eq_sub', simp,
  have f : ∀ x ∈ finset.range (d.succ), (0 : ℚ)^(d.succ - x) = 0,
  {
    rintros x H,
    rw zero_pow,
    rw finset.mem_range at H,
    rw nat.lt_sub_right_iff_add_lt,
    simp,
    assumption,
  },
  apply finset.sum_eq_zero,
  rintros x H,
  rw mul_eq_zero,
  right,
  rw f,
  exact H,
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

lemma sum_antidiagonal {M : Type*} [add_comm_monoid M]
  (n : ℕ) (f : ℕ × ℕ → M) :
  ∑ (p : ℕ × ℕ) in finset.nat.antidiagonal n, f p = ∑ (i : ℕ) in finset.range (n + 1), f (i,(n - i)) :=
begin
  sorry
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
  rw succ_sub, rw succ_le_succ_iff, simp, exact le_of_lt hx,
  apply le_succ_of_le,
  exact le_of_lt hx,
end

namespace finset

lemma mem_range_le (n : ℕ) : ∀ x ∈ finset.range n, x ≤ n :=
begin
  rintros x hx,
  rw finset.mem_range at hx,
  apply le_of_lt hx,
end

lemma sub_ne_zero (n : ℕ) : ∀ x ∈ finset.range n, n - x ≠ 0 :=
begin
  rintros x hx,
  rw finset.mem_range at hx,
  rintros h,
  rw nat.sub_eq_zero_iff_le at h,
  apply le_lt_antisymm h hx,
end

lemma range_succ_mem_le (n x : ℕ) (h : x ∈ finset.range (n+1)) : x ≤ n :=
begin
  rw finset.mem_range at h,
  exact lt_succ_iff.1 h,
end

end finset

namespace nat

lemma le_two_eq_one_or_zero (n : ℕ) (f : n ≠ 1) (g : n ≠ 0) : 2 ≤ n :=
begin
  by_contradiction,
  simp at h,
  cases h, apply f, refl,
  cases h_ᾰ,
  apply g, refl,
  simp at *, apply not_succ_le_zero n, assumption,
end

lemma sub_add_assoc (k m n : ℕ) : k - (m + n) = k - m - n := by omega

end nat

open power_series

theorem exp_bernoulli_neg (f : ℕ → ℚ) (hf : f = λ i : ℕ, (bernoulli_neg i / (nat.factorial i)) )
(g : ℕ → ℚ) (hg : g = λ i : ℕ, if i = 0 then 0 else (1 / (nat.factorial (i) )) ) :
(power_series.mk f) * (power_series.mk g) = power_series.X :=
begin
  rw ext_iff,
  rintros,
  rw coeff_X,
  have g' : g 0 = 0,
  {
    rw hg, simp,
  },
  split_ifs,
  {
    rw h,
    rw coeff_mul,
    rw finset.nat.antidiagonal_succ,
    simp,
    rw hg, simp,
    rw hf, simp,
  },
  rw coeff_mul,
  by_cases n = 0,
  { rw h, simp, right, exact g', },
  have h' : 2 ≤ n,
  {
    apply nat.le_two_eq_one_or_zero, assumption, assumption,
  },
  simp,
  rw [hf, hg], simp,
  rw finset.sum_antidiagonal, simp,
  rw finset.sum_range_succ, simp,
  convert_to ∑ (i : ℕ) in finset.range n, (bernoulli_neg i / ↑(i.factorial) * (↑((n - i).factorial))⁻¹) = 0,
  rw <-sub_eq_zero_iff_eq,
  rw <-finset.sum_sub_distrib,
  apply finset.sum_eq_zero,
  rintros x hx,
  simp [finset.sub_ne_zero n x hx],
  suffices l : (n.factorial : ℚ) * (∑ (i : ℕ) in finset.range n, 1 / ((i.factorial) * ((n - i).factorial)) * bernoulli_neg i) = 0,
  {
    rw mul_eq_zero at l,
    cases l,
    {
      exfalso,
      simp at l,
      apply factorial_ne_zero n,
      assumption,
    },
    rw <-l,
    rw <-sub_eq_zero_iff_eq,
    rw <-finset.sum_sub_distrib,
    apply finset.sum_eq_zero,
    rintros x hx, rw sub_eq_zero_iff_eq,
    ring,
    rw mul_comm (bernoulli_neg x) (_)⁻¹,
    rw mul_eq_mul_right_iff,
    left,
    rw mul_inv',
    rw mul_comm,
  },
  {
    rw finset.mul_sum,
    convert_to (∑ (x : ℕ) in finset.range n, (n.choose x : ℚ) * bernoulli_neg x) = 0,
    {
      {
        rw <-sub_eq_zero_iff_eq,
        rw <-finset.sum_sub_distrib,
        apply finset.sum_eq_zero,
        rintros x hx, rw sub_eq_zero_iff_eq,
        rw <-mul_assoc,
        rw mul_eq_mul_right_iff,
        left,
        rw choose_eq_factorial_div_factorial,
        rw rat.coe_nat_div, simp,
        rw div_eq_mul_inv,
        {
          apply factorial_mul_factorial_dvd_factorial,
          apply finset.mem_range_le n x hx,
        },
        apply finset.mem_range_le n x hx,
      },
    },
    rw sum_bernoulli_neg,
    exact h',
  },
end

lemma bernoulli_poly_var (X : ℚ) (n : ℕ) : bernoulli_poly n (X + 1) =
 ∑ (i : ℕ) in finset.range (n + 1), (n.choose i : ℚ) * bernoulli_poly i X :=
begin
 have h : ∀ k : ℕ, (X + 1)^k = ∑ (i : ℕ) in finset.range (k + 1), k.choose i * X^i,
 {
   rintros k,
   rw add_pow X 1 k, simp [mul_comm],
 },
 rw [bernoulli_poly_def],
 conv_lhs
 {
   apply_congr,
   skip,
   rw h x,
 },
 conv_lhs
 {
   apply_congr,
   skip,
   rw finset.mul_sum,
   rw finset.range_eq_Ico,
 },
 rw finset.range_eq_Ico,
 rw <-finset.dependent_double_sum,
 conv_lhs
{
  apply_congr,
  skip,
  funext,
  rw [finset.sum_Ico_eq_sum_range, finset.range_eq_Ico],
  conv{
    apply_congr,
    skip,
    rw nat.sub_add_assoc,
  },
},
conv_rhs
{
  apply_congr,
  skip,
  rw bernoulli_poly_def,
  rw finset.mul_sum,
  rw finset.range_eq_Ico,
},
rw <-finset.dependent_double_sum,
conv_rhs
{
  apply_congr,
  skip,
  funext,
  rw [finset.sum_Ico_eq_sum_range, finset.range_eq_Ico],
  conv
  {
    apply_congr,
    skip,
    rw [nat.add_sub_cancel_left x _],
  },
},
rw <-sub_eq_zero_iff_eq,
rw <-finset.sum_sub_distrib,
apply finset.sum_eq_zero,
rintros x hx, rw sub_eq_zero_iff_eq,
rw <-finset.range_eq_Ico,
have k :∀ n : ℕ, ∀ x ∈ finset.range (n + 1), n + 1 - x = (n - x) + 1,
sorry,
rw [k],
rw <-finset.sum_flip,
rw <-sub_eq_zero_iff_eq,
rw <-finset.sum_sub_distrib,
apply finset.sum_eq_zero,
rintros y hy, rw sub_eq_zero_iff_eq,
rw nat.sub_sub_self, rw choose_symm_of_eq_add,
swap,
suffices l : n = x + (n - x - y) + y,
exact l,
{sorry,},
rw <-mul_assoc, rw <-mul_assoc, rw mul_eq_mul_right_iff, left,
rw <-mul_assoc, rw mul_comm _ (bernoulli_neg y), rw mul_assoc, rw mul_assoc, rw mul_eq_mul_left_iff, left,
rw choose_mul, rw <-choose_symm,
have d : x + (n - x - y) = n - y,
sorry,
rw d,
rw choose_mul,
rw mul_eq_mul_left_iff, left,
rw nat.add_sub_cancel_left,
have e : n - y - x = n - x - y,
sorry,
rw e,
rw choose_symm,
{
  exact finset.range_succ_mem_le _ _ hy,
},
{ apply nat.sub_le_self, },
sorry,
sorry,
sorry,
sorry,
exact finset.range_succ_mem_le _ _ hy,
rw <-finset.range_eq_Ico at hx, exact hx,
end

lemma exp_bernoulli_poly (t : ℕ) (f : ℕ → ℕ → ℚ) (hf : f = λ t i, (bernoulli_poly i t / (nat.factorial i)) )
(g : ℕ → ℕ → ℚ) (hg : g = λ t i, if i = 0 then 0 else (1 / (nat.factorial (i) )) )
(g' : ℕ → ℕ → ℚ) (hg' : g' = λ t i, (1 / (nat.factorial (i) )) ) :
(power_series.mk (f t)) * (power_series.mk (g t)) = power_series.X * (power_series.mk (g' t))^t :=
begin
  induction t with d hd,
  {
    simp,
    rw exp_bernoulli_neg,
    simp_rw hf, simp,
    simp_rw hg,
  },
  rw pow_succ,
  have lg' : ∀ x y, g' x = g' y,
  {
    rw hg',
    simp,
  },
  have lg : ∀ x y, g x = g y,
  {
    rw hg,
    simp,
  },
  rw lg' d.succ d,
  rw mul_comm  (mk (g' d)) (mk (g' d) ^ d),
  rw <-mul_assoc,
  rw <-hd,
  rw lg d.succ d,
  rw mul_comm,
  rw mul_comm (mk (f d)) (mk (g d)),
  rw mul_assoc,
  rw mul_eq_mul_left_iff,
  left,
  rw ext_iff,
  rintros,
  rw coeff_mul,
  simp,
  rw [hf, hg'],
  rw finset.sum_antidiagonal, simp only [cast_succ, factorial],
  simp_rw bernoulli_poly_var,
  rw finset.sum_div,
  rw <-sub_eq_zero_iff_eq,
  rw <-finset.sum_sub_distrib,
  apply finset.sum_eq_zero,
  rintros x hx, rw sub_eq_zero_iff_eq,
  rw div_eq_iff,
  rw mul_comm,
  rw div_eq_mul_one_div, rw mul_assoc, rw mul_assoc,
  rw mul_eq_mul_left_iff, left,
  rw choose_eq_factorial_div_factorial,
  rw rat.coe_nat_div,
  {
    rw mul_comm _ (n.factorial : ℚ), rw <-mul_assoc, rw mul_comm _ (n.factorial : ℚ), rw one_div, rw one_div,
    rw div_eq_iff, rw mul_assoc, rw mul_comm ((n - x).factorial : ℚ)⁻¹ _, rw <-mul_assoc, simp, rw <-mul_assoc,
    rw mul_assoc, rw rat.mul_inv_cancel ((n-x).factorial : ℚ), simp,
    rw mul_assoc, rw rat.inv_mul_cancel (x.factorial : ℚ), simp,
    {
      simp,
      apply factorial_ne_zero,
    },
    {
      simp,
      apply factorial_ne_zero,
    },
    simp,
    apply not_or,
    apply factorial_ne_zero,
    apply factorial_ne_zero,
  },
  {
    apply factorial_mul_factorial_dvd_factorial,
    rw finset.mem_range at hx,
    exact lt_succ_iff.1 hx,
  },
  {
    rw finset.mem_range at hx,
    exact lt_succ_iff.1 hx,
  },
  {
      simp,
      apply factorial_ne_zero,
  },
end

lemma one_sub_eq_neg : ∀ n : ℕ, ∀ X : ℚ, (bernoulli_poly n) ((1: ℚ) - X) = (-1)^n * bernoulli_poly n X :=
begin
  sorry
end

end bernoulli_poly

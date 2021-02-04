import number_theory.bernoulli
import data.nat.basic
import analysis.complex.roots_of_unity
import topology.algebra.infinite_sum
import data.real.ereal
import data.finset.basic
import tactic.linarith
import algebra.big_operators.intervals
import data.set.intervals.basic
import ring_theory.power_series.basic
import ring_theory.power_series.well_known

noncomputable theory
open_locale big_operators

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
  apply nat.le_lt_antisymm h hx,
end

lemma range_succ_mem_le (n x : ℕ) (h : x ∈ finset.range (n+1)) : x ≤ n :=
begin
  rw finset.mem_range at h,
  exact nat.lt_succ_iff.1 h,
end

end finset

open_locale nat

open nat

def choose_eq_factorial_div_factorial' {a b : ℕ}
  (hab : a ≤ b) : (b.choose a : ℚ) = b! / (a! * (b - a)!) :=
begin
  field_simp [mul_ne_zero, factorial_ne_zero],
  norm_cast,
  rw ← choose_mul_factorial_mul_factorial hab,
  ring,
end

lemma choose_mul (n k s : ℕ) (hn : k ≤ n) (hs : s ≤ k) : (n.choose k : ℚ) * k.choose s =
n.choose s * (n - s).choose (k - s) :=
begin
  -- write everything as ratios of factorials
  rw [choose_eq_factorial_div_factorial' hn,
      choose_eq_factorial_div_factorial' hs,
      choose_eq_factorial_div_factorial' (le_trans hs hn),
      choose_eq_factorial_div_factorial' ],
  -- notice annoying k - s ≤ n - s proof
  swap, exact nat.sub_le_sub_right hn s, -- thank you library-search, it was you or omega
    field_simp [mul_ne_zero, factorial_ne_zero],
  -- notice annoying `n - s - (k - s)` term
  rw sub_sub_sub_cancel_right hs, -- thank you library_search, it was you or omega
  ring,
end

open nat

def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * (bernoulli n)

@[simp] lemma bernoulli_neg_zero  : bernoulli_neg 0 = 1 := rfl

@[simp] lemma bernoulli_neg_one   : bernoulli_neg 1 = -1/2 :=
begin
  rw [bernoulli_neg, bernoulli_one], linarith,
end

theorem bernoulli_odd_eq_zero : ∀ n : ℕ, (n % 2 = 1 ∧ 1 < n) → bernoulli n = 0 :=sorry

theorem ber_neg_eq_ber : ∀ n : ℕ, n ≠ 1 → bernoulli_neg n = bernoulli n :=
begin
  rintros n hn,
  by_cases n = 0,
  { rw h, simp, },
  rw bernoulli_neg, rw neg_one_pow_eq_pow_mod_two,
  by_cases k : n%2 = 1,
  { rw k, simp,
    have f : 1 < n,
    {
      apply one_lt_iff_ne_zero_and_ne_one.2 ⟨h, hn⟩,
    },
    have g := bernoulli_odd_eq_zero n ⟨k,f⟩,
    rw g, simp,
  },
  simp at *,
  rw k, simp,
end

lemma succ_succ_ne_one (n : ℕ) : n.succ.succ ≠ 1 :=
  by { rintros h, rw one_succ_zero at h, simp only at h, apply succ_ne_zero n h, }

@[simp] lemma sum_bernoulli_neg (n : ℕ) ( h : 2 ≤ n ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli_neg k = 0 :=
begin
  cases n, {sorry},
  rw finset.sum_range_succ', simp,
  cases n, {sorry},
  {
    rw finset.sum_range_succ', simp,
    have f := sum_bernoulli n.succ.succ,
    rw finset.sum_range_succ' at f,
    rw finset.sum_range_succ' at f, simp at f,
    conv_lhs
    {
      congr, congr, apply_congr, skip,
      rw ber_neg_eq_ber, skip, apply_congr succ_succ_ne_one x, skip, skip,
    },
    have g := eq_sub_iff_add_eq.2 f,
    rw g,
    sorry,
  },
end

def bernoulli_poly (n : ℕ) : ℚ → ℚ := λ X, ∑ i in finset.range (n+1),
  (bernoulli_neg i)*(nat.choose n i)*(X^(n-i))

namespace bernoulli_poly

lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1),
  (bernoulli_neg (n - i))*(nat.choose n i)*(X^i) :=
begin
  -- flip the sum
  rw [← finset.sum_flip, bernoulli_poly],
  -- suffices to prove the terms in the sums are equal
  apply finset.sum_congr rfl,
  -- so assume k ≤ n,
  intros k hk,
  -- get hk to say something useful
  rw [finset.mem_range, lt_succ_iff] at hk,
  -- make the mathematical substitution we need
  rw choose_symm hk,
  -- now there should be hardly anything left
  congr',
  -- there's some stupid easy thing
  omega,
end

--lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1), (bernoulli_neg i)*(nat.choose n i)*(X^(n-i)) :=
--by { rw [bernoulli_poly, ← fin.sum_univ_eq_sum_range] }

/-
### examples
-/

section examples

open finset

@[simp] lemma bernoulli_poly_zero (X : ℚ) : bernoulli_poly 0 X = 1 := rfl

@[simp] lemma bernoulli_poly_zero' (n : ℕ) : bernoulli_poly n 0 = bernoulli_neg n :=
begin
  -- don't need induction
  -- rewrite the definition
  rw bernoulli_poly, dsimp only,
  -- this is a sum to range n.succ. There's a lemma for that. You can guess its name
  rw sum_range_succ,
  -- Claim: If we can show that sum is zero, we're done.
  suffices : ∑ (x : ℕ) in range n, bernoulli_neg x * (n.choose x) * 0 ^ (n - x) = 0,
  { rw this,
    -- Proof : the simplifier can do it.
    simp,
  },
  -- a sum is zero if all terms are zero
  apply sum_eq_zero,
  -- say k < n
  intros k hk, rw mem_range at hk,
  suffices : (0 : ℚ) ^ (n - k) = 0,
    rw this, simp,
  -- zero_pow is bound to exist
  apply zero_pow,
  -- library_search can now find the way
  exact nat.sub_pos_of_lt hk,
end

@[simp] lemma bernoulli_poly_one (X : ℚ) : bernoulli_poly 1 X = X -1/2 :=
begin
  simp [bernoulli_poly_def, sum_range_succ], ring,
end

end examples

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
  rw power_series.ext_iff,
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
    rw mul_inv', rw mul_comm ((↑(n - x)!)⁻¹) _,
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

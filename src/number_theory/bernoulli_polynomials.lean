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
  apply le_lt_antisymm h hx,
end

lemma range_succ_mem_le (n x : ℕ) (h : x ∈ finset.range (n+1)) : x ≤ n :=
begin
  rw finset.mem_range at h,
  exact lt_succ_iff.1 h,
end

lemma sum_eq_sum_iff {α β : Type*} [canonically_ordered_add_monoid β] [add_comm_group β] ( f g : α → ℕ ) (s : finset α)
( h : ∑ x in s, f x = ∑ x in s, g x) :  ∀ x ∈ s, f x  = g x :=
begin
  conv at h
  {
    rw <-sub_eq_zero_iff_eq,
    rw <-finset.sum_sub_distrib,
    conv
    {
      to_lhs,
      apply_congr,
      skip,
    },
  },
  have h' : ∑ (x : α) in s, (f - g) x = 0,
  simp at *, exact h,
  suffices f : ∀ (x : α), x ∈ s → (f - g) x = 0,
  simp at f,
  rintros x hx,
  specialize f x hx,
  rw sub_eq_zero_iff_eq at f, exact f,
  set g' := f - g with hg',
  have h1 := finset.sum_eq_zero_iff.1 h',
  sorry,
end

end finset

open_locale nat

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

/-def delta_function (i j : ℕ) : ℕ := if i = j then 1 else 0

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
-/

def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * (bernoulli n)

/-lemma bernoulli_neg_def (n : ℕ) :
  bernoulli_neg n = (-1)^n * (bernoulli n) :=
well_founded.fix_eq _ _ _ -/

/-lemma bernoulli_neg_def (n : ℕ) :
  bernoulli_neg n = (delta_function n 0) - ∑ k in finset.range n, (n.choose k) * (bernoulli_neg k) / (n + 1 - k) :=
by { rw [bernoulli_neg_def', ← fin.sum_univ_eq_sum_range], refl } -/

@[simp] lemma bernoulli_neg_zero  : bernoulli_neg 0 = 1 := rfl

@[simp] lemma bernoulli_neg_one   : bernoulli_neg 1 = -1/2 :=
begin
  rw [bernoulli_neg, bernoulli_one],
  linarith,
end

@[simp] lemma two_le_one_false : 2 ≤ 1 → false := by simp

@[simp] lemma two_le_of_ne_zero : ∀ n : ℕ, n ≠ 0 → 2 ≤ n + 1 :=
begin
  rintros n hn,
  induction n with d hd, { simp at *, exfalso, assumption, },
  sorry,
end

lemma zero_le_sub (a b x : ℕ) (h :  x ∈ finset.Ico a b ) : 0 ≤ (b - x) := sorry

lemma bernoulli_neg_def (k : ℕ) :
  bernoulli_neg k =
  (-1)^k - ∑ i in finset.range k, ↑(k.choose i) * (-1)^(k - i) * (bernoulli_neg i) / (k.succ - i) := sorry

lemma sum_choose_neg_one : ∀ n : ℕ, ∑ k in finset.range n, (n.choose k : ℚ) * (-1)^k =
  (-1)^(n - 1) := sorry

lemma neg_one_pow_succ : ∀ n : ℕ, (-1 : ℚ)^n = - (-1)^(n.succ) := sorry

@[simp] lemma sum_bernoulli_neg (n : ℕ) ( h : 2 ≤ n ) :
  ∑ k in finset.range n, (n.choose k : ℚ) * bernoulli_neg k = 0 :=
begin
  suffices f : (-1 : ℚ)^(n - 1) = ∑ i in finset.range n, (n.choose i) / (n.succ - i) * (bernoulli_neg i) * ∑ t in finset.range (n.succ - i), ((n.succ - i).choose t.succ) * (-1)^t - (-1)^n * ∑ i in finset.range n, (n.choose i) * (bernoulli i) / (n.succ - i),
  { conv_rhs at f
    {
      congr, apply_congr, skip,
      rw [<-one_mul ↑(n.choose _)],
      rw <-@one_div_mul_cancel ℚ _ n.succ _,
      rw mul_assoc _ ↑(n.succ) _, rw mul_comm ↑(n.succ) _, rw <-cast_mul,
      rw choose_mul_succ_eq, norm_num,

      rw [succ_sub _],
      rw [finset.sum_range_succ],skip,
      apply_congr ge_iff_le.2 (le_of_lt (finset.mem_range.1 H)),
      congr, skip, apply_congr, skip,
      rw [<-cast_sub _, succ_sub _], skip,
      apply_congr ge_iff_le.2 (le_of_lt (finset.mem_range.1 H)),
      apply_congr le_trans (le_of_lt (finset.mem_range.1 H)) (le_succ n),
    },
    simp at f, simp_rw[mul_add, finset.sum_add_distrib] at f,
    conv_rhs at f
    {
      congr, congr, apply_congr, skip,
      rw [bernoulli_neg], rw mul_comm ((-1)^x : ℚ) _,
      rw mul_assoc ↑(n.choose x) _ _, rw mul_assoc (bernoulli x) _ _,
      rw mul_comm ((-1)^x : ℚ) _, rw <-pow_add, rw nat.sub_add_cancel, rw <-mul_assoc, rw mul_comm,
      skip,
      apply_congr ge_iff_le.2 (le_of_lt (finset.mem_range.1 H)),
      {
        rw finset.range_eq_Ico,
        conv
        {
          apply_congr, skip, conv { congr, skip, apply_congr, skip, rw [neg_one_pow_succ _], rw [succ_eq_add_one x_1], rw [add_comm], },
          conv { congr, skip, rw [finset.range_eq_Ico, finset.sum_Ico_add (λ y, ↑((n - x).succ.choose (y)) * -(-1 : ℚ) ^ (y)) 0 (n-x) 1],  },
          norm_num,
          rw finset.sum_Ico_eq_sub, skip,
          apply_congr succ_le_succ_iff.2 (zero_le_sub _ n x H),
        },
        rw <-finset.range_eq_Ico,
        rw finset.range_one,
        conv {apply_congr, skip, rw [finset.sum_singleton], rw choose_zero_right, rw pow_zero, rw mul_sub,
          rw sum_choose_neg_one, rw[bernoulli_neg, mul_comm ((-1 : ℚ)^x) _, mul_assoc (↑(n.choose x)) _ _, mul_assoc (bernoulli x) _ _ ],
          rw <-pow_add, norm_num, rw nat.add_sub_cancel', rw <-mul_assoc _ _  ((-1 : ℚ)^n), rw mul_comm _ ((-1 : ℚ)^n), rw mul_comm (bernoulli x) _, rw [<-bernoulli_neg], skip,
          apply_congr le_of_lt (finset.mem_range.1 H),
            },
        norm_num, rw <-finset.mul_sum, rw sum_bernoulli,
      },
--      skip,
      congr, skip, apply_congr, skip,
      rw [<-cast_one, <-cast_add, <-nat.sub_add_comm _, cast_sub, cast_add, cast_one], skip,
      apply_congr le_trans (le_of_lt (finset.mem_range.1 H)) (le_succ n),
      apply_congr le_of_lt (finset.mem_range.1 H),
    },
    rw <-finset.mul_sum at f, rw sum_bernoulli at f,
    rw eq_sub_of_add_eq' (eq_sub_iff_add_eq.1 (bernoulli_def n)) at f,
    simp at f,
    sorry,
  },
  suffices f : (-1)^(n - 1) -
  ∑ k in finset.range n, ∑ i in finset.range k.succ,
  (n.choose k : ℚ) * (k.choose i) * (-1)^(k - i) * (bernoulli_neg i) / (k.succ - i) +
  ∑ k in finset.range n, (n.choose k) * (bernoulli_neg k) = ∑ k in finset.range n, ↑(n.choose k) * (bernoulli_neg k),
  {
    simp at f,
    have g : ∀ i ∈ finset.range n, n.succ - i = (n - i).succ := sorry,
    simp_rw [g],

    apply [succ_sub] _,
    simp_rw [finset.sum_range_succ],
    simp_rw [finset.range_eq_Ico] at f,
    rw <-finset.dependent_double_sum at f,
    rw [sub_eq_zero_iff_eq, <-finset.range_eq_Ico] at f,
    conv_rhs at f
    {
      apply_congr, skip,
      conv{
        apply_congr, skip,
        rw choose_mul,
        rw add_comm,
        skip,
        apply_congr le_of_lt (finset.Ico.mem.1 H_1).right,
        apply_congr (finset.Ico.mem.1 H_1).left,
      },
      rw [finset.sum_Ico_eq_sum_range],
      conv
      {
        apply_congr, skip,
        rw [<-add_sub (1 : ℚ) _ ↑x, cast_add, <-add_sub ↑x ↑x_1, add_sub_cancel'_right ↑x ↑x_1,  add_comm (1 : ℚ) _ ],
        rw mul_comm, rw <-mul_assoc (bernoulli_neg x) _ _, rw <-mul_assoc (bernoulli_neg x) _ _, rw mul_assoc (bernoulli_neg x * ↑(n.choose x)) _ _, rw mul_div_assoc,
      },
      rw <-finset.mul_sum,
    },
    simp at f,
    rw [finset.sum_Ico_eq_sum_range] at f,
    rw [choose_mul _ _] at f,

    rw [finset.sum_range_succ, add_comm, choose_succ_self_right],
    rw <-add_sub_cancel ( ∑ (x : ℕ) in finset.range n,
    ↑(n.succ.choose x) * bernoulli_neg x + ↑(n + 1) * bernoulli_neg n) ((n.succ : ℚ )*(-1)^(n - 1)),
    rw [bernoulli_neg, <-mul_assoc],
    have f : ((-1)^n : ℚ) = (-1)^(n - 1) * (-1) := sorry,
    rw f, rw <-mul_assoc, rw <-mul_one (↑(n.succ) * (-1) ^ (n - 1) : ℚ),
    rw <-mul_add (↑(n + 1) * (-1)^(n - 1) : ℚ) _ _,
    sorry },
  {
    rw [<-sum_choose_neg_one, <-finset.sum_sub_distrib, <-sub_eq_zero_iff_eq,
    <-finset.sum_sub_distrib, finset.sum_eq_zero], rintros x hx,
    rw [bernoulli_neg_def, mul_sub, finset.mul_sum], simp,
    rw <-finset.sum_sub_distrib,
    apply finset.sum_eq_zero, rintros y hy,
    rw [sub_eq_zero_iff_eq, mul_assoc ↑(n.choose x) _ _,
    mul_assoc ↑(n.choose x) _ _, <-mul_div_assoc],  },
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

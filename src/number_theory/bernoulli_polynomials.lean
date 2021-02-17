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
  rw ← @@finset.sum_sigma _ _ _ (λ i, finset.Ico i b) (λ x, f x.1 x.2),
  rw ← @@finset.sum_sigma _ _ _ (λ j, finset.Ico a (j+1)) (λ x, f x.2 x.1),
  refine finset.sum_bij'
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _ (λ _ _, rfl)
    (λ (x : Σ (i : ℕ), ℕ) _, (⟨x.2, x.1⟩ : Σ (i : ℕ), ℕ)) _
    (by rintro ⟨⟩ _; refl) (by rintro ⟨⟩ _; refl);
  simp only [finset.Ico.mem, sigma.forall, finset.mem_sigma];
  rintros a b ⟨⟨h₁,h₂⟩, ⟨h₃, h₄⟩⟩; refine ⟨⟨_, _⟩, ⟨_, _⟩⟩; linarith
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

lemma choose_mul {n k s : ℕ} (hn : k ≤ n) (hs : s ≤ k) : (n.choose k : ℚ) * k.choose s =
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

open nat finset

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
  cases n, { norm_num at *, },
  rw finset.sum_range_succ', simp,
  cases n, { norm_num at *, },
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
    rw g, ring,
  },
end

variables {A : Type*} [ring A] [algebra ℚ A]

--[decidable_eq]

def bernoulli_poly (n : ℕ) : polynomial ℚ := ∑ i in finset.range (n+1),
  polynomial.monomial (n-i) ((bernoulli_neg i)*(nat.choose n i))

lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n = ∑ i in finset.range (n+1),
  polynomial.monomial i ((bernoulli_neg (n - i))*(nat.choose n i)) := sorry

/-finsupp.on_finset (range n.succ)
  (λ i, bernoulli_neg (n - i) * nat.choose n i)
  (begin rintros a, contrapose, simp only [cast_eq_zero, mem_range, not_lt, not_not, mul_eq_zero],
    rintros h, right, exact choose_eq_zero_of_lt (succ_le_iff.1 h) end)-/

--∑ i in finset.range (n+1), ((bernoulli_neg i)*(nat.choose n i)) * (X^(n-i))

namespace bernoulli_poly

/-lemma bernoulli_poly_def (n : ℕ) (X : A) : bernoulli_poly n X = ∑ i in finset.range (n+1),
  ((bernoulli_neg (n - i))*(nat.choose n i))•(X^i) :=
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
end -/

--lemma bernoulli_poly_def (n : ℕ) (X : ℚ) : bernoulli_poly n X = ∑ i in finset.range (n+1), (bernoulli_neg i)*(nat.choose n i)*(X^(n-i)) :=
--by { rw [bernoulli_poly, ← fin.sum_univ_eq_sum_range] }

/-
### examples
-/

section examples

open finset

/-@[simp] lemma bernoulli_poly_coeff (n : ℕ) (i ∈ finset.range n.succ) : (bernoulli_poly n).coeff i =
  bernoulli_neg (n - i) * (nat.choose n i) :=
begin
  rw bernoulli_poly, rw ←polynomial.apply_eq_coeff,
end -/

/-@[simp] lemma bernoulli_poly_degree (n : ℕ) : (bernoulli_poly n).degree = n :=
begin
rw bernoulli_poly, rw polynomial.degree,
apply polynomial.card_supp_le_succ_nat_degree,
sorry
end -/

/-lemma bernoulli_poly_coeff' (n i : ℕ) (h : n < i) : (bernoulli_poly n).coeff i = 0 :=
begin
  rw polynomial.coeff_eq_zero_of_degree_lt, rw bernoulli_poly_degree, norm_cast, assumption,
end -/

@[simp] lemma bernoulli_poly_zero : bernoulli_poly 0 = 1 :=
begin
  rw bernoulli_poly, simp only [mul_one, cast_one, polynomial.monomial_zero_left,
  bernoulli_neg_zero, sum_singleton, ring_hom.map_one, choose_self, range_one],
end

@[simp] lemma bernoulli_poly_zero' (n : ℕ) : (bernoulli_poly n).eval 0 = bernoulli_neg n :=
begin
  rw bernoulli_poly, rw polynomial.eval_finset_sum, simp,
  rw sum_range_succ, simp, apply sum_eq_zero, rintros x hx, rw zero_pow', simp,
  { intros h, apply nat.lt_le_antisymm (mem_range.1 hx) (nat.sub_eq_zero_iff_le.1 h), },
end

@[simp] lemma bernoulli_poly_one : bernoulli_poly 1 = polynomial.X + (-1)/2 :=
begin
  rw bernoulli_poly, rw sum_range_succ, simp, rw ←polynomial.X_pow_eq_monomial 1, rw add_comm, simp,
  --rw polynomial.C_eq_algebra_map,
  sorry,
end

end examples

@[simp] lemma nat.le_self_add (x y : ℕ) : x ≤ x + y :=
begin
  exact le.intro rfl,
end

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in finset.range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
   polynomial.monomial n (n + 1 : ℚ) :=
begin
  cases n, simp,
  simp_rw [bernoulli_poly_def],
  simp_rw [finset.smul_sum],
  simp_rw [finset.range_eq_Ico],
  rw ←finset.dependent_double_sum,
  simp_rw [finset.sum_Ico_eq_sum_range], simp,
  simp_rw [polynomial.smul_monomial], simp_rw [mul_comm (bernoulli_neg _) _],
  simp_rw [smul_eq_mul, ←mul_assoc],
  conv_lhs
  { apply_congr, skip, conv
  { apply_congr, skip,
    rw choose_mul ((nat.le_sub_left_iff_add_le (mem_range_le _ _ H)).1 (mem_range_le _ _ H_1))
      (le.intro rfl),
    rw add_comm x x_1, rw nat.add_sub_cancel, rw mul_assoc, rw mul_comm, rw ←smul_eq_mul,
    rw ←polynomial.smul_monomial, },
    rw [←sum_smul], skip, },
  rw sum_range_succ, simp,
  have f : ∀ x ∈ range n.succ, 2 ≤ n.succ + 1 - x, sorry,
  conv_lhs
  { apply_congr, skip, rw [sum_bernoulli_neg _ (f x H)], rw zero_smul, skip, },
  simp,
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

/- theorem exp_bernoulli_neg (f : ℕ → ℚ) (hf : f = λ i : ℕ, (bernoulli_neg i / (nat.factorial i)) )
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
  rw finset.nat.sum_antidiagonal_eq_sum_range_succ_mk, simp,
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
end -/

open finset nat

variables {R : Type*} [comm_semiring R]

/-- The ring homomorphism taking a power series `f(X)` to `f(aX)`. -/
noncomputable def eval_mul_hom (a : R) : power_series R →+* power_series R :=
{ to_fun :=   λ f, power_series.mk $ λ n, a^n * (power_series.coeff R n f),
  map_zero' := by { ext, simp only [linear_map.map_zero, power_series.coeff_mk, mul_zero], },
  map_one' := by { ext1, simp only [mul_boole, power_series.coeff_mk, power_series.coeff_one],
                split_ifs, { rw [h, pow_zero], }, refl, },
  map_add' := by {intros, ext, norm_num, rw mul_add, },
  map_mul' := by {intros, ext, rw [power_series.coeff_mul, power_series.coeff_mk,
              power_series.coeff_mul, finset.mul_sum], apply sum_congr rfl, norm_num,
              intros b c H, rw [<-H, pow_add], ring, }, }


theorem exp_bernoulli_poly' (t : A) :
  power_series.mk (λ n, (bernoulli_poly n / nat.factorial n)) * (exp ℚ - 1)
    = X * eval_mul_hom t (exp A) :=
begin
  ext, rw coeff_mul, rw coeff_mul, rw finset.nat.sum_antidiagonal_eq_sum_range_succ_mk, rw finset.nat.sum_antidiagonal_eq_sum_range_succ_mk,
  simp only [coeff_mk, coeff_one, coeff_exp, ring_hom.id_apply, linear_map.map_sub, factorial,
  rat.algebra_map_rat_rat], rw finset.sum_range_succ, simp,
  have f : ∑ (x : ℕ) in range n, bernoulli_poly x t / ↑x! * ((↑(n - x)!)⁻¹ - ite (n - x = 0) 1 0) =
    ∑ (x : ℕ) in range n, bernoulli_poly x t / ↑x! * (↑(n - x)!)⁻¹,
  {
    apply sum_congr, { refl, }, rintros x hx, split_ifs,
    { exfalso, rw nat.sub_eq_zero_iff_le at h, rw mem_range at hx, revert h hx, omega, },
    { simp, },
  },
  rw f, cases n, { simp, },
  have g : ∑ (i : ℕ) in range (n.succ + 1), (coeff ℚ i) X *
    (coeff ℚ (n.succ - i)) ((eval_mul_hom t) (exp ℚ))
    = (coeff ℚ n) ((eval_mul_hom t) (exp ℚ)),
  {
    suffices g : ∑ (i : ℕ) in range (n.succ + 1), (coeff ℚ i) X *
    (coeff ℚ (n.succ - i)) ((eval_mul_hom t) (exp ℚ))
    = (coeff ℚ 1) X * (coeff ℚ (n.succ - 1)) ((eval_mul_hom t) (exp ℚ)),
    { rw g, rw coeff_X, simp, },
    { refine sum_eq_single 1 _ _,
      { rintros b H hb, rw coeff_X, revert hb, simp, rintros b1 b2, exfalso, apply b1 b2, },
      { rintros H, exfalso, apply H, rw mem_range_succ_iff, omega, },
    },
  },
  rw g, rw eval_mul_hom, simp only [coeff_mk, ring_hom.coe_mk, coeff_exp, ring_hom.id_apply,
  rat.algebra_map_rat_rat], rw ←div_eq_mul_one_div, symmetry, rw div_eq_iff,
  {
    suffices f : t^n = (∑ k in finset.range (n + 1), ((n + 1).choose k : ℚ) *
      bernoulli_poly k t) / (n + 1 : ℚ),
    {

      rw f, rw div_eq_iff, rw mul_assoc _ _ (n + 1 : ℚ), rw mul_comm _ (n + 1 : ℚ),
      norm_cast, rw ←factorial_succ, rw sum_mul, apply sum_congr, { refl, }, rintros x hx,
      rw choose_eq_factorial_div_factorial',
      { rw div_mul_comm', simp, left, ring, rw mul_inv', ring, },
      { apply mem_range_le _ _ hx, },
      { norm_cast, apply succ_ne_zero, },
    },
    rw eq_div_iff, { rw mul_comm, rw sum_bernoulli_poly _ _, },
    { norm_cast, apply succ_ne_zero, },
  },
  { norm_cast, apply factorial_ne_zero n, },
end

end bernoulli_poly

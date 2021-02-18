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
  rw [choose_eq_factorial_div_factorial' hn,
      choose_eq_factorial_div_factorial' hs,
      choose_eq_factorial_div_factorial' (le_trans hs hn),
      choose_eq_factorial_div_factorial' ],
  swap, exact nat.sub_le_sub_right hn s,
    field_simp [mul_ne_zero, factorial_ne_zero],
  rw sub_sub_sub_cancel_right hs,
  ring,
end

open nat finset

def bernoulli_neg (n : ℕ) : ℚ := (-1)^n * (bernoulli n)

@[simp] lemma bernoulli_neg_zero  : bernoulli_neg 0 = 1 := rfl

@[simp] lemma bernoulli_neg_one   : bernoulli_neg 1 = -1/2 :=
begin
  rw [bernoulli_neg, bernoulli_one], linarith,
end

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
    have g := bernoulli_odd_eq_zero (odd_iff.2 k) f,
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

variables {A : Type*} [integral_domain A] [algebra ℚ A]

--[decidable_eq]

def bernoulli_poly (n : ℕ) : polynomial ℚ := ∑ i in finset.range (n+1),
  polynomial.monomial (n-i) ((bernoulli_neg i)*(nat.choose n i))

lemma bernoulli_poly_def (n : ℕ) : bernoulli_poly n = ∑ i in finset.range (n+1),
  polynomial.monomial i ((bernoulli_neg (n - i))*(nat.choose n i)) :=
begin
  rw ←sum_range_reflect, simp, rw bernoulli_poly, apply sum_congr, {refl,}, rintros x hx,
  rw mem_range_succ_iff at hx,
  rw choose_symm hx, rw nat.sub_sub_self hx,
end

namespace bernoulli_poly

/-
### examples
-/

section examples

open finset

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

end examples

@[simp] theorem sum_bernoulli_poly (n : ℕ) :
  ∑ k in finset.range (n + 1), ((n + 1).choose k : ℚ) • bernoulli_poly k =
   polynomial.monomial n (n + 1 : ℚ) :=
begin
  cases n, simp,
  simp_rw [bernoulli_poly_def, finset.smul_sum, finset.range_eq_Ico],
  rw ←finset.dependent_double_sum,
  simp_rw [finset.sum_Ico_eq_sum_range], simp,
  simp_rw [polynomial.smul_monomial, mul_comm (bernoulli_neg _) _, smul_eq_mul, ←mul_assoc],
  conv_lhs
  { apply_congr, skip, conv
  { apply_congr, skip,
    rw choose_mul ((nat.le_sub_left_iff_add_le (mem_range_le _ _ H)).1 (mem_range_le _ _ H_1))
      (le.intro rfl),
    rw add_comm x x_1, rw nat.add_sub_cancel, rw mul_assoc, rw mul_comm, rw ←smul_eq_mul,
    rw ←polynomial.smul_monomial, },
    rw [←sum_smul], skip, },
  rw sum_range_succ, simp,
  have f : ∀ x ∈ range n.succ, 2 ≤ n.succ + 1 - x,
  { rintros x H,
    rw succ_sub (ge_iff_le.1 (mem_range_le _ _ H)), rw succ_le_succ_iff,
    rw succ_sub (ge_iff_le.1 (mem_range_succ_iff.1 H)), rw succ_le_succ_iff, norm_num, },
  conv_lhs
  { apply_congr, skip, rw [sum_bernoulli_neg _ (f x H)], rw zero_smul, skip, },
  simp,
end

open power_series

open finset nat

theorem exp_bernoulli_poly' [char_zero A] (t : A) :
  power_series.mk (λ n, (polynomial.aeval t ((1 / nat.factorial n : ℚ) • bernoulli_poly n))) * (exp A - 1)
    = X * rescale t (exp A) :=
begin
  ext, rw [coeff_mul, coeff_mul, finset.nat.sum_antidiagonal_eq_sum_range_succ_mk,
  finset.nat.sum_antidiagonal_eq_sum_range_succ_mk],
  simp only [coeff_mk, coeff_one, coeff_exp, ring_hom.id_apply, linear_map.map_sub, factorial,
  rat.algebra_map_rat_rat],
  rw finset.sum_range_succ,
  have f : ∀ x ∈ range n, ite (n - x = 0) 1 0 = (0 : A),
  { rintros x hx, split_ifs,
    { exfalso, apply sub_ne_zero _ _ hx h, }, refl, },
  conv_lhs { congr, skip, apply_congr, skip, rw f x H, },
  cases n, { simp, },
  symmetry, rw [sum_eq_single 1],
  { simp, rw mul_comm,
    suffices g : (algebra_map ℚ A) (↑n!)⁻¹ * (n.succ : ℚ) • t ^ n = (n.succ : ℚ) • ∑ (x : ℕ) in range n.succ,
      (↑x!)⁻¹ • ((polynomial.aeval t) (bernoulli_poly x) * (algebra_map ℚ A) (↑(n.succ - x)!)⁻¹),
    { rw [algebra.mul_smul_comm, algebra.smul_def, algebra.smul_def, mul_eq_mul_left_iff] at g,
      cases g with g1 g2, exact g1,
      { exfalso, apply succ_ne_zero n, simp at g2, norm_cast at *, }, },
    { have g : (n.succ : ℚ) • t^n = polynomial.aeval t (polynomial.monomial n (n + 1 : ℚ)),
        { rw polynomial.aeval_monomial, rw algebra.smul_def, norm_num, },
      rw [g, ←sum_bernoulli_poly, smul_sum, alg_hom.map_sum, mul_sum], apply sum_congr, refl,
      { rintros x hx, rw alg_hom.map_smul, rw ←algebra.smul_def,
        rw mul_comm ((polynomial.aeval t) (bernoulli_poly x)) _, rw ←algebra.smul_def,
        rw smul_smul, rw smul_smul, rw ←smul_assoc, rw algebra.smul_def, rw algebra.smul_def,
        rw mul_eq_mul_right_iff, left, rw smul_eq_mul, apply congr_arg _,
        rw choose_eq_factorial_div_factorial, rw cast_dvd_char_zero, rw factorial_succ n,
        rw cast_mul, rw cast_mul, rw div_eq_inv_mul, rw mul_inv', rw ←mul_assoc, rw mul_comm (↑n!)⁻¹ _,
        rw mul_assoc ↑(n.succ) _ _, symmetry, rw mul_comm ↑(n.succ) _,
        rw mul_assoc ((↑x!)⁻¹ * (↑(n + 1 - x)!)⁻¹) _ _, rw mul_comm ↑(n.succ) _, rw ←mul_assoc (↑n!)⁻¹ _ _,
        rw inv_mul_cancel, rw one_mul,
        { norm_num, apply factorial_ne_zero n, },
        { apply factorial_mul_factorial_dvd_factorial (mem_range_le _ _ hx), },
        { apply mem_range_le _ _ hx, }, }, }, },
  { rintros b hb h, rw coeff_X b, split_ifs,
    { exfalso, apply h h_1, },
    { norm_num, }, },
  { rintros h, exfalso, apply h, rw mem_range_succ_iff, rw succ_le_succ_iff, apply nat.zero_le _, },
end

end bernoulli_poly

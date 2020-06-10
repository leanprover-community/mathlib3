/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.convex.specific_functions
import analysis.special_functions.pow
import data.real.conjugate_exponents
import tactic.nth_rewrite

/-!
# Mean value inequalities

In this file we prove various inequalities between mean values:
arithmetic mean, geometric mean, generalized mean (natural and integer
cases).

For generalized means we only prove
$\left( ∑_j w_j z_j \right)^n ≤ ∑_j w_j z_j^n$ because standard versions would
require $\sqrt[n]{x}$ which is not implemented in `mathlib` yet.

Probably a better approach to the generalized means inequality is to
prove `convex_on_rpow` in `analysis/convex/specific_functions` first,
then apply it.

It is not yet clear which versions will be useful in the future, so we
provide two different forms of most inequalities : for `ℝ` and for
`ℝ≥0`. For the AM-GM inequality we also prove special cases for `n=2`
and `n=3`.
-/

universes u v

open real finset
open_locale classical nnreal big_operators
noncomputable theory

variables {ι : Type u} (s : finset ι)

/-- Geometric mean is less than or equal to the arithmetic mean, weighted version
for functions on `finset`s. -/
theorem real.am_gm_weighted (w z : ι → ℝ)
  (hw : ∀ i ∈ s, 0 ≤ w i) (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) :
  (∏ i in s, (z i) ^ (w i)) ≤ ∑ i in s, w i * z i :=
begin
  let s' := s.filter (λ i, w i ≠ 0),
  rw [← sum_filter_ne_zero] at hw',
  suffices : (∏ i in s', (z i) ^ (w i)) ≤ ∑ i in s', w i * z i,
  { have A : ∀ i ∈ s, i ∉ s' → w i = 0,
    { intros i hi hi',
      simpa only [hi, mem_filter, ne.def, true_and, not_not] using hi' },
    have B : ∀ i ∈ s, i ∉ s' → (z i) ^ (w i) = 1,
      from λ i hi hi', by rw [A i hi hi', rpow_zero],
    have C : ∀ i ∈ s, i ∉ s' → w i * z i = 0,
      from λ i hi hi', by rw [A i hi hi', zero_mul],
    rwa [← prod_subset s.filter_subset B, ← sum_subset s.filter_subset C] },
  have A : ∀ i ∈ s', i ∈ s ∧ w i ≠ 0, from λ i hi, mem_filter.1 hi,
  replace hz : ∀ i ∈ s', 0 ≤ z i := λ i hi, hz i (A i hi).1,
  replace hw : ∀ i ∈ s', 0 ≤ w i := λ i hi, hw i (A i hi).1,
  by_cases B : ∃ i ∈ s', z i = 0,
  { rcases B with ⟨i, imem, hzi⟩,
    rw [prod_eq_zero imem],
    { exact sum_nonneg (λ j hj, mul_nonneg (hw j hj) (hz j hj)) },
    { rw hzi, exact zero_rpow (A i imem).2 } },
  { replace hz : ∀ i ∈ s', 0 < z i,
      from λ i hi, lt_of_le_of_ne (hz _ hi) (λ h, B ⟨i, hi, h.symm⟩),
    have := convex_on_exp.map_sum_le hw hw' (λ i _, set.mem_univ $ log (z i)),
    simp only [exp_sum, (∘), smul_eq_mul, mul_comm (w _) (log _)] at this,
    convert this using 1,
    { exact prod_congr rfl (λ i hi, rpow_def_of_pos (hz i hi) _) },
    { exact sum_congr rfl (λ i hi, congr_arg _ (exp_log $ hz i hi).symm) } }
end

theorem nnreal.am_gm_weighted (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) :
  (∏ i in s, (z i) ^ (w i:ℝ)) ≤ ∑ i in s, w i * z i :=
begin
  rw [← nnreal.coe_le_coe, nnreal.coe_prod, nnreal.coe_sum],
  refine real.am_gm_weighted _ _ _ (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg),
  assumption_mod_cast
end

theorem nnreal.am_gm2_weighted (w₁ w₂ p₁ p₂ : ℝ≥0) (hw : w₁ + w₂ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) ≤ w₁ * p₁ + w₂ * p₂ :=
begin
  have := nnreal.am_gm_weighted (univ : finset (fin 2)) (fin.cons w₁ $ fin.cons w₂ fin_zero_elim)
    (fin.cons p₁ $ fin.cons p₂ $ fin_zero_elim),
  simp only [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
    fin.cons_succ, fin.cons_zero, add_zero, mul_one] at this,
  exact this hw
end

theorem real.am_gm2_weighted {w₁ w₂ p₁ p₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
  (hp₁ : 0 ≤ p₁) (hp₂ : 0 ≤ p₂) (hw : w₁ + w₂ = 1) :
  p₁ ^ w₁ * p₂ ^ w₂ ≤ w₁ * p₁ + w₂ * p₂ :=
nnreal.am_gm2_weighted ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ $ nnreal.coe_eq.1 $ by assumption

theorem nnreal.am_gm3_weighted (w₁ w₂ w₃ p₁ p₂ p₃ : ℝ≥0) (hw : w₁ + w₂ + w₃ = 1) :
  p₁ ^ (w₁:ℝ) * p₂ ^ (w₂:ℝ) * p₃ ^ (w₃:ℝ) ≤ w₁ * p₁ + w₂ * p₂ + w₃ * p₃:=
begin
  have := nnreal.am_gm_weighted (univ : finset (fin 3))
    (fin.cons w₁ $ fin.cons w₂ $ fin.cons w₃ fin_zero_elim)
    (fin.cons p₁ $ fin.cons p₂ $ fin.cons p₃ fin_zero_elim),
  simp only [fin.prod_univ_succ, fin.sum_univ_succ, fin.prod_univ_zero, fin.sum_univ_zero,
    fin.cons_succ, fin.cons_zero, add_zero, mul_one, (add_assoc _ _ _).symm,
    (mul_assoc _ _ _).symm] at this,
  exact this hw
end

/-- Young's inequality, a version for nonnegative real numbers. -/
theorem real.young_inequality_of_nonneg {a b p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
  (hpq : p.is_conjugate_exponent q) :
  a * b ≤ a^p / p + b^q / q :=
by simpa [← rpow_mul, ha, hb, hpq.ne_zero, hpq.symm.ne_zero, div_eq_inv_mul]
  using real.am_gm2_weighted (le_of_lt hpq.one_div_pos) (le_of_lt hpq.symm.one_div_pos)
    (rpow_nonneg_of_nonneg ha p) (rpow_nonneg_of_nonneg hb q) hpq.inv_add_inv_conj

/-- Young's inequality, a version for arbitrary real numbers. -/
theorem real.young_inequality (a b : ℝ) {p q : ℝ} (hpq : p.is_conjugate_exponent q) :
  a * b ≤ (abs a)^p / p + (abs b)^q / q :=
calc a * b ≤ abs (a * b)                   : le_abs_self (a * b)
       ... = abs a * abs b                 : abs_mul a b
       ... ≤ (abs a)^p / p + (abs b)^q / q :
  real.young_inequality_of_nonneg (abs_nonneg a) (abs_nonneg b) hpq

/-- Young's inequality, `ℝ≥0` version -/
theorem nnreal.young_inequality (a b : ℝ≥0) {p q : ℝ≥0} (hp : 1 < p) (hpq : 1 / p + 1 / q = 1) :
  a * b ≤ a^(p:ℝ) / p + b^(q:ℝ) / q :=
real.young_inequality_of_nonneg a.coe_nonneg b.coe_nonneg ⟨hp, nnreal.coe_eq.2 hpq⟩

theorem real.pow_am_le_am_pow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 ≤ z i) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n :=
(convex_on_pow n).map_sum_le hw hw' hz

theorem nnreal.pow_am_le_am_pow (w z : ι → ℝ≥0) (hw' : ∑ i in s, w i = 1) (n : ℕ) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n :=
begin
  rw [← nnreal.coe_le_coe],
  push_cast,
  refine (convex_on_pow n).map_sum_le (λ i _, (w i).coe_nonneg) _ (λ i _, (z i).coe_nonneg),
  assumption_mod_cast
end

theorem real.pow_am_le_am_pow_of_even (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) {n : ℕ} (hn : n.even) :
  (∑ i in s, w i * z i) ^ n ≤ ∑ i in s, w i * z i ^ n :=
(convex_on_pow_of_even hn).map_sum_le hw hw' (λ _ _, trivial)

theorem real.fpow_am_le_am_fpow (w z : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
  (hw' : ∑ i in s, w i = 1) (hz : ∀ i ∈ s, 0 < z i) (m : ℤ) :
  (∑ i in s, w i * z i) ^ m ≤ ∑ i in s, w i * z i ^ m :=
(convex_on_fpow m).map_sum_le hw hw' hz

namespace finset

variables {p q : ℝ}

variables {f g : ι → ℝ}

/-- `L^p` seminorm given by the `L^p` norm of the restriction of `f` to `s : finset ι`. -/
def lp_seminorm (s : finset ι) (p : ℝ) (f : ι → ℝ) : ℝ :=
(∑ i in s, (abs $ f i) ^ p) ^ (1 / p)

def holder_dual (f : ι → ℝ) (p : ℝ) (i : ι) : ℝ := (abs $ f i) ^ p / f i

lemma inner_self_holder_dual : ∑ i in s, f i * holder_dual f p i = ∑ i in s, (abs $ f i) ^ p :=
sum_congr rfl $ λ i hi, by simp only [holder_dual, mul_div_cancel']


lemma lq_norm_holder_dual (hpq : is_conjugate_exponent p q) (h : ∑ i in s, (abs $ f i)^p ≠ 0) :
  ∑ i in s, (

lemma inner_self_holder_dual (hpq : is_conjugate_exponent p q) :
  ∑ i, f i * (holder_dual s f p i) = (∑ i 

theorem lq_norm_conj_eq_one_nnreal (hf : ∑ i in s, (f i)^p ≠ 0) (hpq : is_conjugate_exponent p q) :
  ∑ i in s, ((f i) ^ (p - 1) / (∑ i in s, (f i) ^ p) ^ (1 / q)) ^ q = 1 :=
by simp only [nnreal.div_rpow, ← nnreal.rpow_mul, mul_div_assoc', hpq.sub_one_mul_conj,
  one_div_mul_cancel hpq.symm.ne_zero, nnreal.rpow_one, ← nnreal.sum_div, nnreal.div_self hf]

variables (f g)

/-- An auxiliary lemma for Hölder inequality. -/
theorem sum_mul_le_one_of_lp_le_one_of_lq_le_one (hpq : is_conjugate_exponent p q)
  (hf : ∑ i in s, (f i)^p ≤ 1) (hg : ∑ i in s, (g i)^q ≤ 1) :
  ∑ i in s, f i * g i ≤ 1 :=
-- calc ∑ i in s, f i * g i ≤ ∑ i in s, ((f i)^p / ⟨p, hpq.nonneg⟩ + (g i)^q / ⟨q, hpq.symm.nonneg⟩) :
  -- sum_le_sum $ λ i hi, nnreal.young_inequality hpq.1 (nnreal.eq hpq.2) (f i) (g i)
-- ... = (∑ i in s, ((abs $ f i)^p)) / p + (∑ i in s, (abs $ g i)^q) / q :
  -- by simp only [sum_add_distrib, sum_div]
-- ... ≤ 1 / p + 1 / q : add_le_add (div_le_div_of_le_of_nonneg hf (le_of_lt hpq.pos))
  -- (div_le_div_of_le_of_nonneg hg (le_of_lt hpq.symm.pos))
-- ... = 1 : hpq.inv_add_inv_conj

theorem sum_mul_le_lp_mul_lq_nnreal (hpq : is_conjugate_exponent p q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (f i)^p) ^ (1 / p) * (∑ i in s, (g i)^q) ^ (1 / q) :=
begin
  -- First consider the cases `f = 0` and `g = 0`.
  have : ∀ (f g : ι → ℝ≥0) {p q : ℝ}, ((∑ i in s, (f i)^p) = 0) → is_conjugate_exponent p q →
    ∑ i in s, f i * g i ≤ (∑ i in s, (f i)^p) ^ (1 / p) * (∑ i in s, (g i)^q) ^ (1 / q),
  { intros f g p q hf hpq,
    replace hf : ∀ i ∈ s, f i = 0, by simpa [hpq.ne_zero] using hf,
    rw [sum_eq_zero, sum_eq_zero, nnreal.zero_rpow hpq.one_div_ne_zero, zero_mul];
    { intros i hi, simp [hf i hi, hpq.ne_zero] } },
  by_cases hf : ∑ i in s, (f i)^p = 0, { exact this f g hf hpq },
  by_cases hg : ∑ i in s, (g i)^q = 0, { simpa only [mul_comm] using this g f hg hpq.symm },
  clear this,
  -- Now we divide each vector by its norm and apply `sum_mul_le_one_of_lp_le_one_of_lq_le_one`
  have : ∀ {f : ι → ℝ≥0} {p q : ℝ}, is_conjugate_exponent p q → ∑ i in s, (f i)^p ≠ 0 →
    ∑ i in s, (abs (↑(f i / (∑ i in s, (f i)^p)^(1/p)) : ℝ))^p ≤ 1,
  { refine λ f p q hpq hf, le_of_eq _,
    simp only [abs_of_nonneg (nnreal.coe_nonneg _)],
    norm_cast,
    simp_rw [nnreal.div_rpow, ← nnreal.sum_div, ← nnreal.rpow_mul, one_div_mul_cancel hpq.ne_zero,
      nnreal.rpow_one, nnreal.div_self hf] },
  have := s.sum_mul_le_one_of_lp_le_one_of_lq_le_one hpq (this hpq hf) (this hpq.symm hg),
  norm_cast at this,
  simp only [div_mul_div', ← nnreal.sum_div] at this,
  rwa [nnreal.div_le_iff, one_mul] at this,
  apply nnreal.mul_ne_zero'; exact mt nnreal.rpow_eq_zero_iff.1 (mt and.left ‹_›)
end

theorem is_greatest_lp_nnreal (f : ι → ℝ≥0) (hpq : is_conjugate_exponent p q) :
  is_greatest ((λ g : ι → ℝ≥0, ∑ i in s, f i * g i) ''
    {g | ∑ i in s, (g i)^q ≤ 1}) ((∑ i in s, (f i)^p) ^ (1 / p)) :=
begin
  split,
  { use λ i, ((f i) ^ (p - 1) / (∑ i in s, (f i) ^ p) ^ (1 / q)),
    by_cases hf : ∑ i in s, (f i)^p = 0,
    { simp [hf, hpq.ne_zero, hpq.symm.ne_zero] },
    { use le_of_eq (s.lq_norm_conj_eq_one_nnreal hf hpq),
      have : ∀ y : ℝ≥0, y * y ^ (p - 1) = y ^ p,
      { have A : p = 1 + (p-1) := eq_add_of_sub_eq' rfl,
        have B : 1 + (p-1) ≠ 0 := A ▸ hpq.ne_zero,
        intro y,
        simpa using (y.rpow_add' B).symm },
      simp only [← mul_div_assoc'', ← nnreal.rpow_mul, ← nnreal.sum_div, this],
      generalize H : ∑ i in s, (f i)^p = r, rw H at hf,
      rw [nnreal.div_eq_iff, ← nnreal.rpow_add', hpq.inv_add_inv_conj, nnreal.rpow_one],
      { rw hpq.inv_add_inv_conj, exact one_ne_zero },
      { simp [hf] } } },
  { rintros _ ⟨g, hg, rfl⟩,
    apply le_trans (s.sum_mul_le_lp_mul_lq_nnreal f g hpq),
    simpa only [mul_one] using canonically_ordered_semiring.mul_le_mul (le_refl _)
      (nnreal.rpow_le_one hg (le_of_lt hpq.symm.one_div_pos)) }
end

theorem minkowskii_nnreal (hp : 1 < p) :
  (∑ i in s, (f i + g i) ^ p) ^ (1 / p) ≤
    (∑ i in s, (f i) ^ p) ^ (1 / p) + (∑ i in s, (g i) ^ p) ^ (1 / p) :=
begin
  have hpq := is_conjugate_exponent_conjugate_exponent hp,
  have := s.is_greatest_lp_nnreal (f + g) hpq,
  simp only [pi.add_apply, add_mul, sum_add_distrib] at this,
  rcases this.1 with ⟨φ, hφ, H⟩,
  rw ← H,
  exact add_le_add ((s.is_greatest_lp_nnreal f hpq).2 ⟨φ, hφ, rfl⟩)
    ((s.is_greatest_lp_nnreal g hpq).2 ⟨φ, hφ, rfl⟩)
end

end nnreal

variables (f g : ι → ℝ)  

theorem sum_mul_le_lp_mul_lq (hpq : is_conjugate_exponent p q) :
  ∑ i in s, f i * g i ≤ (∑ i in s, (abs $ f i)^p) ^ (1 / p) * (∑ i in s, (abs $ g i)^q) ^ (1 / q) :=
begin
  have := nnreal.coe_le_coe.2 (@sum_mul_le_lp_mul_lq_nnreal ι s p q
    (λ i, ⟨abs (f i), abs_nonneg (f i)⟩) (λ i, ⟨abs (g i), abs_nonneg (g i)⟩) hpq),
  push_cast at this,
  refine le_trans (sum_le_sum $ λ i hi, _) this,
  rw [← abs_mul],
  apply le_abs_self
end

end finset

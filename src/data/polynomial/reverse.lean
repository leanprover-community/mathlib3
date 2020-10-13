/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.degree.basic
import data.polynomial.erase_lead
import data.polynomial.degree.trailing_degree

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : polynomial R` produces the
polynomial with a reversed list of coefficients, equivalent to `X^f.nat_degree * f(1/X)`.

The main result is that `reverse (f * g) = reverse (f) * reverse (g)`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace polynomial

open polynomial finsupp finset

variables {R : Type*} [semiring R] {f : polynomial R}

namespace rev
/-- If `i ≤ N`, then `rev_at N i` returns `N - i`, otherwise it returns `i`.

Essentially, this function is only used for `i ≤ N`.
The advantage of `rev_at N i` over `N - i` is that `rev_at` is an involution.
-/
def rev_at (N i : ℕ) : ℕ := ite (i ≤ N) (N-i) i

@[simp] lemma rev_at_invol {N n : ℕ} : rev_at N (rev_at N n) = n :=
begin
  unfold rev_at,
  split_ifs with h j,
  { exact nat.sub_sub_self h, },
  { exfalso,
    apply j,
    exact nat.sub_le N n, },
  { refl, },
end

@[simp] lemma rev_at_small {N n : ℕ} (H : n ≤ N) : rev_at N n = N-n :=
if_pos H

/-- The function `reflect` of a natural number `N` and a polynomial `f`, applies the function
`rev_at` to the exponents of the terms appearing in the expansion of `f`.  In practice, `reflect`
is only used when `N` is at least as large as the degree of `f`.  Eventually, it will be used with
`N` exactly equal to the degree of `f`.  -/
def reflect : ℕ → polynomial R → polynomial R :=
 λ N : ℕ, λ f : polynomial R, ⟨ image (rev_at N)  (f.support), λ i : ℕ, f.coeff (rev_at N i),
 begin
  intro,
  rw mem_image,
  split,
  { intro h,
    rcases h with ⟨ a, ha, rfl⟩,
    rwa [rev_at_invol, ← mem_support_iff_coeff_ne_zero], },
  { intro,
    use (rev_at N a),
    rwa [rev_at_invol, eq_self_iff_true, and_true, mem_support_iff_coeff_ne_zero], },
end ⟩

@[simp] lemma reflect_zero {n : ℕ} : reflect n (0 : polynomial R) = 0 := rfl

@[simp] lemma reflect_zero_iff {N : ℕ} (f : polynomial R) :
 reflect N (f : polynomial R) = 0 ↔ f=0 :=
begin
  split,
  { intros a,
    injection a with f0 f1,
    rwa [image_eq_empty, support_eq_empty] at f0, },
  { intro a,
    rw [a, reflect_zero], },
end

@[simp] lemma reflect_add (f g : polynomial R) (n : ℕ) :
 reflect n (f + g) = reflect n f + reflect n g :=
begin
  ext1,
  refl,
end

@[simp] lemma reflect_smul (f : polynomial R) (r : R) (N : ℕ) :
 reflect N (C r * f) = C r * (reflect N f) :=
begin
  ext1,
  unfold reflect,
  rw [coeff_mk, coeff_C_mul, coeff_C_mul, coeff_mk],
end

@[simp] lemma reflect_C_mul_X_pow (N n : ℕ) {c : R} :
 reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext1 m,
  unfold reflect,
  rw coeff_mk,
  by_cases h : rev_at N n = m,
  { rw [h, coeff_C_mul, coeff_C_mul, coeff_X_pow_self, ← h, rev_at_invol, coeff_X_pow_self], },
  { rw not_mem_support_iff_coeff_zero.mp,
    { symmetry,
      apply not_mem_support_iff_coeff_zero.mp,
      intro,
      apply h,
      exact (mem_support_C_mul_X_pow a).symm, },
    { intro,
      apply h,
      rw ← @rev_at_invol N m,
      apply congr_arg _,
      exact (mem_support_C_mul_X_pow a).symm, }, },
end

@[simp] lemma reflect_monomial (N n : ℕ) : reflect N ((X : polynomial R) ^ n) = X ^ (rev_at N n) :=
by rw [← one_mul (X^n), ← one_mul (X^(rev_at N n)), ← C_1, reflect_C_mul_X_pow]

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, reverse f = f (1/X) * X ^ f.nat_degree. -/
def reverse : polynomial R → polynomial R := λ f, reflect f.nat_degree f

lemma pol_ind_Rhom_prod_on_card (cf cg : ℕ) {rp : ℕ → polynomial R → polynomial R}
 (rp_add  : ∀ f g : polynomial R, ∀ F : ℕ,
  rp F (f+g) = rp F f + rp F g)
 (rp_smul : ∀ f : polynomial R, ∀ r : R, ∀ F : ℕ,
  rp F ((C r)*f) = C r * rp F f)
 (rp_mon : ∀ N n : ℕ, n ≤ N →
  rp N (X^n) = X^(N-n)) :
 ∀ N O : ℕ, ∀ f g : polynomial R,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  have rp_zero : ∀ T : ℕ, rp T (0 : polynomial R) = 0,
  { intro,
    rw [← zero_mul (1 : polynomial R), ← C_0, rp_smul, C_0, zero_mul, zero_mul], },
  induction cf with cf hcf,
  --first induction: base case
  { induction cg with cg hcg,
    -- second induction: base case
    { intros N O f g Cf Cg Nf Og,
      rw [C_mul_X_pow_of_card_support_le_one Cf, C_mul_X_pow_of_card_support_le_one Cg],
      rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
      repeat {rw rp_smul},
      rw [rp_mon _ _ Nf, rp_mon _ _ Og, rp_mon],
      { rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
        congr,
        rcases (nat.le.dest Og) with ⟨ G, rfl ⟩,
        rcases (nat.le.dest Nf) with ⟨ F, rfl ⟩,
        repeat {rw nat.add_sub_cancel_left},
        rw [add_comm _ F, add_comm G F, add_assoc, nat.add_sub_assoc, ← add_assoc],
        rw [add_comm f.nat_degree _, add_comm (_+f.nat_degree) G, nat.add_sub_cancel],
        rw add_comm,
        exact add_le_add_left Og f.nat_degree, },
      { rw add_comm N O,
        exact add_le_add Og Nf, }, },
    -- second induction: induction step
    { intros N O f g Cf Cg Nf Og,
      by_cases g0 : g = 0,
      { rw [g0, mul_zero, rp_zero, rp_zero, mul_zero], },
      { rw [← erase_lead_add_C_mul_X_pow g, mul_add, rp_add, rp_add, mul_add],
        rw hcg N O f _ Cf _ Nf (le_trans erase_lead_nat_degree_le Og),
        rw hcg N O f _ Cf (le_add_left card_support_C_mul_X_pow_le_one) Nf _,
        { exact (le_trans (nat_degree_C_mul_X_pow_le g.leading_coeff g.nat_degree) Og), },
        { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cg (erase_lead_support_card_lt g0)), }, }, }, },
  --first induction: induction step
  { intros N O f g Cf Cg Nf Og,
    by_cases f0 : f=0,
    { rw [f0, zero_mul, rp_zero, rp_zero, zero_mul], },
    { rw [← erase_lead_add_C_mul_X_pow f, add_mul, rp_add, rp_add, add_mul],
      rw hcf N O _ g _ Cg (le_trans erase_lead_nat_degree_le Nf) Og,
      rw hcf N O _ g (le_add_left card_support_C_mul_X_pow_le_one) Cg _ Og,
      { exact (le_trans (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree) Nf), },
      { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cf (erase_lead_support_card_lt f0)), }, }, },
end

lemma pol_ind_Rhom_prod {rp : ℕ → polynomial R → polynomial R}
 (rp_add  : ∀ f g : polynomial R, ∀ F : ℕ,
  rp F (f+g) = rp F f + rp F g)
 (rp_smul : ∀ f : polynomial R, ∀ r : R, ∀ F : ℕ,
  rp F ((C r)*f) = C r * rp F f)
 (rp_mon : ∀ N n : ℕ, n ≤ N →
  rp N (X^n) = X^(N-n)) :
 ∀ N O : ℕ, ∀ f g : polynomial R,
 f.nat_degree ≤ N → g.nat_degree ≤ O →
 (rp (N + O) (f*g)) = (rp N f) * (rp O g) :=
begin
  intros _ _ f g,
  apply pol_ind_Rhom_prod_on_card f.support.card g.support.card rp_add rp_smul rp_mon,
  { exact (f.support).card.le_succ, },
  { exact (g.support).card.le_succ, },
end

@[simp] theorem reflect_mul
 {f g : polynomial R} {F G : ℕ} (Ff : f.nat_degree ≤ F) (Gg : g.nat_degree ≤ G) :
 reflect (F+G) (f*g) = reflect F f * reflect G g :=
begin
  apply pol_ind_Rhom_prod reflect_add reflect_smul _ F G f g Ff Gg,
  { intros N n Nn,
    rw [reflect_monomial, rev_at_small Nn], },
end

theorem reverse_mul (f g : polynomial R) {fg : f.leading_coeff*g.leading_coeff ≠ 0} :
 reverse (f*g) = reverse f * reverse g :=
begin
  unfold reverse,
  rw [nat_degree_mul' fg, reflect_mul (le_refl _) (le_refl _)],
end

end rev
end polynomial

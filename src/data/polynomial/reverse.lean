/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : polynomial R` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.nat_degree * f(1/X)`.

The main result is that `reverse (f * g) = reverse (f) * reverse (g)`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace polynomial

open polynomial finsupp finset
open_locale classical

variables {R : Type*} [semiring R] {f : polynomial R}

namespace rev
/-- If `i ≤ N`, then `rev_at_fun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `rev_at`.
-/
def rev_at_fun (N i : ℕ) : ℕ := ite (i ≤ N) (N-i) i

lemma rev_at_fun_invol {N i : ℕ} : rev_at_fun N (rev_at_fun N i) = i :=
begin
  unfold rev_at_fun,
  split_ifs with h j,
  { exact nat.sub_sub_self h, },
  { exfalso,
    apply j,
    exact nat.sub_le N i, },
  { refl, },
end

lemma rev_at_fun_inj {N : ℕ} : function.injective (rev_at_fun N) :=
begin
  intros a b hab,
  rw [← @rev_at_fun_invol N a, hab, rev_at_fun_invol],
end

/-- If `i ≤ N`, then `rev_at N i` returns `N - i`, otherwise it returns `i`.
Essentially, this embedding is only used for `i ≤ N`.
The advantage of `rev_at N i` over `N - i` is that `rev_at` is an involution.
-/
def rev_at (N : ℕ) : function.embedding ℕ ℕ :=
{ to_fun := λ i , (ite (i ≤ N) (N-i) i),
  inj' := rev_at_fun_inj }

/-- We prefer to use the bundled `rev_at` over unbundled `rev_at_fun`. -/
@[simp] lemma rev_at_fun_eq (N i : ℕ) : rev_at_fun N i = rev_at N i := rfl

@[simp] lemma rev_at_invol {N i : ℕ} : (rev_at N) (rev_at N i) = i :=
rev_at_fun_invol

@[simp] lemma rev_at_le {N i : ℕ} (H : i ≤ N) : rev_at N i = N - i :=
if_pos H

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (rev_at N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.  -/
noncomputable def reflect (N : ℕ) (f : polynomial R) : polynomial R :=
finsupp.emb_domain (rev_at N) f

lemma reflect_support (N : ℕ) (f : polynomial R) :
  (reflect N f).support = image (rev_at N) f.support :=
begin
  ext1,
  rw [reflect, mem_image, support_emb_domain, mem_map],
end

@[simp] lemma coeff_reflect (N : ℕ) (f : polynomial R) (i : ℕ) :
  coeff (reflect N f) i = f.coeff (rev_at N i) :=
calc finsupp.emb_domain (rev_at N) f i
    = finsupp.emb_domain (rev_at N) f (rev_at N (rev_at N i)) : by rw rev_at_invol
... = f.coeff (rev_at N i) : finsupp.emb_domain_apply _ _ _

@[simp] lemma reflect_zero {N : ℕ} : reflect N (0 : polynomial R) = 0 := rfl

@[simp] lemma reflect_eq_zero_iff {N : ℕ} {f : polynomial R} :
  reflect N (f : polynomial R) = 0 ↔ f = 0 :=
begin
  split,
  { intros a,
    injection a with f0 f1,
    rwa [map_eq_empty, support_eq_empty] at f0, },
  { rintro rfl,
    exact reflect_zero, },
end

@[simp] lemma reflect_add (f g : polynomial R) (N : ℕ) :
  reflect N (f + g) = reflect N f + reflect N g :=
by { ext1, rw [coeff_add, coeff_reflect, coeff_reflect, coeff_reflect, coeff_add], }

@[simp] lemma reflect_C_mul (f : polynomial R) (r : R) (N : ℕ) :
  reflect N (C r * f) = C r * (reflect N f) :=
by { ext1, rw [coeff_reflect, coeff_C_mul, coeff_C_mul, coeff_reflect], }

@[simp] lemma reflect_C_mul_X_pow (N n : ℕ) {c : R} :
  reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext,
  rw [reflect_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_reflect],
  split_ifs,
  { rw [h, rev_at_invol, coeff_X_pow_self], },
  { rw [not_mem_support_iff_coeff_zero.mp],
    intro a,
    rw [← one_mul (X ^ n), ← C_1] at a,
    apply h,
    rw [← (mem_support_C_mul_X_pow a), rev_at_invol], },
end

@[simp] lemma reflect_monomial (N n : ℕ) : reflect N ((X : polynomial R) ^ n) = X ^ (rev_at N n) :=
by rw [← one_mul (X ^ n), ← one_mul (X ^ (rev_at N n)), ← C_1, reflect_C_mul_X_pow]

lemma reflect_mul_induction (cf cg : ℕ) :
 ∀ N O : ℕ, ∀ f g : polynomial R,
 f.support.card ≤ cf.succ → g.support.card ≤ cg.succ → f.nat_degree ≤ N → g.nat_degree ≤ O →
 (reflect (N + O) (f * g)) = (reflect N f) * (reflect O g) :=
begin
  induction cf with cf hcf,
  --first induction: base case
  { induction cg with cg hcg,
    -- second induction: base case
    { intros N O f g Cf Cg Nf Og,
      rw [C_mul_X_pow_of_card_support_le_one Cf, C_mul_X_pow_of_card_support_le_one Cg],
      rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
      repeat {rw reflect_C_mul},
      repeat {rw reflect_monomial},
      { rw [mul_assoc, X_pow_mul, mul_assoc, ← pow_add X],
        congr,
        rcases (nat.le.dest Og) with ⟨ G, rfl ⟩,
        rcases (nat.le.dest Nf) with ⟨ F, rfl ⟩,
        repeat {rw nat.add_sub_cancel_left},
        repeat {rw rev_at_le},
        { rw [← add_assoc, add_assoc _ F, add_comm F, ← add_assoc, add_assoc _ F],
          rw [add_comm f.nat_degree, add_comm F],
          repeat {rw nat.add_sub_cancel_left}, },
        { exact le_add_right (le_refl _), },
        { exact le_add_right (le_refl _), },
        { rw ← add_assoc (_ + F),
          rw add_comm _ g.nat_degree,
          rw ← add_assoc,
          rw add_assoc,
          exact nat.le_add_right _ _, }, }, },
    -- second induction: induction step
    { intros N O f g Cf Cg Nf Og,
      by_cases g0 : g = 0,
      { rw [g0, mul_zero, reflect_zero, reflect_zero, mul_zero], },
      { rw [← erase_lead_add_C_mul_X_pow g, mul_add, reflect_add, reflect_add, mul_add],
        rw hcg N O f _ Cf _ Nf (le_trans erase_lead_nat_degree_le Og),
        rw hcg N O f _ Cf (le_add_left card_support_C_mul_X_pow_le_one) Nf _,
        { exact (le_trans (nat_degree_C_mul_X_pow_le g.leading_coeff g.nat_degree) Og), },
        { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cg (erase_lead_support_card_lt g0)), }, }, }, },
  --first induction: induction step
  { intros N O f g Cf Cg Nf Og,
    by_cases f0 : f=0,
    { rw [f0, zero_mul, reflect_zero, reflect_zero, zero_mul], },
    { rw [← erase_lead_add_C_mul_X_pow f, add_mul, reflect_add, reflect_add, add_mul],
      rw hcf N O _ g _ Cg (le_trans erase_lead_nat_degree_le Nf) Og,
      rw hcf N O _ g (le_add_left card_support_C_mul_X_pow_le_one) Cg _ Og,
      { exact (le_trans (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree) Nf), },
      { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cf (erase_lead_support_card_lt f0)), }, }, },
end

@[simp] theorem reflect_mul
  {f g : polynomial R} {F G : ℕ} (Ff : f.nat_degree ≤ F) (Gg : g.nat_degree ≤ G) :
  reflect (F + G) (f * g) = reflect F f * reflect G g :=
reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, reverse f = f (1/X) * X ^ f.nat_degree. -/
noncomputable def reverse (f : polynomial R) : polynomial R := reflect f.nat_degree f

@[simp] lemma reverse_zero : reverse (0 : polynomial R) = 0 := rfl

theorem reverse_mul {f g : polynomial R} (fg : f.leading_coeff * g.leading_coeff ≠ 0) :
 reverse (f * g) = reverse f * reverse g :=
begin
  unfold reverse,
  rw [nat_degree_mul' fg, reflect_mul (le_refl _) (le_refl _)],
end

@[simp] lemma reverse_mul_of_domain {R : Type*} [domain R] (f g : polynomial R) :
  reverse (f * g) = reverse f * reverse g :=
begin
  by_cases f0 : f=0,
  { rw [f0, zero_mul, reverse_zero, zero_mul], },
  by_cases g0 : g=0,
  { rw [g0, mul_zero, reverse_zero, mul_zero], },
  apply reverse_mul,
  apply mul_ne_zero;
    rwa [← leading_coeff_eq_zero] at *
end

end rev
end polynomial

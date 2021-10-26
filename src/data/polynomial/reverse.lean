/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead
import data.polynomial.eval

/-!
# Reverse of a univariate polynomial

The main definition is `reverse`.  Applying `reverse` to a polynomial `f : polynomial R` produces
the polynomial with a reversed list of coefficients, equivalent to `X^f.nat_degree * f(1/X)`.

The main result is that `reverse (f * g) = reverse f * reverse g`, provided the leading
coefficients of `f` and `g` do not multiply to zero.
-/

namespace polynomial

open polynomial finsupp finset
open_locale classical

section semiring

variables {R : Type*} [semiring R] {f : polynomial R}

/-- If `i ≤ N`, then `rev_at_fun N i` returns `N - i`, otherwise it returns `i`.
This is the map used by the embedding `rev_at`.
-/
def rev_at_fun (N i : ℕ) : ℕ := ite (i ≤ N) (N-i) i

lemma rev_at_fun_invol {N i : ℕ} : rev_at_fun N (rev_at_fun N i) = i :=
begin
  unfold rev_at_fun,
  split_ifs with h j,
  { exact tsub_tsub_cancel_of_le h, },
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

lemma rev_at_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
  rev_at (N + O) (n + o) = rev_at N n + rev_at O o :=
begin
  rcases nat.le.dest hn with ⟨n', rfl⟩,
  rcases nat.le.dest ho with ⟨o', rfl⟩,
  repeat { rw rev_at_le (le_add_right rfl.le) },
  rw [add_assoc, add_left_comm n' o, ← add_assoc, rev_at_le (le_add_right rfl.le)],
  repeat {rw add_tsub_cancel_left},
end

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (rev_at N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.  -/
noncomputable def reflect (N : ℕ) : polynomial R → polynomial R
| ⟨f⟩ := ⟨finsupp.emb_domain (rev_at N) f⟩

lemma reflect_support (N : ℕ) (f : polynomial R) :
  (reflect N f).support = image (rev_at N) f.support :=
begin
  rcases f,
  ext1,
  rw [reflect, mem_image, support, support, support_emb_domain, mem_map],
end

@[simp] lemma coeff_reflect (N : ℕ) (f : polynomial R) (i : ℕ) :
  coeff (reflect N f) i = f.coeff (rev_at N i) :=
begin
  rcases f,
  simp only [reflect, coeff],
  calc finsupp.emb_domain (rev_at N) f i
      = finsupp.emb_domain (rev_at N) f (rev_at N (rev_at N i)) : by rw rev_at_invol
  ... = f (rev_at N i) : finsupp.emb_domain_apply _ _ _
end

@[simp] lemma reflect_zero {N : ℕ} : reflect N (0 : polynomial R) = 0 := rfl

@[simp] lemma reflect_eq_zero_iff {N : ℕ} {f : polynomial R} :
  reflect N (f : polynomial R) = 0 ↔ f = 0 :=
by { rcases f, simp [reflect, ← zero_to_finsupp] }

@[simp] lemma reflect_add (f g : polynomial R) (N : ℕ) :
  reflect N (f + g) = reflect N f + reflect N g :=
by { ext, simp only [coeff_add, coeff_reflect], }

@[simp] lemma reflect_C_mul (f : polynomial R) (r : R) (N : ℕ) :
  reflect N (C r * f) = C r * (reflect N f) :=
by { ext, simp only [coeff_reflect, coeff_C_mul], }

@[simp] lemma reflect_C_mul_X_pow (N n : ℕ) {c : R} :
  reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext,
  rw [reflect_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_reflect],
  split_ifs with h j,
  { rw [h, rev_at_invol, coeff_X_pow_self], },
  { rw [not_mem_support_iff.mp],
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
  --first induction (left): base case
  { induction cg with cg hcg,
    -- second induction (right): base case
    { intros N O f g Cf Cg Nf Og,
      rw [← C_mul_X_pow_eq_self Cf, ← C_mul_X_pow_eq_self Cg],
      simp only [mul_assoc, X_pow_mul, ← pow_add X, reflect_C_mul, reflect_monomial,
                 add_comm, rev_at_add Nf Og] },
    -- second induction (right): induction step
    { intros N O f g Cf Cg Nf Og,
      by_cases g0 : g = 0,
      { rw [g0, reflect_zero, mul_zero, mul_zero, reflect_zero], },

      rw [← erase_lead_add_C_mul_X_pow g, mul_add, reflect_add, reflect_add, mul_add, hcg, hcg];
        try { assumption },
      { exact le_add_left card_support_C_mul_X_pow_le_one },
      { exact (le_trans (nat_degree_C_mul_X_pow_le g.leading_coeff g.nat_degree) Og) },
      { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cg (erase_lead_support_card_lt g0)) },
      { exact le_trans erase_lead_nat_degree_le Og } } },
  --first induction (left): induction step
  { intros N O f g Cf Cg Nf Og,
    by_cases f0 : f = 0,
    { rw [f0, reflect_zero, zero_mul, zero_mul, reflect_zero], },

    rw [← erase_lead_add_C_mul_X_pow f, add_mul, reflect_add, reflect_add, add_mul, hcf, hcf];
       try { assumption },
    { exact le_add_left card_support_C_mul_X_pow_le_one },
    { exact (le_trans (nat_degree_C_mul_X_pow_le f.leading_coeff f.nat_degree) Nf) },
    { exact nat.lt_succ_iff.mp (gt_of_ge_of_gt Cf (erase_lead_support_card_lt f0)) },
    { exact (le_trans erase_lead_nat_degree_le Nf) } },
end

@[simp] theorem reflect_mul
  (f g : polynomial R) {F G : ℕ} (Ff : f.nat_degree ≤ F) (Gg : g.nat_degree ≤ G) :
  reflect (F + G) (f * g) = reflect F f * reflect G g :=
reflect_mul_induction _ _ F G f g f.support.card.le_succ g.support.card.le_succ Ff Gg

/-- The reverse of a polynomial f is the polynomial obtained by "reading f backwards".
Even though this is not the actual definition, reverse f = f (1/X) * X ^ f.nat_degree. -/
noncomputable def reverse (f : polynomial R) : polynomial R := reflect f.nat_degree f

lemma coeff_reverse (f : polynomial R) (n : ℕ) :
  f.reverse.coeff n = f.coeff (rev_at f.nat_degree n) :=
by rw [reverse, coeff_reflect]

@[simp] lemma coeff_zero_reverse (f : polynomial R) : coeff (reverse f) 0 = leading_coeff f :=
by rw [coeff_reverse, rev_at_le (zero_le f.nat_degree), tsub_zero, leading_coeff]

@[simp] lemma reverse_zero : reverse (0 : polynomial R) = 0 := rfl

@[simp] lemma reverse_eq_zero : f.reverse = 0 ↔ f = 0 :=
by simp [reverse]

lemma reverse_nat_degree_le (f : polynomial R) : f.reverse.nat_degree ≤ f.nat_degree :=
begin
  rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero],
  intros n hn,
  rw with_bot.coe_lt_coe at hn,
  rw [coeff_reverse, rev_at, function.embedding.coe_fn_mk,
      if_neg (not_le_of_gt hn), coeff_eq_zero_of_nat_degree_lt hn],
end

lemma nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree (f : polynomial R) :
  f.nat_degree = f.reverse.nat_degree + f.nat_trailing_degree :=
begin
  by_cases hf : f = 0,
  { rw [hf, reverse_zero, nat_degree_zero, nat_trailing_degree_zero] },
  apply le_antisymm,
  { refine tsub_le_iff_right.mp _,
    apply le_nat_degree_of_ne_zero,
    rw [reverse, coeff_reflect, ←rev_at_le f.nat_trailing_degree_le_nat_degree, rev_at_invol],
    exact trailing_coeff_nonzero_iff_nonzero.mpr hf },
  { rw ← le_tsub_iff_left f.reverse_nat_degree_le,
    apply nat_trailing_degree_le_of_ne_zero,
    have key := mt leading_coeff_eq_zero.mp (mt reverse_eq_zero.mp hf),
    rwa [leading_coeff, coeff_reverse, rev_at_le f.reverse_nat_degree_le] at key },
end

lemma reverse_nat_degree (f : polynomial R) :
  f.reverse.nat_degree = f.nat_degree - f.nat_trailing_degree :=
by rw [f.nat_degree_eq_reverse_nat_degree_add_nat_trailing_degree, add_tsub_cancel_right]

lemma reverse_leading_coeff (f : polynomial R) : f.reverse.leading_coeff = f.trailing_coeff :=
by rw [leading_coeff, reverse_nat_degree, ←rev_at_le f.nat_trailing_degree_le_nat_degree,
  coeff_reverse, rev_at_invol, trailing_coeff]

lemma reverse_nat_trailing_degree  (f : polynomial R) : f.reverse.nat_trailing_degree = 0 :=
begin
  by_cases hf : f = 0,
  { rw [hf, reverse_zero, nat_trailing_degree_zero] },
  { rw ← nat.le_zero_iff,
    apply nat_trailing_degree_le_of_ne_zero,
    rw [coeff_zero_reverse],
    exact mt leading_coeff_eq_zero.mp hf },
end

lemma reverse_trailing_coeff (f : polynomial R) : f.reverse.trailing_coeff = f.leading_coeff :=
by rw [trailing_coeff, reverse_nat_trailing_degree, coeff_zero_reverse]

theorem reverse_mul {f g : polynomial R} (fg : f.leading_coeff * g.leading_coeff ≠ 0) :
 reverse (f * g) = reverse f * reverse g :=
begin
  unfold reverse,
  rw [nat_degree_mul' fg, reflect_mul  f g rfl.le rfl.le],
end

@[simp] lemma reverse_mul_of_domain {R : Type*} [ring R] [is_domain R] (f g : polynomial R) :
  reverse (f * g) = reverse f * reverse g :=
begin
  by_cases f0 : f=0,
  { simp only [f0, zero_mul, reverse_zero], },
  by_cases g0 : g=0,
  { rw [g0, mul_zero, reverse_zero, mul_zero], },
  simp [reverse_mul, *],
end

lemma trailing_coeff_mul {R : Type*} [ring R] [is_domain R] (p q : polynomial R) :
  (p * q).trailing_coeff = p.trailing_coeff * q.trailing_coeff :=
by rw [←reverse_leading_coeff, reverse_mul_of_domain, leading_coeff_mul,
  reverse_leading_coeff, reverse_leading_coeff]

@[simp] lemma coeff_one_reverse (f : polynomial R) : coeff (reverse f) 1 = next_coeff f :=
begin
  rw [coeff_reverse, next_coeff],
  split_ifs with hf,
  { have : coeff f 1 = 0 := coeff_eq_zero_of_nat_degree_lt (by simp only [hf, zero_lt_one]),
    simp [*, rev_at] },
  { rw rev_at_le,
    exact nat.succ_le_iff.2 (pos_iff_ne_zero.2 hf) }
end

end semiring

section ring

variables {R : Type*} [ring R]

@[simp] lemma reflect_neg (f : polynomial R) (N : ℕ) :
  reflect N (- f) = - reflect N f :=
by rw [neg_eq_neg_one_mul, ←C_1, ←C_neg, reflect_C_mul, C_neg, C_1, ←neg_eq_neg_one_mul]

@[simp] lemma reflect_sub (f g : polynomial R) (N : ℕ) :
  reflect N (f - g) = reflect N f - reflect N g :=
by rw [sub_eq_add_neg, sub_eq_add_neg, reflect_add, reflect_neg]

@[simp] lemma reverse_neg (f : polynomial R) :
  reverse (- f) = - reverse f :=
by rw [reverse, reverse, reflect_neg, nat_degree_neg]

end ring

end polynomial

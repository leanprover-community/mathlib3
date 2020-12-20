/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead
import data.polynomial.degree

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

lemma rev_at_add {N O n o : ℕ} (hn : n ≤ N) (ho : o ≤ O) :
  rev_at (N + O) (n + o) = rev_at N n + rev_at O o :=
begin
  rcases nat.le.dest hn with ⟨n', rfl⟩,
  rcases nat.le.dest ho with ⟨o', rfl⟩,
  repeat { rw rev_at_le (le_add_right rfl.le) },
  rw [add_assoc, add_left_comm n' o, ← add_assoc, rev_at_le (le_add_right rfl.le)],
  repeat {rw nat.add_sub_cancel_left},
end

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
    refl, },
end

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

@[simp] lemma reverse_zero : reverse (0 : polynomial R) = 0 := rfl

theorem reverse_mul {f g : polynomial R} (fg : f.leading_coeff * g.leading_coeff ≠ 0) :
 reverse (f * g) = reverse f * reverse g :=
begin
  unfold reverse,
  rw [nat_degree_mul' fg, reflect_mul  f g rfl.le rfl.le],
end

@[simp] lemma reverse_mul_of_domain {R : Type*} [domain R] (f g : polynomial R) :
  reverse (f * g) = reverse f * reverse g :=
begin
  by_cases f0 : f=0,
  { simp only [f0, zero_mul, reverse_zero], },
  by_cases g0 : g=0,
  { rw [g0, mul_zero, reverse_zero, mul_zero], },
  simp [reverse_mul, *],
end

@[simp] lemma coeff_zero_reverse (f : polynomial R) : coeff (reverse f) 0 = leading_coeff f :=
by simp [reverse, coeff_reflect]

@[simp] lemma coeff_one_reverse (f : polynomial R) : coeff (reverse f) 1 = next_coeff f :=
begin
  rw [reverse, coeff_reflect, next_coeff],
  split_ifs with hf,
  { have : coeff f 1 = 0 := coeff_eq_zero_of_nat_degree_lt (by simp only [hf, zero_lt_one]),
    simp [*, rev_at] },
  { rw rev_at_le,
    exact nat.succ_le_iff.2 (zero_lt_iff_ne_zero.2 hf) }
end

end polynomial

/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import data.polynomial.erase_lead
import data.polynomial.degree.trailing_degree
import data.polynomial.to_finset

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
  { exact nat.sub_sub_self h, },
  { exfalso,
    apply j,
    exact nat.sub_le N i, },
  { refl, },
end

lemma rev_at_fun_inj {N : ℕ} : function.injective (rev_at_fun N) :=
λ a b hab, by rw [← @rev_at_fun_invol N a, hab, rev_at_fun_invol]

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
  repeat { rw rev_at_le (le_add_right rfl.le), },
  rw [add_assoc, add_left_comm n' o, ← add_assoc, rev_at_le (le_add_right rfl.le)],
  repeat { rw nat.add_sub_cancel_left },
end

/-- `reflect N f` is the polynomial such that `(reflect N f).coeff i = f.coeff (rev_at N i)`.
In other words, the terms with exponent `[0, ..., N]` now have exponent `[N, ..., 0]`.

In practice, `reflect` is only used when `N` is at least as large as the degree of `f`.

Eventually, it will be used with `N` exactly equal to the degree of `f`.  -/
noncomputable def reflect (N : ℕ) (f : polynomial R) : polynomial R :=
finsupp.emb_domain (rev_at N) f

lemma reflect_support (N : ℕ) (f : polynomial R) :
  (reflect N f).support = image (rev_at N) f.support :=
by refine finset.ext (λ (a : ℕ), (by rw [reflect, mem_image, support_emb_domain, mem_map]))

@[simp] lemma coeff_reflect (N : ℕ) (f : polynomial R) (i : ℕ) :
  coeff (reflect N f) i = f.coeff (rev_at N i) :=
calc finsupp.emb_domain (rev_at N) f i
    = finsupp.emb_domain (rev_at N) f (rev_at N (rev_at N i)) : by rw rev_at_invol
... = f.coeff (rev_at N i) : finsupp.emb_domain_apply _ _ _

@[simp] lemma reflect_zero {N : ℕ} : reflect N (0 : polynomial R) = 0 := rfl

@[simp] lemma reflect_eq_zero_iff {N : ℕ} {f : polynomial R} :
  reflect N (f : polynomial R) = 0 ↔ f = 0 :=
by refine ⟨(λ a, by rwa [reflect, emb_domain_eq_zero] at a), by { rintro rfl, refl }⟩

@[simp] lemma reflect_add (f g : polynomial R) (N : ℕ) :
  reflect N (f + g) = reflect N f + reflect N g :=
by { ext1, rw [coeff_add, coeff_reflect, coeff_reflect, coeff_reflect, coeff_add], }

@[simp] lemma reflect_C_mul (f : polynomial R) (r : R) (N : ℕ) :
  reflect N (C r * f) = C r * (reflect N f) :=
by refine ext (λ (n : ℕ), by rw [coeff_reflect, coeff_C_mul, coeff_C_mul, coeff_reflect])

@[simp] lemma reflect_C_mul_X_pow (N n : ℕ) {c : R} :
  reflect N (C c * X ^ n) = C c * X ^ (rev_at N n) :=
begin
  ext,
  rw [reflect_C_mul, coeff_C_mul, coeff_C_mul, coeff_X_pow, coeff_reflect],
  split_ifs,
  { rw [h, rev_at_invol, coeff_X_pow_self], },
  { rw not_mem_support_iff_coeff_zero.mp,
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
by rw [reverse, reverse, reverse, nat_degree_mul' fg, reflect_mul  f g rfl.le rfl.le]

@[simp] lemma reverse_mul_of_domain {R : Type*} [domain R] (f g : polynomial R) :
  reverse (f * g) = reverse f * reverse g :=
begin
  by_cases f0 : f=0,
  { rw [f0, zero_mul, reverse_zero, zero_mul], },
  by_cases g0 : g=0,
  { rw [g0, mul_zero, reverse_zero, mul_zero], },
  apply reverse_mul,
  apply mul_ne_zero;
  { rwa [← leading_coeff_eq_zero] at *, },
end

lemma reflect_ne_zero_iff {N : ℕ} {f : polynomial R} :
  reflect N (f : polynomial R) ≠ 0 ↔ f ≠ 0 :=
not_congr reflect_eq_zero_iff

@[simp] lemma rev_at_gt {N n : ℕ} (H : N < n) : rev_at N n = n :=
if_neg (not_le.mpr H)

@[simp] lemma reflect_invol (N : ℕ) : reflect N (reflect N f) = f :=
by refine ext (λ (n : ℕ), by rw [coeff_reflect, coeff_reflect, rev_at_invol])

/-- `monotone_rev_at N _` coincides with `rev_at N _` in the range [0,..,N].  I use
`monotone_rev_at` just to show that `rev_at` exchanges `min`s and `max`s.  With an alternative
proof of the exchange property that does not use this definition, it can be removed! -/
def monotone_rev_at (N : ℕ) : ℕ → ℕ := λ i : ℕ , (N-i)

lemma monotone_rev_at_monotone (N : ℕ) : mon (monotone_rev_at N) :=
begin
  intros x y hxy,
  rw [monotone_rev_at, nat.sub_le_iff],
  by_cases xle : x ≤ N,
  { rwa nat.sub_sub_self xle, },
  rw not_le at xle,
  apply le_of_lt,
  convert gt_of_ge_of_gt hxy xle,
  convert nat.sub_zero N,
  exact nat.sub_eq_zero_iff_le.mpr (le_of_lt xle),
end

lemma monotone_rev_at_max'_min' {N : ℕ} {s : finset ℕ} {hs : s.nonempty} :
  max' (image (monotone_rev_at N) s) (nonempty.image hs (monotone_rev_at N)) =
  monotone_rev_at N (min' s hs) :=
monotone_max'_min' hs (monotone_rev_at_monotone N)

@[simp] lemma monotone_rev_at_eq_rev_at_small {N n : ℕ} :
  (n ≤ N) → rev_at N n = monotone_rev_at N n :=
λ H, by convert (@rev_at_le N n H)

lemma rev_at_small_min_max {N : ℕ} {s : finset ℕ} {hs : s.nonempty} (sm : s.max' hs ≤ N) :
  max' (image (rev_at N) s) (nonempty.image hs (rev_at N)) = rev_at N (min' s hs) :=
begin
  rwa [monotone_rev_at_eq_rev_at_small (le_trans (le_max' _ _ (min'_mem s hs)) sm),
    ← monotone_rev_at_max'_min'],
  have im : (image (rev_at N) s) = (image (monotone_rev_at N) s) →
    (image (rev_at N) s).max' (nonempty.image hs (rev_at N)) = (image (monotone_rev_at N) s).max'
    (nonempty.image hs (monotone_rev_at N)) := λ a, (by {congr, exact a}),
  apply im,
  ext1 a,
  repeat { rw mem_image },
  refine ⟨_ , _⟩;
  { rintro ⟨a, ha, rfl⟩ ,
    refine ⟨a, ha, by rw (monotone_rev_at_eq_rev_at_small (le_trans (le_max' _ _ ha) sm)) ⟩, },
end

lemma nat_degree_reflect_eq_nat_trailing_degree {N : ℕ} (f0 : f ≠ 0) (H : f.nat_degree ≤ N) :
  (reflect N f).nat_degree = rev_at N f.nat_trailing_degree :=
begin
  rw nat_degree_eq_support_max' (reflect_ne_zero_iff.mpr f0),
  rw [nat_trailing_degree_eq_support_min' f0],
  simp_rw [reflect, finsupp.support_emb_domain, map_eq_image],
  refine rev_at_small_min_max (by rwa ← nat_degree_eq_support_max' f0),
end

namespace rev

lemma nat_degree_reflect_le {N : ℕ} : (reflect N f).nat_degree ≤ max N f.nat_degree :=
begin
  by_cases f0 : f=0,
  { rw [f0, reflect_zero, nat_degree_zero], exact zero_le (max N 0), },
  by_cases dsm : f.nat_degree ≤ N,
  { rw [nat_degree_reflect_eq_nat_trailing_degree f0 dsm, max_eq_left dsm],
    rw rev_at_le (le_trans nat_trailing_degree_le_nat_degree dsm),
    exact (nat.sub_le N f.nat_trailing_degree), },
  { rw [not_le, lt_iff_le_and_ne] at dsm,
    rw [max_eq_right (dsm.1), nat_degree_eq_support_max', nat_degree_eq_support_max' f0],
    { apply max'_le,
      intros y hy,
      rw [reflect_support, mem_image] at hy,
      rcases hy with ⟨ y , hy , rfl ⟩,
      rw ← nat_degree_eq_support_max',
      by_cases ys : y ≤ N,
      { rw rev_at_le ys, exact (le_trans (nat.sub_le N y) dsm.1), },
      { rw rev_at_gt (not_le.mp ys), exact le_nat_degree_of_mem_supp _ hy, }, },
    { rwa [ne.def, (@reflect_eq_zero_iff R _ N f)], }, },
end

@[simp] lemma reverse_invol (h : f.coeff 0 ≠ 0) : reverse (reverse f) = f :=
begin
  rw [reverse, reverse, nat_degree_reflect_eq_nat_trailing_degree _ rfl.le],
  { rw [rev_at_le nat_trailing_degree_le_nat_degree, nat_trailing_degree_eq_zero h, nat.sub_zero,
      reflect_invol], },
  { intro f0, apply h, rw [f0, coeff_zero], },
end


lemma lead_reflect_eq_trailing (N : ℕ) (H : f.nat_degree ≤ N) :
  leading_coeff (reflect N f) = trailing_coeff f :=
begin
  by_cases f0 : f = 0,
  { rw [f0, reflect_zero, leading_coeff, trailing_coeff, coeff_zero, coeff_zero], },
  rw [leading_coeff, trailing_coeff, nat_trailing_degree_eq_support_min' f0],
  rw nat_degree_eq_support_max' (reflect_ne_zero_iff.mpr f0),
  simp_rw [coeff_reflect, reflect_support],
  rw [rev_at_small_min_max, rev_at_invol],
  convert H,
  rw nat_degree_eq_support_max',
end

lemma trailing_reflect_eq_lead (N : ℕ) (H : f.nat_degree ≤ N) :
  trailing_coeff (reflect N f) = leading_coeff f :=
begin
  conv_rhs { rw ← @reflect_invol R _ f N },
  rw lead_reflect_eq_trailing,
  convert @nat_degree_reflect_le R _ f N,
  rwa max_eq_left,
end

lemma nat_trailing_degree_reflect_eq_nat_degree {N : ℕ} (f0 : f ≠ 0) (H : f.nat_degree ≤ N) :
  (reflect N f).nat_trailing_degree = rev_at N f.nat_degree :=
begin
  conv_rhs { rw ← @reflect_invol R _ f N },
  rw [nat_degree_reflect_eq_nat_trailing_degree (reflect_ne_zero_iff.mpr f0), rev_at_invol],
  apply le_trans nat_degree_reflect_le _,
  rw max_eq_left H,
end

lemma lead_reverse_eq_trailing (f : polynomial R) : leading_coeff (reverse f) = trailing_coeff f :=
lead_reflect_eq_trailing _ rfl.le

lemma trailing_reverse_eq_lead (f : polynomial R) : trailing_coeff (reverse f) = leading_coeff f :=
trailing_reflect_eq_lead _ rfl.le

end rev

end semiring

section integral_domain

open rev

variables {R : Type*} [integral_domain R] {p q : polynomial R}

@[simp] lemma trailing_coeff_mul (p q : polynomial R)  : trailing_coeff (p * q) =
  trailing_coeff p * trailing_coeff q :=
begin
  by_cases p0 : p = 0,
  { rw [p0, zero_mul], convert (zero_mul q.trailing_coeff).symm, },
  by_cases q0 : q = 0,
  { rw [q0, mul_zero], convert (mul_zero p.trailing_coeff).symm, },
  rw [← @reflect_invol R _ (p * q) (p.nat_degree + q.nat_degree), trailing_reflect_eq_lead],
  { rw [reflect_mul p q rfl.le rfl.le, leading_coeff_mul],
    rw [← trailing_reflect_eq_lead p.nat_degree, reflect_invol],
    { rw [← trailing_reflect_eq_lead q.nat_degree, reflect_invol],
      convert @nat_degree_reflect_le R _ q q.nat_degree,
      rw max_eq_left rfl.le, },
    { convert @nat_degree_reflect_le R _ p p.nat_degree,
      exact (max_eq_left rfl.le).symm, }, },
  { convert nat_degree_reflect_le,
    exact (max_eq_left nat_degree_mul_le).symm, },
end

/-- `polynomial.trailing_coeff` bundled as a `monoid_hom` when `R` is an `integral_domain`, and thus
  `trailing_coeff` is multiplicative -/
noncomputable def trailing_coeff_hom : polynomial R →* R :=
{ to_fun := trailing_coeff,
  map_one' := trailing_coeff_one,
  map_mul' := trailing_coeff_mul }

@[simp] lemma trailing_coeff_hom_apply (p : polynomial R) :
  trailing_coeff_hom p = trailing_coeff p := rfl

@[simp] lemma trailing_coeff_pow (p : polynomial R) (n : ℕ) :
  trailing_coeff (p ^ n) = trailing_coeff p ^ n :=
trailing_coeff_hom.map_pow p n

end integral_domain

end polynomial

/-
Copyleft. No rights reserved.
Authors: Johan Commelin
-/

import field_theory.finite.basic
import field_theory.separable
import linear_algebra.finite_dimensional

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

-/

noncomputable theory

-- move this
section
open function
variables {K L : Type*} [field K] [field L]

lemma ring_hom.char_p_iff (f : K →+* L) (p : ℕ) :
  char_p K p ↔ char_p L p :=
begin
  split; introI; constructor; intro n,
  { rw [← f.map_nat_cast, f.map_eq_zero],
    apply char_p.cast_eq_zero_iff },
  { rw [← f.injective.eq_iff, f.map_nat_cast, f.map_zero],
    apply char_p.cast_eq_zero_iff }
end

variables (K L) [algebra K L]

lemma algebra.char_p_iff (p : ℕ) :
  char_p K p ↔ char_p L p :=
(algebra_map K L).char_p_iff p

end

open polynomial

lemma galois_poly_separable {K : Type*} [field K] (p q : ℕ) [char_p K p] (h : p ∣ q) :
  separable (X ^ q - X : polynomial K) :=
begin
  use [1, (X ^ q - X - 1)],
  rw [← char_p.cast_eq_zero_iff (polynomial K) p] at h,
  rw [derivative_sub, derivative_pow, derivative_X, h],
  ring,
end

section splitting_field_facts

variables {K : Type*} {L : Type*} [field K] [field L] {f : polynomial K}

lemma exists_finset_of_splits (i : K →+* L) (sep : separable f) : splits i f →
  ∃ (s : finset L), f.map i = C (i f.leading_coeff) *
  (s.prod (λ a : L, (X : polynomial L) - C a)) :=
begin
  classical,
  intro sp, cases exists_multiset_of_splits i sp with s h, use s.to_finset, rw h,
  rw finset.prod_eq_multiset_prod, rw ← multiset.to_finset_eq,
  apply nodup_of_separable_prod,
  apply separable.of_mul_right,
  rw ←h,
  exact sep.map,
end

open_locale big_operators
variables {α : Type*} (s : finset α) (g : α → polynomial K)

-- I have a proof in another project, hope to PR soon - Aaron Anderson
lemma nat_degree_prod_eq' (h : ∏ i in s, (g i).leading_coeff ≠ 0) :
  (s.prod g).nat_degree = ∑ i in s, (g i).nat_degree :=
begin
  rw finset.prod_ne_zero_iff at h,
  rw nat_degree_prod,
  intros i hi hgi,
  apply h i hi,
  rw [hgi, polynomial.leading_coeff_zero],
end

lemma card_roots_eq_of_separable_of_splits
  (sep : separable f) (sp : polynomial.splits (ring_hom.id K) f) :
  f.roots.card = f.nat_degree :=
begin
  classical,
  have hf : f ≠ 0, { rintro rfl, exact not_separable_zero sep },
  have hflc : f.leading_coeff ≠ 0, { rwa [ne.def, leading_coeff_eq_zero] },
  cases (exists_finset_of_splits (ring_hom.id K) sep sp) with s hs,
  simp only [ring_hom.id_apply, map_id] at hs, rw hs,
  rw [roots_C_mul _ hflc, roots_prod_X_sub_C, nat_degree_C_mul_eq_of_no_zero_divisors hflc],
  rw nat_degree_prod_eq',
  { simp only [mul_one, nat_degree_X_sub_C, nat.cast_id, finset.sum_const, nsmul_eq_mul,
      finset.card_def], },
  { simp only [(monic_X_sub_C _).leading_coeff, finset.prod_const_one,
                ne.def, not_false_iff, one_ne_zero] }
end

-- linter complains, but removing causes `instance : fintype (galois_field p n)` below to fail
instance is_splitting_field.finite_dimensional  [algebra K L] [is_splitting_field K L f] :
  finite_dimensional K L :=
is_splitting_field.finite_dimensional L f

end splitting_field_facts

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
@[derive field]
def galois_field (p : ℕ) [fact p.prime] (n : ℕ) :=
splitting_field (X^(p^n) - X : polynomial (zmod p))

instance : inhabited (@galois_field 2 (fact.mk nat.prime_two) 1) :=
⟨37⟩

namespace galois_field
variables (p : ℕ) [fact p.prime] (n : ℕ)

instance : algebra (zmod p) (galois_field p n) :=
splitting_field.algebra _

instance : is_splitting_field (zmod p) (galois_field p n) (X^(p^n) - X) :=
polynomial.is_splitting_field.splitting_field _

instance : char_p (galois_field p n) p :=
(algebra.char_p_iff (zmod p) (galois_field p n) p).mp (by apply_instance)

-- should be able to apply_instance from finite_dimensional.fintype on finite.lean
instance : fintype (galois_field p n) :=
finite_dimensional.fintype_of_fintype (zmod p) (galois_field p n)

/-
lemma finrank : finite_dimensional.finrank (zmod p) (galois_field p n) = n :=
begin
  sorry,
end

lemma card : fintype.card (galois_field p n) = p ^ n :=
begin
  let b := is_noetherian.finset_basis (zmod p) (galois_field p n),
  rw [module.card_fintype b, ← finite_dimensional.finrank_eq_card_basis b, zmod.card, finrank],
end
-/

theorem splits_zmod_X_pow_sub_X : splits (ring_hom.id (zmod p)) (X ^ p - X) :=
begin
  have hp : 1 < p,
  { apply nat.prime.one_lt,
    apply fact_iff.mp,
    assumption },
  have h1 : (-X : polynomial (zmod p)).degree < (X ^ p : polynomial (zmod p)).degree,
  { rw [degree_X_pow, degree_neg, degree_X],
    assumption_mod_cast },
  have h2 : (X ^ p - X : polynomial (zmod p)).nat_degree = p,
  { convert nat_degree_eq_of_degree_eq (degree_add_eq_left_of_degree_lt h1),
    rw nat_degree_X_pow },
  have h3 : roots (X ^ p - X : polynomial (zmod p)) = finset.univ.val,
  { convert finite_field.roots_X_pow_card_sub_X _,
    simp only [eq_self_iff_true, zmod.card], },
  rw [splits_iff_card_roots, h3, ←finset.card_def, finset.card_univ, h2, zmod.card],
end

def equiv_zmod_p : galois_field p 1 ≃ₐ[zmod p] (zmod p) :=
have h : (X ^ p ^ 1 : polynomial (zmod p)) = X ^ (fintype.card (zmod p)),
  by rw [pow_one, zmod.card p],
have inst : is_splitting_field (zmod p) (zmod p) (X ^ p ^ 1 - X),
  by { rw h, apply_instance },
by exactI (is_splitting_field.alg_equiv (zmod p) (X ^ (p ^ 1) - X : polynomial (zmod p))).symm

end galois_field

/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/

import algebra.char_p.algebra
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
  rw nat_degree_prod,
  { simp only [mul_one, nat_degree_X_sub_C, nat.cast_id, finset.sum_const, nsmul_eq_mul,
      finset.card_def], },
  { intros i hi,
    exact X_sub_C_ne_zero i, }
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

lemma finrank {n} (h : n ≠ 0) : finite_dimensional.finrank (zmod p) (galois_field p n) = n :=
begin
  set g_poly := (X^(p^n) - X : polynomial (zmod p)),
  have hp : 1 < p := (fact.out (nat.prime p)).one_lt,
  have aux : g_poly ≠ 0 := finite_field.X_pow_card_pow_sub_X_ne_zero _ h hp,
  have key : fintype.card ((g_poly).root_set (galois_field p n)) = (g_poly).nat_degree :=
    card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
    (splitting_field.splits g_poly),
  have nat_degree_eq : (g_poly).nat_degree = p ^ n :=
    finite_field.X_pow_card_pow_sub_X_nat_degree_eq _ h hp,
  rw nat_degree_eq at key,
  suffices : (g_poly).root_set (galois_field p n) = set.univ,
  { simp_rw [this, ←fintype.of_equiv_card (equiv.set.univ _)] at key,
    rw [@card_eq_pow_findim (zmod p), zmod.card] at key,
    exact nat.pow_right_injective ((nat.prime.one_lt' p).out) key },
  rw set.eq_univ_iff_forall,
  suffices : ∀ x (hx : x ∈ (⊤ : subalgebra (zmod p) (galois_field p n))),
    x ∈ (X ^ p ^ n - X : polynomial (zmod p)).root_set (galois_field p n),
  { simpa, },
  rw ← splitting_field.adjoin_root_set,
  simp_rw algebra.mem_adjoin_iff,
  intros x hx,
  apply subring.closure_induction hx; clear_dependent x; simp_rw mem_root_set aux,
  { rintros x (⟨r, rfl⟩ | hx),
    { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub],
      rw [← ring_hom.map_pow, zmod.pow_card_pow, sub_self], },
    { dsimp only [galois_field] at hx,
      rwa mem_root_set aux at hx, }, },
  { simp only [aeval_X_pow, zero_pow_eq_zero, aeval_X, sub_zero, alg_hom.map_sub],
    apply pow_pos,
    exact nat.prime.pos (fact.out _), },
  { simp, },
  { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub, add_pow_char_pow, sub_eq_zero],
    intros x y hx hy,
    rw [hx, hy], },
  { intros x hx,
    simp only [sub_eq_zero, aeval_X_pow, aeval_X, alg_hom.map_sub, sub_neg_eq_add] at *,
    rw [neg_pow, hx, char_p.neg_one_pow_char_pow],
    simp, },
  { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub, mul_pow, sub_eq_zero],
    intros x y hx hy,
    rw [hx, hy], },
end

lemma card (h : n ≠ 0) : fintype.card (galois_field p n) = p ^ n :=
begin
  let b := is_noetherian.finset_basis (zmod p) (galois_field p n),
  rw [module.card_fintype b, ← finite_dimensional.finrank_eq_card_basis b, zmod.card, finrank p h],
end

theorem splits_zmod_X_pow_sub_X : splits (ring_hom.id (zmod p)) (X ^ p - X) :=
begin
  have hp : 1 < p := (fact.out (nat.prime p)).one_lt,
  have h1 : roots (X ^ p - X : polynomial (zmod p)) = finset.univ.val,
  { convert finite_field.roots_X_pow_card_sub_X _,
    exact (zmod.card p).symm },
  have h2 := finite_field.X_pow_card_sub_X_nat_degree_eq (zmod p) hp,
  rw [splits_iff_card_roots, h1, ←finset.card_def, finset.card_univ, h2, zmod.card],
end

def equiv_zmod_p : galois_field p 1 ≃ₐ[zmod p] (zmod p) :=
have h : (X ^ p ^ 1 : polynomial (zmod p)) = X ^ (fintype.card (zmod p)),
  by rw [pow_one, zmod.card p],
have inst : is_splitting_field (zmod p) (zmod p) (X ^ p ^ 1 - X),
  by { rw h, apply_instance },
by exactI (is_splitting_field.alg_equiv (zmod p) (X ^ (p ^ 1) - X : polynomial (zmod p))).symm

end galois_field

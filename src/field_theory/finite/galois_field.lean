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

## Main Results

- `galois_field.alg_equiv_galois_field`: Uniqueness of finite fields

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

instance : fintype (galois_field p n) := by {dsimp only [galois_field],
  exact finite_dimensional.fintype_of_fintype (zmod p) (galois_field p n) }

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
    rw [@card_eq_pow_finrank (zmod p), zmod.card] at key,
    exact nat.pow_right_injective ((nat.prime.one_lt' p).out) key },
  rw set.eq_univ_iff_forall,
  suffices : ∀ x (hx : x ∈ (⊤ : subalgebra (zmod p) (galois_field p n))),
    x ∈ (X ^ p ^ n - X : polynomial (zmod p)).root_set (galois_field p n),
  { simpa, },
  rw ← splitting_field.adjoin_root_set,
  simp_rw algebra.mem_adjoin_iff,
  intros x hx,
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  unfreezingI { cases p, cases hp, },
  apply subring.closure_induction hx; clear_dependent x; simp_rw mem_root_set aux,
  { rintros x (⟨r, rfl⟩ | hx),
    { simp only [aeval_X_pow, aeval_X, alg_hom.map_sub],
      rw [← ring_hom.map_pow, zmod.pow_card_pow, sub_self], },
    { dsimp only [galois_field] at hx,
      rwa mem_root_set aux at hx, }, },
  { dsimp only [g_poly],
    rw [← coeff_zero_eq_aeval_zero'],
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, ring_hom.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub],
    intro hn,
    exact nat.not_lt_zero 1 (pow_eq_zero hn.symm ▸ hp), },
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
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  unfreezingI { cases p, cases hp, },
  rw [splits_iff_card_roots, h1, ←finset.card_def, finset.card_univ, h2, zmod.card],
end

/-- A Galois field with exponent 1 is equivalent to `zmod` -/
def equiv_zmod_p : galois_field p 1 ≃ₐ[zmod p] (zmod p) :=
have h : (X ^ p ^ 1 : polynomial (zmod p)) = X ^ (fintype.card (zmod p)),
  by rw [pow_one, zmod.card p],
have inst : is_splitting_field (zmod p) (zmod p) (X ^ p ^ 1 - X),
  by { rw h, apply_instance },
by exactI (is_splitting_field.alg_equiv (zmod p) (X ^ (p ^ 1) - X : polynomial (zmod p))).symm

variables {K : Type*} [field K] [fintype K] [algebra (zmod p) K]

theorem splits_X_pow_card_sub_X : splits (algebra_map (zmod p) K) (X ^ fintype.card K - X) :=
by rw [←splits_id_iff_splits, map_sub, map_pow, map_X, splits_iff_card_roots,
  finite_field.roots_X_pow_card_sub_X, ←finset.card_def, finset.card_univ,
  finite_field.X_pow_card_sub_X_nat_degree_eq]; exact fintype.one_lt_card

lemma is_splitting_field_of_card_eq (h : fintype.card K = p ^ n) :
  is_splitting_field (zmod p) K (X ^ (p ^ n) - X) :=
{ splits := by { rw ← h, exact splits_X_pow_card_sub_X p },
  adjoin_roots :=
  begin
    have hne : n ≠ 0,
    { rintro rfl, rw [pow_zero, fintype.card_eq_one_iff_nonempty_unique] at h,
      cases h, resetI, exact false_of_nontrivial_of_subsingleton K },
    refine algebra.eq_top_iff.mpr (λ x, algebra.subset_adjoin _),
    rw [map_sub, map_pow, map_X, finset.mem_coe, multiset.mem_to_finset, mem_roots,
        is_root.def, eval_sub, eval_pow, eval_X, ← h, finite_field.pow_card, sub_self],
    exact finite_field.X_pow_card_pow_sub_X_ne_zero K hne (fact.out _)
  end }

/-- Uniqueness of finite fields : Any finite field is isomorphic to some Galois field. -/
def alg_equiv_galois_field (h : fintype.card K = p ^ n) :
  K ≃ₐ[zmod p] galois_field p n :=
by haveI := is_splitting_field_of_card_eq _ _ h; exact is_splitting_field.alg_equiv _ _

end galois_field

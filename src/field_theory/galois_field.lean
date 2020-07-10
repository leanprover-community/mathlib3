/-
Copyleft. No rights reserved.
Authors: Johan Commelin
-/

import field_theory.finite

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

/-- The canonical isomorphism between a field and the splitting field of a polynomial that splits-/
def ring_equiv_splitting_field_of_splits {f : polynomial K}
  (h : polynomial.splits (ring_hom.id K) f) :
  (K ≃+* f.splitting_field) :=
begin
  apply ring_equiv.of _,
  { refine equiv.mk (algebra_map K f.splitting_field) (polynomial.splitting_field.lift f h) _ _,
    swap, apply right_inverse_of_injective_of_left_inverse, apply ring_hom.injective,
    iterate 2 {intro, simp}, },
  apply_instance,
end

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

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
@[derive field]
def galois_field (p : ℕ) [fact p.prime] (n : ℕ) :=
splitting_field (X^(p^n) - X : polynomial (zmod p))

namespace galois_field
variables (p : ℕ) [fact p.prime] (n : ℕ)

instance : algebra (zmod p) (galois_field p n) :=
splitting_field.algebra _

instance : is_splitting_field (zmod p) (galois_field p n) (X^(p^n) - X) :=
polynomial.is_splitting_field_splitting_field _

instance : char_p (galois_field p n) p :=
(algebra.char_p_iff (zmod p) (galois_field p n) p).mp (by apply_instance)

instance : fintype (galois_field p n) :=
sorry

lemma card : fintype.card (galois_field p n) = p ^ n :=
sorry

variable {n}
theorem zmod_p_splits_X_pow_p_sub_X : splits (ring_hom.id (zmod p)) (X ^ p - X) :=
begin
  apply splits_of_exists_multiset, swap, apply finset.univ.val, apply_instance,
  simp only [ring_hom.id_apply, map_id, map_sub],
  conv_rhs {rw [sub_eq_add_neg, add_comm]},
  rw [leading_coeff_add_of_degree_lt, leading_coeff_X_pow, C_1, one_mul], swap,
  { rw [degree_X_pow, degree_neg, degree_X], apply with_bot.coe_lt_coe.2,
    apply nat.prime.one_lt, apply _inst_1, },
  sorry,
end

def equiv_zmod_p : zmod p ≃+* galois_field p 1 :=
ring_equiv_splitting_field_of_splits (by { rw nat.pow_one, apply zmod_p_splits_X_pow_p_sub_X p, })

end galois_field

/-
Copyleft. No rights reserved.
Authors: Johan Commelin
-/

import field_theory.finite
import field_theory.splitting_field

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

end galois_field

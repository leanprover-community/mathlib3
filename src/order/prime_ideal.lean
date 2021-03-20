/-
Copyright (c) 2021 Noam Atar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noam Atar
-/
import order.basic
import order.ideal
import order.pfilter

/-!
# Prime ideals

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more
structure, such as a bottom element, a top element, or a join-semilattice structure.

- `order.ideal.prime_pair`: A pair of an `ideal` and a `pfilter` which form a partition of `P`.
  This is useful as giving the data of a prime ideal is the same as giving the data of a prime
  filter.
- `order.ideal.is_prime`: a predicate for prime ideals. Dual to the notion of a prime filter.
- `order.pfilter.is_prime`: a predicate for prime filters. Dual to the notion of a prime ideal.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/

namespace order

variables {P : Type*}

section preorder

variables [preorder P]

namespace ideal

/-- A pair of an `ideal` and a `pfilter` which form a partition of `P`.
-/
@[nolint has_inhabited_instance]
structure prime_pair (P : Type*) [preorder P] :=
(I            : ideal P)
(F            : pfilter P)
(compl_I_eq_F : (I : set P)ᶜ = F)

lemma prime_pair.compl_F_eq_I (IF : prime_pair P) : (IF.F : set P)ᶜ = IF.I :=
by rw [←IF.compl_I_eq_F, compl_compl]

lemma prime_pair.ideal_is_proper (IF : prime_pair P) : is_proper IF.I :=
begin
  cases IF.F.nonempty,
  apply is_proper_of_not_mem (_ : w ∉ IF.I),
  rwa ← prime_pair.compl_I_eq_F at h,
end

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff] class is_prime (I : ideal P) extends is_proper I : Prop :=
(compl_filter : is_pfilter (I : set P)ᶜ)

/-- Create an element of type `order.ideal.prime_pair` from an ideal satisfying the predicate
`order.ideal.is_prime`. -/
def is_prime.to_prime_pair {I : ideal P} (h : is_prime I) : prime_pair P :=
{ I            := I,
  F            := h.compl_filter.to_pfilter,
  compl_I_eq_F := rfl }

lemma prime_pair.is_prime (IF : prime_pair P) : is_prime IF.I :=
{ compl_filter := by { rw IF.compl_I_eq_F, exact IF.F.is_pfilter },
  ..IF.ideal_is_proper }

end ideal

namespace pfilter

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff] class is_prime (I : pfilter P) : Prop :=
(compl_ideal : is_ideal (I : set P)ᶜ)

/-- Create an element of type `order.ideal.prime_pair` from a filter satisfying the predicate
`order.pfilter.is_prime`. -/
def is_prime.to_prime_pair {F : pfilter P} (h : is_prime F) : ideal.prime_pair P :=
{ I            := h.compl_ideal.to_ideal,
  F            := F,
  compl_I_eq_F := compl_compl _ }

lemma _root_.order.ideal.prime_pair.pfilter_is_prime (IF : ideal.prime_pair P) : is_prime IF.2 :=
{ compl_ideal := by { rw IF.compl_F_eq_I, exact IF.I.is_ideal } }

end pfilter

end preorder

end order

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

open order.pfilter

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
(is_compl_I_F : is_compl (I : set P) F)

namespace prime_pair
variable (IF : prime_pair P)

lemma compl_I_eq_F : (IF.I : set P)ᶜ = IF.F := IF.is_compl_I_F.compl_eq
lemma compl_F_eq_I : (IF.F : set P)ᶜ = IF.I := IF.is_compl_I_F.eq_compl.symm

lemma I_is_proper : is_proper IF.I :=
begin
  cases IF.F.nonempty,
  apply is_proper_of_not_mem (_ : w ∉ IF.I),
  rwa ← IF.compl_I_eq_F at h,
end

lemma disjoint : disjoint (IF.I : set P) IF.F := IF.is_compl_I_F.disjoint

lemma I_union_F : (IF.I : set P) ∪ IF.F = set.univ := IF.is_compl_I_F.sup_eq_top
lemma F_union_I : (IF.F : set P) ∪ IF.I = set.univ := IF.is_compl_I_F.symm.sup_eq_top

end prime_pair

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff] class is_prime (I : ideal P) extends is_proper I : Prop :=
(compl_filter : is_pfilter (I : set P)ᶜ)

/-- Create an element of type `order.ideal.prime_pair` from an ideal satisfying the predicate
`order.ideal.is_prime`. -/
def is_prime.to_prime_pair {I : ideal P} (h : is_prime I) : prime_pair P :=
{ I            := I,
  F            := h.compl_filter.to_pfilter,
  is_compl_I_F := is_compl_compl }

lemma prime_pair.I_is_prime (IF : prime_pair P) : is_prime IF.I :=
{ compl_filter := by { rw IF.compl_I_eq_F, exact IF.F.is_pfilter },
  ..IF.I_is_proper }

section semilattice_inf

variable [semilattice_inf P]
variables {x y : P}

lemma is_prime.mem_or_mem {I : ideal P} (hI : is_prime I) : x ⊓ y ∈ I → x ∈ I ∨ y ∈ I :=
begin
  contrapose!,
  intro h,
  let IF : prime_pair P := hI.to_prime_pair,
  have hxy : x ∈ ↑IF.F ∧ y ∈ ↑IF.F := by rwa ← prime_pair.compl_I_eq_F,
  show x ⊓ y ∈ IF.F,
  repeat {rw ← pfilter.mem_def at hxy},
  refine @inf_mem P _ IF.F x y hxy.1 hxy.2,
end

end semilattice_inf

end ideal

namespace pfilter

/-- A filter `F` is prime if its complement is an ideal.
-/
@[mk_iff] class is_prime (F : pfilter P) : Prop :=
(compl_ideal : is_ideal (F : set P)ᶜ)

/-- Create an element of type `order.ideal.prime_pair` from a filter satisfying the predicate
`order.pfilter.is_prime`. -/
def is_prime.to_prime_pair {F : pfilter P} (h : is_prime F) : ideal.prime_pair P :=
{ I            := h.compl_ideal.to_ideal,
  F            := F,
  is_compl_I_F := is_compl_compl.symm }

lemma _root_.order.ideal.prime_pair.F_is_prime (IF : ideal.prime_pair P) : is_prime IF.F :=
{ compl_ideal := by { rw IF.compl_F_eq_I, exact IF.I.is_ideal } }

end pfilter

end preorder

end order

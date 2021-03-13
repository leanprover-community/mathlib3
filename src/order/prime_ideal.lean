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

- `prime_pair`: A pair of an `ideal` and a `pfilter` who form a partition of `P`.
                This is useful as giving the data of a prime ideal is the same
                as giving the data of a prime pfilter.
- `is_prime`: a predicate for prime ideals.
              Dual to the notion of a prime filter.

## References

- <https://en.wikipedia.org/wiki/Ideal_(order_theory)>

## Tags

ideal, prime

-/

namespace order

variables {P : Type*}

namespace ideal

section preorder

variables [preorder P]

/-- A pair of an `ideal` and a `pfilter` who form a partition of `P`.
-/
structure prime_pair (P : Type*) [preorder P] :=
(I        : ideal P)
(F        : pfilter P)
(disjoint : (I : set P) ∩ F = ∅)
(cover    : (I : set P) ∪ F = set.univ)

lemma prime_pair.ideal_compl_eq_pfilter {IF : prime_pair P} : (IF.I : set P)ᶜ = IF.F :=
set.subset.antisymm (set.compl_subset_iff_union.2 IF.cover)
(set.subset_compl_comm.mp (set.subset_compl_iff_disjoint.2 IF.disjoint))

lemma prime_pair.ideal_is_proper (IF : prime_pair P) : is_proper IF.I :=
begin
  cases @pfilter.nonempty _ _ IF.F,
  apply is_proper_of_not_mem (_ : w ∉ IF.I),
  rwa ← prime_pair.ideal_compl_eq_pfilter at h,
end

/-- An ideal `I` is prime if its complement is a filter.
-/
@[mk_iff] class is_prime (I : ideal P) extends is_proper I : Prop :=
(compl_filter : is_pfilter ((I : set P)ᶜ))

def prime_pair.of_is_prime (I : ideal P) (h : is_prime I) : prime_pair P :=
⟨I, h.compl_filter.to_pfilter, set.inter_compl_self _, set.union_compl_self _⟩

lemma is_prime.of_is_prime_pair (IF : prime_pair P) : is_prime IF.I :=
{ compl_filter := by {rw prime_pair.ideal_compl_eq_pfilter, exact (IF.F).is_pfilter},
  ..IF.ideal_is_proper
}

end preorder

end ideal

end order

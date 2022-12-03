/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/

import algebra.module.basic
import algebra.big_operators.basic

/-!
# Finite sums over modules over a ring
-/

open_locale big_operators

universes u v
variables {α R k S M M₂ M₃ ι : Type*}
section add_comm_monoid
variables [semiring R] [add_comm_monoid M] [module R M] (r s : R) (x y : M)
variables {R M}
lemma list.sum_smul {l : list R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_list_sum l

lemma multiset.sum_smul {l : multiset R} {x : M} : l.sum • x = (l.map (λ r, r • x)).sum :=
((smul_add_hom R M).flip x).map_multiset_sum l

lemma finset.sum_smul {f : ι → R} {s : finset ι} {x : M} :
  (∑ i in s, f i) • x = (∑ i in s, (f i) • x) :=
((smul_add_hom R M).flip x).map_sum f s
end add_comm_monoid

lemma finset.cast_card [comm_semiring R] (s : finset α) : (s.card : R) = ∑ a in s, 1 :=
by rw [finset.sum_const, nat.smul_one_eq_coe]

/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/

import algebra.big_operators.basic
import algebra.ring.equiv

/-!
# Results about mapping big operators across ring equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace ring_equiv

open_locale big_operators

variables {α R S : Type*}

protected lemma map_list_prod [semiring R] [semiring S] (f : R ≃+* S) (l : list R) :
  f l.prod = (l.map f).prod := map_list_prod f l

protected lemma map_list_sum [non_assoc_semiring R] [non_assoc_semiring S] (f : R ≃+* S)
  (l : list R) : f l.sum = (l.map f).sum := map_list_sum f l

/-- An isomorphism into the opposite ring acts on the product by acting on the reversed elements -/
protected lemma unop_map_list_prod [semiring R] [semiring S] (f : R ≃+* Sᵐᵒᵖ) (l : list R) :
  mul_opposite.unop (f l.prod) = (l.map (mul_opposite.unop ∘ f)).reverse.prod :=
unop_map_list_prod f l

protected lemma map_multiset_prod [comm_semiring R] [comm_semiring S] (f : R ≃+* S)
  (s : multiset R) : f s.prod = (s.map f).prod := map_multiset_prod f s

protected lemma map_multiset_sum [non_assoc_semiring R] [non_assoc_semiring S]
  (f : R ≃+* S) (s : multiset R) : f s.sum = (s.map f).sum := map_multiset_sum f s

protected lemma map_prod [comm_semiring R] [comm_semiring S] (g : R ≃+* S) (f : α → R)
  (s : finset α) : g (∏ x in s, f x) = ∏ x in s, g (f x) :=
map_prod g f s

protected lemma map_sum [non_assoc_semiring R] [non_assoc_semiring S]
  (g : R ≃+* S) (f : α → R) (s : finset α) : g (∑ x in s, f x) = ∑ x in s, g (f x) :=
map_sum g f s

end ring_equiv

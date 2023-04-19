/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Scott Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
import algebra.hom.group
import algebra.group.commute

/-!
# Multiplicative homomorphisms respect semiconjugation and commutation.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

section commute

variables {F M N : Type*} [has_mul M] [has_mul N] {a x y : M}

@[simp, to_additive]
protected lemma semiconj_by.map [mul_hom_class F M N] (h : semiconj_by a x y) (f : F) :
  semiconj_by (f a) (f x) (f y) :=
by simpa only [semiconj_by, map_mul] using congr_arg f h

@[simp, to_additive]
protected lemma commute.map [mul_hom_class F M N] (h : commute x y) (f : F) :
  commute (f x) (f y) :=
h.map f

end commute

/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.set.basic
import data.bool

/-!
# Booleans and set operations

This file contains two trivial lemmas about `bool`, `set.univ`, and `set.range`.
-/

open set

namespace bool

@[simp] lemma univ_eq : (univ : set bool) = {ff, tt} :=
(eq_univ_of_forall bool.dichotomy).symm

@[simp] lemma range_eq {α : Type*} (f : bool → α) : range f = {f ff, f tt} :=
by rw [← image_univ, univ_eq, image_pair]

end bool

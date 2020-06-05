/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

Some proofs and docs came from `algebra/commute` (c) Neil Strickland
-/
import algebra.group_power
import data.equiv.mul_add

/-!
# Semiconjugate elements of a semigroup

## Main definitions

We say that `x` is semiconjugate to `y` by `a` (`semiconj_by a x y`), if `a * x = y * a`.
In this file we  provide operations on `semiconj_by _ _ _`.

In the names of these operations, we treat `a` as the “left” argument,
and both `x` and `y` as “right” arguments. This way most names in this
file agree with the names of the corresponding lemmas for `commute a b
= semiconj_by a b b`. As a side effect, some lemmas have only `_right`
version.

Lean does not immediately recognise these terms as equations,
so for rewriting we need syntax like `rw [(h.pow_right 5).eq]`
rather than just `rw [h.pow_right 5]`.
-/

universes u v


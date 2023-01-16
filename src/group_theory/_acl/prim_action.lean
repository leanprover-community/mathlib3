/-
Copyright (c) 2021 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import group_theory.iwasawa
import algebra.pointwise

/-!

# Primitive actions and maximal subgroups

Will incorporate relevant material of group_theory.iwasawa

-/

open_locale big_operators pointwise

variables {G : Type*} [group G]
variables {X : Type*} [mul_action G X]

variable (G)
def is_block_of (B : set X) :=
  nonempty B ∧ ∀ (g : G), g • B = B ∨ g • B ∩ B = ∅

lemma singleton_is_block (x : X) :
  is_block_of G ({x} : set X) :=
begin
  split,
  exact nonempty_of_inhabited,
  intro g,
  rw set.smul_singleton _ _,

  cases classical.em (g • x = x) with h h',
  { apply or.intro_left,  sorry, },
  sorry,
end

lemma primitive_iff_trivial_blocks :
is_primitive G X
 ↔ ∀ (B : set X), is_block_of G B ↔ subsingleton B :=
begin
  split
end

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/

import algebra.order.group.basic
import order.bounds

/-!
### Least upper bound and the greatest lower bound in linear ordered additive commutative groups
-/

section linear_ordered_add_comm_group

variables {α : Type*} [linear_ordered_add_comm_group α] {s : set α} {a ε : α}

lemma is_glb.exists_between_self_add (h : is_glb s a) (hε : 0 < ε) :
  ∃ b ∈ s, a ≤ b ∧ b < a + ε :=
h.exists_between $ lt_add_of_pos_right _ hε

lemma is_glb.exists_between_self_add' (h : is_glb s a) (h₂ : a ∉ s) (hε : 0 < ε) :
  ∃ b ∈ s, a < b ∧ b < a + ε :=
h.exists_between' h₂ $ lt_add_of_pos_right _ hε

lemma is_lub.exists_between_sub_self  (h : is_lub s a) (hε : 0 < ε) : ∃ b ∈ s, a - ε < b ∧ b ≤ a :=
h.exists_between $ sub_lt_self _ hε

lemma is_lub.exists_between_sub_self' (h : is_lub s a) (h₂ : a ∉ s) (hε : 0 < ε) :
  ∃ b ∈ s, a - ε < b ∧ b < a :=
h.exists_between' h₂ $ sub_lt_self _ hε

end linear_ordered_add_comm_group

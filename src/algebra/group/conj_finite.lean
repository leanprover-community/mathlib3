/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/

import algebra.group.conj
import data.finite.basic
import data.fintype.units

/-!
# Conjugacy of elements of finite groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*} [monoid α]

local attribute [instance, priority 100] is_conj.setoid

instance [fintype α] [decidable_rel (is_conj : α → α → Prop)] :
  fintype (conj_classes α) :=
quotient.fintype (is_conj.setoid α)

instance [finite α] : finite (conj_classes α) :=
quotient.finite _

instance [decidable_eq α] [fintype α] : decidable_rel (is_conj : α → α → Prop) :=
λ a b, by { delta is_conj semiconj_by, apply_instance }

instance [fintype α] [decidable_rel (is_conj : α → α → Prop)] {a : α} : fintype (conjugates_of a) :=
@subtype.fintype _ _ (‹decidable_rel is_conj› a) _

namespace conj_classes

variables [fintype α] [decidable_rel (is_conj : α → α → Prop)]

instance {x : conj_classes α} : fintype (carrier x) :=
quotient.rec_on_subsingleton x $ λ a, conjugates_of.fintype

end conj_classes

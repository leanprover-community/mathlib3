/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/

import order.filter
import algebra.module.submodule.basic
import topology.algebra.monoid
import analysis.asymptotics.asymptotics

/-! ## Zero at filter -/

namespace filter

open_locale topological_space

def zero_at_filter {α : Type*} {β : Type*} [has_zero β] [topological_space β] (l : filter α)
(f : α → β) : Prop := filter.tendsto f l (𝓝 0)

lemma zero_is_zero_at_filter {α : Type*} {β : Type*} [has_zero β] [topological_space β]
(l : filter α) : zero_at_filter l (0 : α → β) := tendsto_const_nhds

def zero_at_filter_submodule {α : Type*} {β : Type*} [topological_space β] [semiring β]
[has_continuous_add β] [has_continuous_mul β] (l : filter α) : submodule β (α → β) :=
{ carrier := zero_at_filter l,
  zero_mem' := zero_is_zero_at_filter l,
  add_mem' := by { intros a b ha hb, simpa using ha.add hb, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul c }, }

def zero_at_filter_add_submonoid {α : Type*} {β : Type*} [topological_space β]
[add_zero_class β] [has_continuous_add β] (l : filter α) : add_submonoid (α → β) :=
{ carrier := zero_at_filter l,
  add_mem' := by { intros a b ha hb,simpa using ha.add hb },
  zero_mem' := zero_is_zero_at_filter l, }

def bounded_at_filter {α : Type*} {β : Type*} [has_norm β] [has_one (α → β)] (l : filter α)
(f : α → β) : Prop := asymptotics.is_O l f (1 : α → β)

lemma zero_at_filter_is_bounded_at_filter {α : Type*} {β : Type*} [normed_field β]
(l : filter α) (f : α → β) (hf : zero_at_filter l f) : bounded_at_filter l f :=
begin
  apply asymptotics.is_O_of_div_tendsto_nhds, { simp, }, { convert hf, ext1, simp, },
end

lemma zero_is_bounded_at_filter {α : Type*} {β : Type*} [normed_field β] (l : filter α) :
  bounded_at_filter l (0 : α → β) :=
(zero_at_filter_is_bounded_at_filter l _) (zero_is_zero_at_filter l)

def bounded_filter_submodule {α : Type*} {β : Type*} [normed_field β] (l : filter α) :
  submodule β (α → β) :=
{ carrier := bounded_at_filter l,
  zero_mem' := zero_is_bounded_at_filter l,
  add_mem' := by { intros f g hf hg, simpa using hf.add hg, },
  smul_mem' := by { intros c f hf, simpa using hf.const_mul_left c }, }

def bounded_filter_subalgebra {α : Type*} {β : Type*} [normed_field β] (l : filter α) :
  subalgebra β (α → β) :=
begin
  apply submodule.to_subalgebra,
  work_on_goal 3 {use bounded_filter_submodule l},
  work_on_goal 2 { by {intros f g hf hg, by simpa using hf.mul hg,},},
  simpa using (asymptotics.is_O_const_mul_self (1 :β) (1 : α → β) l),
end

end filter

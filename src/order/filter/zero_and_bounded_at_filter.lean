/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import algebra.module.submodule.basic
import topology.algebra.monoid
import analysis.asymptotics.asymptotics

/-!
# Zero and Bounded at filter

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a filter `l` we define the notion of a function being `zero_at_filter` as well as being
`bounded_at_filter`. Alongside this we construct the `submodule`, `add_submonoid` of functions
that are `zero_at_filter`. Similarly, we construct the `submodule` and `subalgebra` of functions
that are `bounded_at_filter`.

-/

namespace filter

variables {α β : Type*}

open_locale topology

/-- If `l` is a filter on `α`, then a function `f : α → β` is `zero_at_filter l`
  if it tends to zero along `l`. -/
def zero_at_filter [has_zero β] [topological_space β] (l : filter α) (f : α → β) : Prop :=
filter.tendsto f l (𝓝 0)

lemma zero_zero_at_filter [has_zero β] [topological_space β] (l : filter α) :
  zero_at_filter l (0 : α → β) :=
tendsto_const_nhds

lemma zero_at_filter.add [topological_space β] [add_zero_class β] [has_continuous_add β]
  {l : filter α} {f g : α → β} (hf : zero_at_filter l f) (hg : zero_at_filter l g) :
  zero_at_filter l (f + g) :=
by simpa using hf.add hg

lemma zero_at_filter.neg [topological_space β] [add_group β] [has_continuous_neg β] {l : filter α}
  {f : α → β} (hf : zero_at_filter l f) :
  zero_at_filter l (-f) :=
by simpa using hf.neg

lemma zero_at_filter.smul {𝕜 : Type*} [topological_space 𝕜] [topological_space β] [has_zero 𝕜]
  [has_zero β] [smul_with_zero 𝕜 β] [has_continuous_smul 𝕜 β]
   {l : filter α} {f : α → β} (c : 𝕜) (hf : zero_at_filter l f) :
  zero_at_filter l (c • f) :=
by simpa using hf.const_smul c

/-- `zero_at_filter_submodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
def zero_at_filter_submodule [topological_space β] [semiring β]
  [has_continuous_add β] [has_continuous_mul β] (l : filter α) : submodule β (α → β) :=
{ carrier := zero_at_filter l,
  zero_mem' := zero_zero_at_filter l,
  add_mem' := λ a b ha hb, ha.add hb,
  smul_mem' := λ c f hf, hf.smul c }

/-- `zero_at_filter_add_submonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
def zero_at_filter_add_submonoid [topological_space β]
  [add_zero_class β] [has_continuous_add β] (l : filter α) : add_submonoid (α → β) :=
{ carrier := zero_at_filter l,
  add_mem' := λ a b ha hb, ha.add hb,
  zero_mem' := zero_zero_at_filter l, }

/-- If `l` is a filter on `α`, then a function `f: α → β` is `bounded_at_filter l`
if `f =O[l] 1`. -/
def bounded_at_filter [has_norm β] (l : filter α) (f : α → β) : Prop :=
asymptotics.is_O l f (1 : α → ℝ)

lemma zero_at_filter.bounded_at_filter [normed_add_comm_group β] {l : filter α} {f : α → β}
  (hf : zero_at_filter l f) : bounded_at_filter l f :=
begin
  rw [zero_at_filter, ← asymptotics.is_o_const_iff (one_ne_zero' ℝ)] at hf,
  exact hf.is_O,
end

lemma const_bounded_at_filter [normed_field β] (l : filter α) (c : β) :
  bounded_at_filter l (function.const α c : α → β) :=
asymptotics.is_O_const_const c one_ne_zero l

lemma bounded_at_filter.add [normed_add_comm_group β] {l : filter α} {f g : α → β}
  (hf : bounded_at_filter l f) (hg : bounded_at_filter l g) :
  bounded_at_filter l (f + g) :=
by simpa using hf.add hg

lemma bounded_at_filter.neg [normed_add_comm_group β] {l : filter α} {f : α → β}
  (hf : bounded_at_filter l f) :
  bounded_at_filter l (-f) :=
hf.neg_left

lemma bounded_at_filter.smul {𝕜 : Type*} [normed_field 𝕜] [normed_add_comm_group β]
  [normed_space 𝕜 β] {l : filter α} {f : α → β} (c : 𝕜) (hf : bounded_at_filter l f) :
  bounded_at_filter l (c • f) :=
hf.const_smul_left c

lemma bounded_at_filter.mul [normed_field β] {l : filter α} {f g : α → β}
  (hf : bounded_at_filter l f) (hg : bounded_at_filter l g) :
  bounded_at_filter l (f * g) :=
begin
  refine (hf.mul hg).trans _,
  convert asymptotics.is_O_refl _ l,
  ext x,
  simp,
end

/-- The submodule of functions that are bounded along a filter `l`. -/
def bounded_filter_submodule [normed_field β] (l : filter α) : submodule β (α → β) :=
{ carrier := bounded_at_filter l,
  zero_mem' := const_bounded_at_filter l 0,
  add_mem' := λ f g hf hg, hf.add hg,
  smul_mem' := λ c f hf, hf.smul c }

/-- The subalgebra of functions that are bounded along a filter `l`. -/
def bounded_filter_subalgebra [normed_field β] (l : filter α) :
  subalgebra β (α → β) :=
begin
  refine submodule.to_subalgebra (bounded_filter_submodule l) _ (λ f g hf hg, _),
  { exact const_bounded_at_filter l (1:β) },
  { simpa only [pi.one_apply, mul_one, norm_mul] using hf.mul hg, },

end

end filter

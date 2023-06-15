/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finsupp.defs

/-!
# Building finitely supported functions off finsets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `finsupp.indicator` to help create finsupps from finsets.

## Main declarations

* `finsupp.indicator`: Turns a map from a `finset` into a `finsupp` from the entire type.
-/

noncomputable theory

open finset function

variables {ι α : Type*}

namespace finsupp
variables [has_zero α] {s : finset ι} (f : Π i ∈ s, α) {i : ι}

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def indicator (s : finset ι) (f : Π i ∈ s, α) : ι →₀ α :=
{ to_fun := λ i, by haveI := classical.dec_eq ι; exact
    if H : i ∈ s then f i H else 0,
  support := by haveI := classical.dec_eq α; exact
    (s.attach.filter $ λ i : s, f i.1 i.2 ≠ 0).map (embedding.subtype _),
  mem_support_to_fun := λ i, begin
    letI := classical.dec_eq α,
    rw [mem_map, dite_ne_right_iff],
    exact ⟨λ ⟨⟨j, hj⟩, hf, rfl⟩, ⟨hj, (mem_filter.1 hf).2⟩,
      λ ⟨hi, hf⟩, ⟨⟨i, hi⟩, mem_filter.2 $ ⟨mem_attach _ _, hf⟩, rfl⟩⟩,
  end }

lemma indicator_of_mem (hi : i ∈ s) (f : Π i ∈ s, α) : indicator s f i = f i hi :=
@dif_pos _ (id _) hi _ _ _
lemma indicator_of_not_mem (hi : i ∉ s) (f : Π i ∈ s, α) : indicator s f i = 0 :=
@dif_neg _ (id _) hi _ _ _

variables (s i)

@[simp] lemma indicator_apply [decidable_eq ι] :
  indicator s f i = if hi : i ∈ s then f i hi else 0 := by convert rfl

lemma indicator_injective : injective (λ f : Π i ∈ s, α, indicator s f) :=
begin
  intros a b h,
  ext i hi,
  rw [←indicator_of_mem hi a, ←indicator_of_mem hi b],
  exact congr_fun h i,
end

lemma support_indicator_subset : ((indicator s f).support : set ι) ⊆ s :=
begin
  intros i hi,
  rw [mem_coe, mem_support_iff] at hi,
  by_contra,
  exact hi (indicator_of_not_mem h _),
end

lemma single_eq_indicator (i : ι) (b : α) :
  single i b = indicator {i} (λ _ _, b) :=
by { classical, ext, simp [single_apply, indicator_apply, @eq_comm _ a] }

end finsupp

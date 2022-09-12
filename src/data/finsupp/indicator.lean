/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finsupp.defs

/-!
# Building finitely supported functions off finsets

This file defines `finsupp.pindicator` to help create finsupps from finsets.

## Main declarations

* `finsupp.pindicator`: Turns a partially defined function from a `finset`
into a `finsupp` from the entire type.
-/

noncomputable theory

open finset function
open_locale classical

variables {ι α : Type*}

namespace finsupp
variables [has_zero α] {s : finset ι} (f : Π i ∈ s, α) {i : ι}

/-- Create an element of `ι →₀ α` from a finset `s` and a function `f` defined on this finset. -/
def pindicator (s : finset ι) (f : Π i ∈ s, α) : ι →₀ α :=
{ to_fun := λ i, if H : i ∈ s then f i H else 0,
  support := (s.attach.filter $ λ i : s, f i.1 i.2 ≠ 0).map $ embedding.subtype _,
  mem_support_to_fun := λ i, begin
    rw [mem_map, dite_ne_right_iff],
    exact ⟨λ ⟨⟨j, hj⟩, hf, rfl⟩, ⟨hj, (mem_filter.1 hf).2⟩,
      λ ⟨hi, hf⟩, ⟨⟨i, hi⟩, mem_filter.2 $ ⟨mem_attach _ _, hf⟩, rfl⟩⟩,
  end }

lemma pindicator_of_mem (hi : i ∈ s) (f : Π i ∈ s, α) : pindicator s f i = f i hi := dif_pos hi
lemma pindicator_of_not_mem (hi : i ∉ s) (f : Π i ∈ s, α) : pindicator s f i = 0 := dif_neg hi

variables (s i)

@[simp] lemma pindicator_apply : pindicator s f i = if hi : i ∈ s then f i hi else 0 := rfl

lemma pindicator_injective : injective (λ f : Π i ∈ s, α, pindicator s f) :=
begin
  intros a b h,
  ext i hi,
  rw [←pindicator_of_mem hi a, ←pindicator_of_mem hi b],
  exact congr_fun h i,
end

lemma support_pindicator_subset : ((pindicator s f).support : set ι) ⊆ s :=
begin
  intros i hi,
  rw [mem_coe, mem_support_iff] at hi,
  by_contra,
  exact hi (pindicator_of_not_mem h _),
end

end finsupp

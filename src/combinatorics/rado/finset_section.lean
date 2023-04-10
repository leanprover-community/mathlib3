/-
Copyright (c) 2023 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/

import combinatorics.rado.auxiliary

/-!
# Sections of families of finite sets

Let `F : ι → finset α` be a family of finite sets. A *section* of `F` is a function `f : ι → α`
such that `f i ∈ F i` for all `i : ι`. We define `finset.is_section F f` to express this property
and `finset.is_section_on F f s` to express that `f` is a section on the finset `s`.

We then provide some basic API lemmas.

(Note: `section` is a reserved word, so would be problematic as a name.)
-/

namespace finset

variables {ι : Type*} {α : Type*}

/-- A function `f : ι → α` is a *section* of `F : ι → finset α` if it maps `i` into `F i`. -/
def is_section (F : ι → finset α) (f : ι → α) : Prop := ∀ i, f i ∈ F i

/-- A function `f : ι → α` is a *section* of `F : ι → finset α` on a finite set `s` if it maps
`i` into `F i` for all `i ∈ s`. -/
def is_section_on (F : ι → finset α) (f : ι → α) (s : finset ι) : Prop :=
∀ ⦃i⦄ (hi : i ∈ s), f i ∈ F i

protected
lemma is_section.is_section_on {F : ι → finset α} {f : ι → α} (h : is_section F f) (s : finset ι) :
  is_section_on F f s :=
λ i _, h i

lemma is_section_iff_is_section_on {F : ι → finset α} {f : ι → α} :
  is_section F f ↔ ∀ s : finset ι, is_section_on F f s :=
⟨λ H, H.is_section_on, λ H i, H {i} (mem_singleton_self i)⟩

lemma is_section_on.congr {F : ι → finset α} {f g : ι → α} {s : finset ι}
  (h₁ : is_section_on F f s) (h₂ : s.eq_on f g) : is_section_on F g s :=
λ i hi, h₂ hi ▸ h₁ hi

lemma is_section_on.subset {F : ι → finset α} {f : ι → α} {t s : finset ι}
  (h₁ : is_section_on F f s) (h₂ : t ⊆ s) : is_section_on F f t :=
λ i hi, h₁ (h₂ hi)

lemma is_section_on_iff_is_section_restrict {F : ι → finset α} {f : ι → α} {s : finset ι} :
  is_section_on F f s ↔ is_section (s.restrict F) (s.restrict f) :=
⟨λ H i, H i.property, λ H i hi, H ⟨i, hi⟩⟩

lemma is_section_on.image_subset_bUnion [decidable_eq α] {F : ι → finset α} {f : ι → α}
  {s : finset ι} (h : is_section_on F f s) : s.image f ⊆ s.bUnion F :=
begin
  refine λ i hi, mem_bUnion.mpr _,
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hi,
  exact ⟨j, hj, h hj⟩,
end

end finset

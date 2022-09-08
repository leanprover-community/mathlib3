/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.set.basic

/-!
# Sets in sigma types

This file defines `set.sigma`, the indexed sum of sets.
-/

namespace set
variables {ι ι' : Type*} {α β : ι → Type*} {s s₁ s₂ : set ι} {t t₁ t₂ : Π i, set (α i)}
  {u : set (Σ i, α i)} {x : Σ i, α i} {i : ι} {a : α i}

/-- Indexed sum of sets. `s.sigma t` is the set of dependent pairs `⟨i, a⟩` such that `i ∈ s` and
`a ∈ t i`.-/
protected def sigma (s : set ι) (t : Π i, set (α i)) : set (Σ i, α i) := {x | x.1 ∈ s ∧ x.2 ∈ t x.1}

@[simp] lemma mem_sigma_iff : x ∈ s.sigma t ↔ x.1 ∈ s ∧ x.2 ∈ t x.1 := iff.rfl
@[simp] lemma mk_sigma_iff : (⟨i, a⟩ : Σ i, α i) ∈ s.sigma t ↔ i ∈ s ∧ a ∈ t i := iff.rfl

lemma mk_mem_sigma (hi : i ∈ s) (ha : a ∈ t i) : (⟨i, a⟩ : Σ i, α i) ∈ s.sigma t := ⟨hi, ha⟩

lemma sigma_mono (hs : s₁ ⊆ s₂) (ht : ∀ i, t₁ i ⊆ t₂ i) : s₁.sigma t₁ ⊆ s₂.sigma t₂ :=
λ x hx, ⟨hs hx.1, ht _ hx.2⟩

lemma sigma_subset_iff : s.sigma t ⊆ u ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → (⟨i, a⟩ : Σ i, α i) ∈ u :=
⟨λ h i hi a ha, h $ mk_mem_sigma hi ha, λ h ⟨i, a⟩ ha, h ha.1 ha.2⟩

lemma forall_sigma_iff {p : (Σ i, α i) → Prop} :
  (∀ x ∈ s.sigma t, p x) ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃a⦄, a ∈ t i → p ⟨i, a⟩ :=
sigma_subset_iff

lemma exists_sigma_iff {p : (Σ i, α i) → Prop} :
  (∃ x ∈ s.sigma t, p x) ↔ ∃ (i ∈ s) (a ∈ t i), p ⟨i, a⟩ :=
⟨λ ⟨⟨i, a⟩, ha, h⟩, ⟨i, ha.1, a, ha.2, h⟩, λ ⟨i, hi, a, ha, h⟩, ⟨⟨i, a⟩, ⟨hi, ha⟩, h⟩⟩

@[simp] lemma sigma_empty : s.sigma (λ _, (∅ : set (α i))) = ∅ := ext $ λ _, and_false _
@[simp] lemma empty_sigma : (∅ : set ι).sigma t = ∅ := ext $ λ _, false_and _
lemma univ_sigma_univ : (@univ ι).sigma (λ _, @univ (α i)) = univ := ext $ λ _, true_and _
@[simp] lemma sigma_univ : s.sigma (λ _, univ : Π i, set (α i)) = sigma.fst ⁻¹' s :=
ext $ λ _, and_true _

@[simp] lemma singleton_sigma : ({i} : set ι).sigma t = sigma.mk i '' t i :=
ext $ λ x, begin
  split,
  { obtain ⟨j, a⟩ := x,
    rintro ⟨(rfl : j = i), ha⟩,
    exact mem_image_of_mem _ ha },
  { rintro ⟨b, hb, rfl⟩,
    exact ⟨rfl, hb⟩ }
end

@[simp] lemma sigma_singleton {a : Π i, α i} :
  s.sigma (λ i, ({a i} : set (α i))) = (λ i, sigma.mk i $ a i) '' s :=
by { ext ⟨x, y⟩, simp [and.left_comm, eq_comm] }

lemma singleton_sigma_singleton {a : Π i, α i} :
  ({i} : set ι).sigma (λ i, ({a i} : set (α i))) = {⟨i, a i⟩} :=
by rw [sigma_singleton, image_singleton]

@[simp] lemma union_sigma : (s₁ ∪ s₂).sigma t = s₁.sigma t ∪ s₂.sigma t :=
ext $ λ _, or_and_distrib_right

@[simp] lemma sigma_union : s.sigma (λ i, t₁ i ∪ t₂ i) = s.sigma t₁ ∪ s.sigma t₂ :=
ext $ λ _, and_or_distrib_left

lemma sigma_inter_sigma : s₁.sigma t₁ ∩ s₂.sigma t₂ = (s₁ ∩ s₂).sigma (λ i, t₁ i ∩ t₂ i) :=
by { ext ⟨x, y⟩, simp [and_assoc, and.left_comm] }

lemma insert_sigma : (insert i s).sigma t = (sigma.mk i '' t i) ∪ s.sigma t :=
by rw [insert_eq, union_sigma, singleton_sigma]

lemma sigma_insert {a : Π i, α i} :
  s.sigma (λ i, insert (a i) (t i)) = ((λ i, ⟨i, a i⟩) '' s) ∪ s.sigma t :=
by simp_rw [insert_eq, sigma_union, sigma_singleton]

lemma sigma_preimage_eq {f : ι' → ι} {g : Π i, β i → α i} :
  (f ⁻¹' s).sigma (λ i, g (f i) ⁻¹' t (f i)) =
    (λ p : Σ i, β (f i), sigma.mk _ (g _ p.2)) ⁻¹' (s.sigma t) := rfl

lemma sigma_preimage_left {f : ι' → ι} :
  (f ⁻¹' s).sigma (λ i, t (f i)) = (λ p : Σ i, α (f i), sigma.mk _ p.2) ⁻¹' (s.sigma t) := rfl

lemma sigma_preimage_right {g : Π i, β i → α i} :
  s.sigma (λ i, g i ⁻¹' t i) = (λ p : Σ i, β i, sigma.mk p.1 (g _ p.2)) ⁻¹' (s.sigma t) := rfl

lemma preimage_sigma_map_sigma {α' : ι' → Type*} (f : ι → ι') (g : Π i, α i → α' (f i)) (s : set ι')
  (t : Π i, set (α' i)) :
  sigma.map f g ⁻¹' (s.sigma t) = (f ⁻¹' s).sigma (λ i, g i ⁻¹' t (f i)) := rfl

@[simp] lemma mk_preimage_sigma (hi : i ∈ s) : sigma.mk i ⁻¹' s.sigma t = t i :=
ext $ λ _, and_iff_right hi

@[simp] lemma mk_preimage_sigma_eq_empty (hi : i ∉ s) : sigma.mk i ⁻¹' s.sigma t = ∅ :=
ext $ λ _, iff_of_false (hi ∘ and.left) id

lemma mk_preimage_sigma_eq_if [decidable_pred (∈ s)] :
  sigma.mk i ⁻¹' s.sigma t = if i ∈ s then t i else ∅ :=
by split_ifs; simp [h]

lemma mk_preimage_sigma_fn_eq_if {β : Type*} [decidable_pred (∈ s)] (g : β → α i) :
  (λ b, sigma.mk i (g b)) ⁻¹' s.sigma t = if i ∈ s then g ⁻¹' t i else ∅ :=
ext $ λ _, by split_ifs; simp [h]

lemma sigma_univ_range_eq {f : Π i, α i → β i} :
  (univ : set ι).sigma (λ i, range (f i)) = range (λ x : Σ i, α i, ⟨x.1, f _ x.2⟩) :=
ext $ by simp [range]

protected lemma nonempty.sigma :
  s.nonempty → (∀ i, (t i).nonempty) → (s.sigma t : set _).nonempty :=
λ ⟨i, hi⟩ h, let ⟨a, ha⟩ := h i in ⟨⟨i, a⟩, hi, ha⟩

lemma nonempty.sigma_fst : (s.sigma t : set _).nonempty → s.nonempty := λ ⟨x, hx⟩, ⟨x.1, hx.1⟩
lemma nonempty.sigma_snd : (s.sigma t : set _).nonempty → ∃ i ∈ s, (t i).nonempty :=
λ ⟨x, hx⟩, ⟨x.1, hx.1, x.2, hx.2⟩

lemma sigma_nonempty_iff : (s.sigma t : set _).nonempty ↔ ∃ i ∈ s, (t i).nonempty :=
⟨nonempty.sigma_snd, λ ⟨i, hi, a, ha⟩, ⟨⟨i, a⟩, hi, ha⟩⟩

lemma sigma_eq_empty_iff : s.sigma t = ∅ ↔ ∀ i ∈ s, t i = ∅ :=
not_nonempty_iff_eq_empty.symm.trans $ sigma_nonempty_iff.not.trans $
  by simp only [not_nonempty_iff_eq_empty, not_exists]

lemma image_sigma_mk_subset_sigma_left {a : Π i, α i} (ha : ∀ i, a i ∈ t i) :
  (λ i, sigma.mk i (a i)) '' s ⊆ s.sigma t :=
image_subset_iff.2 $ λ i hi, ⟨hi, ha _⟩

lemma image_sigma_mk_subset_sigma_right (hi : i ∈ s) : sigma.mk i '' t i ⊆ s.sigma t :=
image_subset_iff.2 $ λ a, and.intro hi

lemma sigma_subset_preimage_fst (s : set ι) (t : Π i, set (α i)) : s.sigma t ⊆ sigma.fst ⁻¹' s :=
λ a, and.left

lemma fst_image_sigma_subset (s : set ι) (t : Π i, set (α i)) : sigma.fst '' s.sigma t ⊆ s :=
image_subset_iff.2 $ λ a, and.left

lemma fst_image_sigma (s : set ι) (ht : ∀ i, (t i).nonempty) : sigma.fst '' s.sigma t = s :=
(fst_image_sigma_subset _ _).antisymm $ λ i hi, let ⟨a, ha⟩ := ht i in ⟨⟨i, a⟩, ⟨hi, ha⟩, rfl⟩

lemma sigma_diff_sigma : s₁.sigma t₁ \ s₂.sigma t₂ = s₁.sigma (t₁ \ t₂) ∪ (s₁ \ s₂).sigma t₁ :=
ext $ λ x, by by_cases h₁ : x.1 ∈ s₁; by_cases h₂ : x.2 ∈ t₁ x.1; simp [*, ←imp_iff_or_not]

end set

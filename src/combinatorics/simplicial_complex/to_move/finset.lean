import data.finset.basic
import combinatorics.simplicial_complex.to_move.set

variables {α : Type*}

namespace finset

@[simp]
lemma attach_nonempty_iff (s : finset α) :
  s.attach.nonempty ↔ s.nonempty :=
by simp [←card_pos]

lemma exists_min [semilattice_inf α]
  {s : finset α} (hs₁ : s.nonempty) (hs₂ : ∀ x y ∈ s, x ⊓ y ∈ s) :
  ∃ z ∈ s, ∀ y ∈ s, z ≤ y :=
@multiset.exists_min_of_inf_closed _ _ s.1 (by simpa using hs₁.ne_empty) hs₂

--Are those two in mathlib?
lemma ssubset_of_ssubset_of_subset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊂ s₂) (hs₂s₃ : s₂ ⊆ s₃) :
  s₁ ⊂ s₃ :=
⟨subset.trans hs₁s₂.1 hs₂s₃, λ hs₃s₁, hs₁s₂.2 (subset.trans hs₂s₃ hs₃s₁)⟩
lemma ssubset_of_subset_of_ssubset {s₁ s₂ s₃ : finset α} (hs₁s₂ : s₁ ⊆ s₂) (hs₂s₃ : s₂ ⊂ s₃) :
  s₁ ⊂ s₃ :=
⟨subset.trans hs₁s₂ hs₂s₃.1, λ hs₃s₁, hs₂s₃.2 (subset.trans hs₃s₁ hs₁s₂)⟩

--and this one?
lemma union_subset_iff [decidable_eq α] {s₁ s₂ s₃ : finset α} :
  s₁ ∪ s₂ ⊆ s₃ ↔ s₁ ⊆ s₃ ∧ s₂ ⊆ s₃ :=
begin
  split,
  { rintro h,
    split,
    exact subset.trans (subset_union_left s₁ s₂) h,
    exact subset.trans (subset_union_right s₁ s₂) h },
  rintro ⟨hs₁s₃, hs₂s₃⟩,
  exact union_subset hs₁s₃ hs₂s₃,
end

lemma subset_inter_iff [decidable_eq α] {s₁ s₂ s₃ : finset α} :
  s₁ ⊆ s₂ ∩ s₃ ↔ s₁ ⊆ s₂ ∧ s₁ ⊆ s₃ :=
begin
  split,
  { rintro h,
    split,
    exact subset.trans h (inter_subset_left _ _),
    exact subset.trans h (inter_subset_right _ _), },
  rintro ⟨h₁, h₂⟩,
  exact subset_inter h₁ h₂,
end

lemma subset_iff_inter_eq_left [decidable_eq α] {s₁ s₂ : finset α}  :
  s₁ ⊆ s₂ ↔ s₁ ∩ s₂ = s₁ :=
begin
  split,
  { rintro h,
    ext t,
    simp only [and_iff_left_iff_imp, finset.mem_inter],
    apply h },
  intro h,
  rw ←h,
  exact inter_subset_right _ _,
end

lemma subset_iff_inter_eq_right [decidable_eq α] {s₁ s₂ : finset α} :
  s₁ ⊆ s₂ ↔ s₂ ∩ s₁ = s₁ :=
begin
  split,
  { rintro h,
    ext t,
    simp only [and_iff_right_iff_imp, finset.mem_inter],
    apply h },
  rintro h,
  rw ← h,
  exact finset.inter_subset_left _ _,
end

lemma subset_singleton_iff {s : finset α} {a : α} : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
begin
  split,
  { intro hs,
    apply or.imp_right _ s.eq_empty_or_nonempty,
    rintro ⟨t, ht⟩,
    apply subset.antisymm hs,
    rwa [singleton_subset_iff, ←mem_singleton.1 (hs ht)] },
  rintro (rfl | rfl),
  { exact empty_subset _ },
  exact subset.refl _,
end

lemma ssubset_singleton_iff_eq_empty (x : α) (s : finset α) :
  s ⊂ {x} ↔ s = ∅ :=
by rw [←coe_ssubset, coe_singleton, set.ssubset_singleton_iff_eq_empty x s, coe_eq_empty]

lemma eq_empty_of_ssubset_singleton {x : α} {s : finset α} (hs : s ⊂ {x}) :
  s = ∅ :=
(ssubset_singleton_iff_eq_empty _ _).1 hs

lemma exists_of_ssubset {s t : finset α} (h : s ⊂ t) :
  ∃ x ∈ t, x ∉ s :=
set.exists_of_ssubset h

lemma strong_downward_induction_on {α : Type*} {p : finset α → Prop} {n : ℕ}
  (h : ∀ {t₁}, (∀ {t₂ : finset α}, t₂.card ≤ n → t₁ ⊂ t₂ → p t₂) → p t₁) {s : finset α} :
  s.card ≤ n → p s :=
begin
  apply well_founded.induction (measure_wf (λ (t : finset α), n - t.card)) s,
  exact (λ x ih hx, h (λ z hz xz, ih _ ((nat.sub_lt_sub_left_iff hz).2 (finset.card_lt_card xz)) hz)),
end

-- TODO: find in mathlib or move to mathlib
lemma strong_downward_induction_on' {α : Type*} {p : finset α → Prop} {A : set (finset α)}
  {n : ℕ} (hA : ∀ {t : finset α}, t ∈ A → t.card ≤ n) {s : finset α} (hs : s ∈ A)
  (h : ∀ {t₁}, t₁ ∈ A → (∀ {t₂}, t₂ ∈ A → t₁ ⊂ t₂ → p t₂) → p t₁) :
  p s :=
@strong_downward_induction_on _ (λ t₁, t₁ ∈ A → p t₁) n (λ t₁ ih ht₁, h ht₁ (λ Z hZ₁ hZ₂,
  ih (hA hZ₁) hZ₂ hZ₁)) s (hA hs) hs

end finset

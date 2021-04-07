import data.finset.basic
import combinatorics.simplicial_complex.to_move.multiset
import combinatorics.simplicial_complex.to_move.set

variables {α : Type*}

namespace finset

@[simp] lemma attach_nonempty_iff (s : finset α) : s.attach.nonempty ↔ s.nonempty :=
by simp [←card_pos]

lemma exists_min [semilattice_inf α]
  {s : finset α} (hs₁ : s.nonempty) (hs₂ : ∀ x y ∈ s, x ⊓ y ∈ s):
  ∃ z ∈ s, ∀ y ∈ s, z ≤ y :=
@multiset.exists_min_of_inf_closed _ _ s.1 (by simpa using hs₁.ne_empty) hs₂

--Are those two in mathlib?
lemma ssubset_of_ssubset_of_subset {X Y Z : finset α} (hXY : X ⊂ Y) (hYZ : Y ⊆ Z) : X ⊂ Z :=
  ⟨subset.trans hXY.1 hYZ, (λ hZX, hXY.2 (subset.trans hYZ hZX))⟩
lemma ssubset_of_subset_of_ssubset {X Y Z : finset α} (hXY : X ⊆ Y) (hYZ : Y ⊂ Z) : X ⊂ Z :=
  ⟨subset.trans hXY hYZ.1, (λ hZX, hYZ.2 (subset.trans hZX hXY))⟩

--and this one?
lemma union_subset_iff [decidable_eq α] {X Y Z : finset α} : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { rintro hXYZ,
    split,
    exact subset.trans (subset_union_left X Y) hXYZ,
    exact subset.trans (subset_union_right X Y) hXYZ },
  rintro ⟨hXZ, hYZ⟩,
  exact union_subset hXZ hYZ,
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

lemma subset_iff_inter_eq_left [decidable_eq α] {X Y : finset α}  :
  X ⊆ Y ↔ X ∩ Y = X :=
begin
  split,
  { rintro h,
    ext t,
    simp only [and_iff_left_iff_imp, finset.mem_inter],
    apply h },
  rintro h,
  rw ← h,
  exact inter_subset_right _ _,
end

lemma subset_iff_inter_eq_right [decidable_eq α] {X Y : finset α} :
  X ⊆ Y ↔ Y ∩ X = X :=
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
  { rintro (rfl | rfl),
    { apply empty_subset },
    { apply subset.refl } }
end

lemma ssubset_singleton_iff_eq_empty (x : α) (X : finset α) : X ⊂ {x} ↔ X = ∅ :=
begin
  rw [←coe_ssubset, coe_singleton, set.ssubset_singleton_iff_eq_empty x X],
  simp,
end

lemma eq_empty_of_ssubset_singleton {x : α} {X : finset α} (hX : X ⊂ {x}) : X = ∅ :=
(ssubset_singleton_iff_eq_empty _ _).1 hX

lemma exists_of_ssubset {s t : finset α} (h : s ⊂ t) : (∃x∈t, x ∉ s) :=
set.exists_of_ssubset h

lemma coe_eq_empty_iff {X : finset α} : (X : set α) = ∅ ↔ X = ∅ :=
by simp [set.ext_iff, ext_iff]

lemma strong_downward_induction_on {α : Type*} {p : finset α → Prop}
  {n : ℕ} (h : ∀ {Y}, (∀ {Z : finset α}, Z.card ≤ n → Y ⊂ Z → p Z) → p Y) :
  ∀ {y : finset α}, y.card ≤ n → p y :=
begin
  intro y,
  apply well_founded.induction (measure_wf (λ (X : finset α), n - X.card)) y,
  exact (λ x ih hx, h (λ z hz xz, ih _ ((nat.sub_lt_sub_left_iff hz).2 (finset.card_lt_card xz)) hz)),
end

-- TODO: find in mathlib or move to mathlib
lemma strong_downward_induction_on' {α : Type*} {p : finset α → Prop} {A : set (finset α)}
  {n : ℕ} (hA : ∀ {X}, X ∈ A → (X : finset α).card ≤ n) {X : finset α} (hX : X ∈ A) :
  (∀ {Y}, Y ∈ A → (∀ {Z}, Z ∈ A → Y ⊂ Z → p Z) → p Y) → p X := λ h,
begin
  apply @strong_downward_induction_on _ (λ Y, Y ∈ A → p Y) n _ X (hA hX) hX,
  exact λ Y ih hY, h hY (λ Z hZ₁ hZ₂, ih (hA hZ₁) hZ₂ hZ₁),
end

end finset

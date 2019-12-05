/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import data.set.intervals.basic algebra.order_functions data.set.lattice

universe u

namespace set

section decidable_linear_order
variables {α : Type u} [decidable_linear_order α] {a a₁ a₂ b b₁ b₂ : α}

@[simp] lemma Ico_diff_Iio {a b c : α} : Ico a b \ Iio c = Ico (max a c) b :=
set.ext $ by simp [Ico, Iio, iff_def, max_le_iff] {contextual:=tt}

@[simp] lemma Ico_inter_Iio {a b c : α} : Ico a b ∩ Iio c = Ico a (min b c) :=
set.ext $ by simp [Ico, Iio, iff_def, lt_min_iff] {contextual:=tt}

/-- If two half-open intervals are disjoint and the endpoint of one lies in the other,
  then it must be equal to the endpoint of the other. -/
lemma eq_of_Ico_disjoint {x₁ x₂ y₁ y₂ : α}
  (h : disjoint (Ico x₁ x₂) (Ico y₁ y₂)) (hx : x₁ < x₂) (hy : y₁ < y₂) (h2 : x₂ ∈ Ico y₁ y₂) :
  y₁ = x₂ :=
begin
  apply le_antisymm h2.1, rw [←not_lt], intro h3,
  apply not_disjoint_iff.mpr ⟨max y₁ x₁, _, _⟩ h,
  simp [le_refl, h3, hx],
  simp [le_refl, hy, lt_trans hx h2.2]
end

end decidable_linear_order

section ordered_comm_group

variables {α : Type u} [ordered_comm_group α]

lemma image_neg_Iio (r : α) : image (λz, -z) (Iio r) = Ioi (-r) :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp only [mem_Ioi, neg_lt_neg_iff],
    exact hz'.1 },
  { intros hz,
    simp only [mem_image, mem_Iio],
    use -z,
    simp [hz],
    exact neg_lt.1 hz }
end

lemma image_neg_Iic (r : α)  : image (λz, -z) (Iic r) = Ici (-r) :=
begin
  apply set.ext,
  intros z,
  apply iff.intro,
  { intros hz,
    apply exists.elim hz,
    intros z' hz',
    rw [←hz'.2],
    simp only [neg_le_neg_iff, mem_Ici],
    exact hz'.1 },
  { intros hz,
    simp only [mem_image, mem_Iic],
    use -z,
    simp [hz],
    exact neg_le.1 hz }
end

end ordered_comm_group

section decidable_linear_ordered_comm_group

variables {α : Type u} [decidable_linear_ordered_comm_group α]

/-- If we remove a smaller interval from a larger, the result is nonempty -/
lemma nonempty_Ico_sdiff {x dx y dy : α} (h : dy < dx) (hx : 0 < dx) :
  nonempty ↥(Ico x (x + dx) \ Ico y (y + dy)) :=
begin
  cases lt_or_le x y with h' h',
  { use x, simp* },
  { use max x (x + dy), simp [*, le_refl] }
end

end decidable_linear_ordered_comm_group

end set

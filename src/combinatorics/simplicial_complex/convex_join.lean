import analysis.convex.basic
import linear_algebra.affine_space.affine_subspace
import combinatorics.simplicial_complex.to_move.default

open set

variables {E : Type*} [add_comm_group E] [module ℝ E] {x y : E} {A B C D : set E} {c : set (set E)}

def convex_join (A B : set E) :
  set E :=
A ∪ B ∪ ⋃ a b (ha : a ∈ A) (hb : b ∈ B), open_segment a b

/-The three other possible defs of `convex_join`. They are *not* equivalent.


This one is the weakest, not even respecting
`convex_hull (A ∪ B) = convex_join (convex_hull A) (convex_hull B)` as it doesn't cope well with
`A = ∅` or `B = ∅`.

def convex_join (A B : set E) :
  set E :=
⋃ a b (ha : a ∈ A) (hb : b ∈ B), segment a b


That one is stronger than the one I went for. It respects
`convex_hull (A ∪ B) = convex_join (convex_hull A) (convex_hull B)` and even adds some segments, but
doesn't unfold nicely as it breaks into four cases `(a ∈ A ∨ a ∈ B) ∧ (b ∈ A ∨ b ∈ B)` two of which
are hard but essentially the same.

def convex_join (A B : set E) :
  set E :=
⋃ a b (ha : a ∈ A ∪ B) (hb : b ∈ A ∪ B), segment a b
-/

lemma mem_convex_join_iff :
  x ∈ convex_join A B ↔ x ∈ A ∪ B ∨ ∃ a b : E, a ∈ A ∧ b ∈ B ∧ x ∈ open_segment a b :=
begin
  unfold convex_join,
  simp,
end

lemma convex_join_comm :
  convex_join A B = convex_join B A :=
begin
  ext x,
  rw [mem_convex_join_iff, mem_convex_join_iff, union_comm],
  split;
  { rintro (hx | ⟨a, b, ha, hb, hx⟩),
    { left,
      exact hx },
    right,
    rw open_segment_symm at hx,
    exact ⟨b, a, hb, ha, hx⟩ }
end

lemma subset_convex_join_left (A B : set E) :
  A ⊆ convex_join A B :=
begin
  rintro x hx,
  left,
  left,
  exact hx,
end

lemma subset_convex_join_right (A B : set E) :
  B ⊆ convex_join A B :=
begin
  rintro x hx,
  left,
  right,
  exact hx,
end

lemma convex_join_mono_left (hAB : A ⊆ B) (C : set E) :
  convex_join A C ⊆ convex_join B C :=
begin
  sorry
end

lemma convex_join_mono_right (A : set E) (hBC : B ⊆ C) :
  convex_join A B ⊆ convex_join A C :=
begin
  sorry
end

lemma convex_join_mono (hAC : A ⊆ C) (hBD : B ⊆ D) :
  convex_join A B ⊆ convex_join C D :=
subset.trans (convex_join_mono_left hAC B) (convex_join_mono_right C hBD)

lemma union_subset_convex_join (A B : set E) :
  A ∪ B ⊆ convex_join A B :=
union_subset (subset_convex_join_left A B) (subset_convex_join_right A B)

lemma convex_join_empty :
  convex_join A ∅ = A :=
begin
  unfold convex_join,
  rw union_empty,
  simp,
end

lemma empty_convex_join :
  convex_join ∅ B = B :=
begin
  rw convex_join_comm,
  exact convex_join_empty,
end

lemma convex_join_eq_of_nonempty (hA : A.nonempty) (hB : B.nonempty) :
  convex_join A B = ⋃ a b (ha : a ∈ A) (hb : b ∈ B), segment a b :=
begin
  sorry
  /-
  apply union_eq_self_of_subset_left,
  rintro x (hx | hx),
  { obtain ⟨b, hb⟩ := hB,
    simp,
    refine ⟨x, hx, b, hb, left_mem_segment _ _⟩ },
  obtain ⟨a, ha⟩ := hA,
  simp,
  refine ⟨a, ha, x, hx, right_mem_segment _ _⟩,-/
end

lemma convex_convex_join (hA : convex A) (hB : convex B) :
  convex (convex_join A B) :=
begin
  cases A.eq_empty_or_nonempty with hAemp hAnemp,
  {
    rw [hAemp, empty_convex_join],
    exact hB,
  },
  cases B.eq_empty_or_nonempty with hBemp hBnemp,
  {
    rw [hBemp, convex_join_empty],
    exact hA,
  },
  rw convex_join_eq_of_nonempty hAnemp hBnemp,
  rintro X Y hX hY x y hx hy hxy,
  simp at *,
  obtain ⟨AX, hAX, BX, hBX, aX, bX, haX, hbX, habX, hX⟩ := hX,
  obtain ⟨AY, hAY, BY, hBY, aY, bY, haY, hbY, habY, hY⟩ := hY,
  refine ⟨(1 - y*aY/(x*aX + y*aY)) • AX + (y*aY/(x*aX + y*aY)) • AY, hA hAX hAY _ _ _,
          (1 - y*bY/(x*bX + y*bY)) • BX + (y*bY/(x*bX + y*bY)) • BY, hB hBX hBY _ _ _,
          x*aX + y*aY, x*bX + y*bY, _, _, _, _⟩,
  {
    sorry
  },
  {
    sorry
  },
  { exact sub_add_cancel 1 _ }, --use one of `sub_add_cancel 1 _` and `add_sub_cancel'_right _ 1`
  {
    sorry
  },
  {
    sorry
  },
  { exact sub_add_cancel 1 _ },
  { exact add_nonneg (mul_nonneg hx haX) (mul_nonneg hy haY) },
  { exact add_nonneg (mul_nonneg hx hbX) (mul_nonneg hy hbY) },
  { calc
      x * aX + y * aY + (x * bX + y * bY)
          = x * (aX + bX) + y * (aY + bY) : by ring
      ... = 1 : by rw [habX, habY, mul_one, mul_one, hxy] },
  sorry
end

lemma convex_join_subset_convex_hull_union (A B : set E) :
  convex_join A B ⊆ convex_hull (A ∪ B) :=
begin
  cases A.eq_empty_or_nonempty with hAemp hAnemp,
  { rw [hAemp, empty_union, empty_convex_join],
    exact subset_convex_hull B },
  cases B.eq_empty_or_nonempty with hBemp hBnemp,
  { rw [hBemp, union_empty, convex_join_empty],
    exact subset_convex_hull A },
  rw convex_join_eq_of_nonempty hAnemp hBnemp,
  rintro x hx,
  simp at hx,
  obtain ⟨a, ha, b, hb, hx⟩ := hx,
  exact convex_iff_segment_subset.1 (convex_convex_hull _) (convex_hull_mono
    (subset_union_left _ _) (subset_convex_hull A ha)) (convex_hull_mono (subset_union_right _ _)
    (subset_convex_hull B hb)) hx,
end

lemma convex_hull_union_of_convex (hA : convex A) (hB : convex B) :
  convex_hull (A ∪ B) = convex_join A B :=
begin
  apply (convex_hull_min (union_subset_convex_join A B) (convex_convex_join hA hB)).antisymm,
  exact (convex_join_subset_convex_hull_union A B),
end

lemma convex_hull_union (A B : set E) :
  convex_hull (A ∪ B) = convex_join (convex_hull A) (convex_hull B) :=
begin
  rw [←convex_hull_convex_hull_union, ←convex_hull_self_union_convex_hull],
  exact convex_hull_union_of_convex (convex_convex_hull A) (convex_convex_hull B),
end

lemma convex_hull_insert (hA : A.nonempty) :
  convex_hull (insert x A) = ⋃ a ∈ convex_hull A, segment x a :=
begin
  rw [insert_eq, ←convex_hull_self_union_convex_hull, convex_hull_union_of_convex
  (convex_singleton x) (convex_convex_hull A), convex_join_eq_of_nonempty (singleton_nonempty x)
  (convex_hull_nonempty_iff.2 hA)],
  ext x,
  simp,
end

lemma convex_join_min {A B C : set E} (hAC : A ⊆ C) (hBC : B ⊆ C) (hC : convex C) :
  convex_join A B ⊆ C :=
begin
  refine subset.trans (convex_join_mono (subset_convex_hull A) (subset_convex_hull B)) _,
  rw ←convex_hull_union,
  exact convex_hull_min (union_subset hAC hBC) hC,
end

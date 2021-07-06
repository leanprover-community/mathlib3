/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
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

lemma convex_join_comm (A B : set E) :
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

lemma convex_join_subset_convex_join_left (hAB : A ⊆ B) (C : set E) :
  convex_join A C ⊆ convex_join B C :=
begin
  rintro x (hx | hx),
  { left,
    exact union_subset_union_left C hAB hx },
  right,
  simp only [mem_Union] at ⊢ hx,
  obtain ⟨a, c, ha, hc, hx⟩ := hx,
  exact ⟨a, c, hAB ha, hc, hx⟩,
end

lemma convex_join_subset_convex_join_right (A : set E) (hBC : B ⊆ C) :
  convex_join A B ⊆ convex_join A C :=
begin
  rw [convex_join_comm, convex_join_comm A C],
  exact convex_join_subset_convex_join_left hBC A,
end

lemma convex_join_subset_convex_join (hAC : A ⊆ C) (hBD : B ⊆ D) :
  convex_join A B ⊆ convex_join C D :=
subset.trans (convex_join_subset_convex_join_left hAC B)
  (convex_join_subset_convex_join_right C hBD)

lemma union_subset_convex_join (A B : set E) :
  A ∪ B ⊆ convex_join A B :=
union_subset (subset_convex_join_left A B) (subset_convex_join_right A B)

lemma convex_join_empty :
  convex_join A ∅ = A :=
begin
  unfold convex_join,
  rw union_empty,
  simp only [mem_empty_eq, Union_neg, Union_empty, not_false_iff, union_empty],
end

lemma empty_convex_join :
  convex_join ∅ B = B :=
begin
  rw convex_join_comm,
  exact convex_join_empty,
end

lemma segment_subset_convex_join {a b : E} (ha : a ∈ A) (hb : b ∈ B) :
  segment a b ⊆ convex_join A B :=
begin
  rintro x hx,
  obtain rfl | rfl | hx := eq_left_or_right_or_mem_open_segment_of_mem_segment hx,
  { exact subset_convex_join_left A B ha },
  { exact subset_convex_join_right A B hb },
  right,
  simp only [mem_Union],
  exact ⟨a, b, ha, hb, hx⟩,
end

lemma convex_join_eq_of_nonempty (hA : A.nonempty) (hB : B.nonempty) :
  convex_join A B = ⋃ a b (ha : a ∈ A) (hb : b ∈ B), segment a b :=
begin
  ext x,
  simp only [mem_convex_join_iff, mem_Union],
  split,
  { rintro ((hx | hx) | ⟨a, b, ha, hb, hx⟩),
    { obtain ⟨b, hb⟩ := hB,
      exact ⟨x, b, hx, hb, left_mem_segment x b⟩ },
    { obtain ⟨a, ha⟩ := hA,
      exact ⟨a, x, ha, hx, right_mem_segment a x⟩ },
    exact ⟨a, b, ha, hb, open_segment_subset_segment a b hx⟩ },
  rintro ⟨a, b, ha, hb, hx⟩,
  obtain rfl | (rfl | hx) := eq_left_or_right_or_mem_open_segment_of_mem_segment hx,
  { left,
    exact subset_union_left _ _ ha },
  { left,
    exact subset_union_right _ _ hb },
  right,
  exact ⟨a, b, ha, hb, hx⟩,
end

lemma convex_hull_quadruple {a b c d : E} :
  convex_join (segment a b) (segment c d) = convex_hull {a, b, c, d} :=
begin
  rw [finite.convex_hull_eq, convex_join_eq_of_nonempty ⟨a, left_mem_segment _ _⟩
    ⟨c, left_mem_segment _ _⟩],
  swap,
  { simp only [finite.insert, finite_singleton] },
  ext x,
  simp only [mem_Union],
  split,
  { rintro ⟨y, z, ⟨ya, yb, hya, hyb, hyab, hy⟩, ⟨zc, zd, hzc, hzd, hzcd, hz⟩,
      ⟨xy, xz, hxy, hxz, hxyz, hx⟩⟩,
    sorry
  },
  rintro ⟨w, hw₀, hw₁, hx⟩,
  rw ←hx,
  let y := (1 - (w b)/(w a + w b)) • a + ((w b)/(w a + w b)) • b,
  let z := (1 - (w d)/(w c + w d)) • c + ((w d)/(w c + w d)) • d,
  have hwa : 0 ≤ w a := hw₀ a (by simp only [true_or, eq_self_iff_true, mem_insert_iff]),
  have hwb : 0 ≤ w b := hw₀ b (by simp only [true_or, or_true, eq_self_iff_true, mem_insert_iff]),
  have hwc : 0 ≤ w c := hw₀ c (by simp only [true_or, or_true, eq_self_iff_true, mem_insert_iff]),
  have hwd : 0 ≤ w d := hw₀ d (by simp only [or_true, eq_self_iff_true, mem_insert_iff,
    mem_singleton_iff]),
  have hwab : 0 ≤ w a + w b := add_nonneg hwa hwb,
  have hwcd : 0 ≤ w c + w d := add_nonneg hwc hwd,
  have hy : y ∈ segment a b,
  { refine ⟨(1 - (w b)/(w a + w b)), ((w b)/(w a + w b)), _, _, _, rfl⟩,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 hwa) hwab },
    { exact div_nonneg hwb hwab },
    exact sub_add_cancel 1 _ },
  have hz : z ∈ segment c d,
  { refine ⟨(1 - (w d)/(w c + w d)), ((w d)/(w c + w d)), _, _, _, rfl⟩,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 hwc) hwcd },
    { exact div_nonneg hwd hwcd },
    exact sub_add_cancel 1 _ },
  refine ⟨y, z, hy, hz, w a + w b, w c + w d, hwab, hwcd, _, _⟩,
  {
    rw ← hw₁,
    sorry,
  },
  sorry
  /-cases A.eq_empty_or_nonempty with hAemp hAnemp,
  { rw [hAemp, empty_convex_join],
    exact hB },
  cases B.eq_empty_or_nonempty with hBemp hBnemp,
  { rw [hBemp, convex_join_empty],
    exact hA },
  rw convex_join_eq_of_nonempty hAnemp hBnemp,
  rintro x y hx hy wx wy hwx hwy hwxy,
  simp only [mem_Union] at ⊢ hy hx,
  obtain ⟨ax, bx, hax, hbx, wax, wbx, hwax, hwbx, hwabx, hx⟩ := hx,
  obtain ⟨ay, b_y, hay, hby, way, wby, hway, hwby, hwaby, hy⟩ := hy,
  let az := (1 - wy*way/(wx*wax + wy*way)) • ax + (wy*way/(wx*wax + wy*way)) • ay,
  let bz := (1 - wy*wby/(wx*wbx + wy*wby)) • bx + (wy*wby/(wx*wbx + wy*wby)) • b_y,
  have da_nonneg : 0 ≤ wx*wax + wy*way := add_nonneg (mul_nonneg hwx hwax) (mul_nonneg hwy hway),
  have db_nonneg : 0 ≤ wx*wbx + wy*wby := add_nonneg (mul_nonneg hwx hwbx) (mul_nonneg hwy hwby),
  have haz : az ∈ A,
  { apply hA hax hay,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 (mul_nonneg hwx hwax)) da_nonneg },
    { exact div_nonneg (mul_nonneg hwy hway) da_nonneg },
    exact sub_add_cancel 1 _ },
  have hbz : bz ∈ B,
  { apply hB hbx hby,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 (mul_nonneg hwx hwbx)) db_nonneg },
    { exact div_nonneg (mul_nonneg hwy hwby) db_nonneg },
    exact sub_add_cancel 1 _ },
  refine ⟨az, bz, haz, hbz, wx * wax + wy * way, wx * wbx + wy * wby, da_nonneg, db_nonneg, _, _⟩,
  {
    calc
      wx * wax + wy * way + (wx * wbx + wy * wby)
          = wx * (wax + wbx) + wy * (way + wby) : by ring
      ... = 1 : by rw [hwabx, hwaby, mul_one, mul_one, hwxy]
  },
  rw [←hx, ←hy],
  simp,-/
  /-rw convex_iff_open_segment_subset at ⊢ hB hA,
  simp only [mem_convex_join_iff, mem_Union],
  rintro x y ((hx | hx) | ⟨a, b, ha, hb, hx⟩) hy, --((hy | hy) | ⟨a, b, ha, hb, hy⟩)
  {
    obtain ((hy | hy) | ⟨a, b, ha, hb, hy⟩) := hy,
    exact subset.trans (hA hx hy) (subset_convex_join_left A B),
  },
  {
    rintro z hz,
    simp only [mem_convex_join_iff, mem_Union],
    right,
    exact ⟨x, y, hx, hy, hz⟩,
  },
  {

  }-/
end

lemma convex_hull_triple {a b c : E} :
  convex_join (segment a b) {c} = convex_hull {a, b, c} :=
by rw [←pair_eq_singleton, ←convex_hull_quadruple, segment_same, pair_eq_singleton]

lemma convex_convex_join (hA : convex A) (hB : convex B) :
  convex (convex_join A B) :=
begin
  cases A.eq_empty_or_nonempty with hAemp hAnemp,
  { rw [hAemp, empty_convex_join],
    exact hB },
  cases B.eq_empty_or_nonempty with hBemp hBnemp,
  { rw [hBemp, convex_join_empty],
    exact hA },
  rw convex_join_eq_of_nonempty hAnemp hBnemp,
  rw convex_iff_segment_subset at ⊢ hB hA,
  rintro x y hx hy z hz,
  simp only [mem_Union] at ⊢ hy hx,
  obtain ⟨ax, bx, hax, hbx, hx⟩ := hx,
  obtain ⟨ay, b_y, hay, hby, hy⟩ := hy,
  have h : z ∈ convex_join (segment ax ay) (segment bx b_y),
  { have triv : ({ax, ay, bx, b_y} : set E) = {ax, bx, ay, b_y} := by simp only [set.insert_comm],
    rw [convex_hull_quadruple, triv, ←convex_hull_quadruple],
    exact segment_subset_convex_join hx hy hz },
  rw convex_join_eq_of_nonempty ⟨ax, left_mem_segment _ _⟩ ⟨bx, left_mem_segment _ _⟩ at h,
  simp only [mem_Union] at h,
  obtain ⟨az, bz, haz, hbz, hz⟩ := h,
  exact ⟨az, bz, hA hax hay haz, hB hbx hby hbz, hz⟩,
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
  simp only [mem_Union] at hx,
  obtain ⟨a, b, ha, hb, hx⟩ := hx,
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
  refine subset.trans (convex_join_subset_convex_join (subset_convex_hull A) (subset_convex_hull B))
    _,
  rw ←convex_hull_union,
  exact convex_hull_min (union_subset hAC hBC) hC,
end

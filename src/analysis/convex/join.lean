/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import analysis.convex.combination
import linear_algebra.affine_space.affine_subspace

/-!
# Convex join
-/

lemma exists₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
  {p : Π i₁, κ₁ i₁ → Π i₂, κ₂ i₂ → Prop} :
  (∃ i₁ j₁ i₂ j₂, p i₁ j₁ i₂ j₂) ↔ ∃ i₂ j₂ i₁ j₁, p i₁ j₁ i₂ j₂ :=
by simp only [@exists_comm (κ₁ _), @exists_comm ι₁]

namespace set
variables {α : Type*}

@[simp] lemma insert_singleton (a : α) : insert a ({a} : set α) = {a} :=
insert_eq_of_mem $ mem_singleton _

@[simp] lemma insert_idem (a : α) (s : set α) : insert a (insert a s) = insert a s :=
insert_eq_of_mem $ mem_insert _ _

@[simp] lemma finite.to_finset_singleton {a : α} (ha : ({a} : set α).finite) : ha.to_finset = {a} :=
finset.ext $ by simp

variables [decidable_eq α] {a : α} {s : set α}

@[simp] lemma finite.to_finset_insert' (hs : (insert a s).finite) :
  hs.to_finset = insert a (hs.subset $ subset_insert _ _).to_finset :=
finset.ext $ by simp

end set

open set

section
variables {𝕜 E ι : Type*} [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {s X Y : set E}

-- can be proven from the stuff about closure operators
lemma convex_hull_convex_hull_union :
  convex_hull 𝕜 (convex_hull 𝕜 X ∪ Y) = convex_hull 𝕜 (X ∪ Y) :=
subset.antisymm (convex_hull_min (union_subset (convex_hull_mono (subset_union_left X Y))
  (subset.trans (subset_convex_hull 𝕜 Y) (convex_hull_mono (subset_union_right X Y))))
  (convex_convex_hull 𝕜 _)) (convex_hull_mono (union_subset_union_left _ (subset_convex_hull 𝕜 _)))

-- can be proven from the stuff about closure operators
lemma convex_hull_self_union_convex_hull :
  convex_hull 𝕜 (X ∪ convex_hull 𝕜 Y) = convex_hull 𝕜 (X ∪ Y) :=
begin
  rw [union_comm, union_comm X Y],
  exact convex_hull_convex_hull_union,
end

end

variables {ι : Sort*} {𝕜 E : Type*}

section ordered_semiring
variables [ordered_semiring 𝕜] [add_comm_monoid E] [module 𝕜 E] {s t s₁ s₂ t₁ t₂ u : set E}
  {x y : E}

variables (𝕜)

/-- The join of two sets is the union of the segments joining them. This can be interpreted as the
topological join, but within the original space. -/
def convex_join (s t : set E) : set E := ⋃ (x ∈ s) (y ∈ t), segment 𝕜 x y

variables {𝕜}

lemma mem_convex_join : x ∈ convex_join 𝕜 s t ↔ ∃ (a ∈ s) (b ∈ t), x ∈ segment 𝕜 a b :=
by simp [convex_join]

lemma convex_join_comm (s t : set E) : convex_join 𝕜 s t = convex_join 𝕜 t s :=
by { ext x, rw [mem_convex_join, mem_convex_join, exists₂_comm], simp_rw segment_symm }

lemma convex_join_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : convex_join 𝕜 s₁ t₁ ⊆ convex_join 𝕜 s₂ t₂ :=
bUnion_mono hs $ λ x hx, bUnion_mono ht $ λ y hy, subset.rfl

lemma convex_join_mono_left (hs : s₁ ⊆ s₂) : convex_join 𝕜 s₁ t ⊆ convex_join 𝕜 s₂ t :=
convex_join_mono hs subset.rfl

lemma convex_join_mono_right (ht : t₁ ⊆ t₂) : convex_join 𝕜 s t₁ ⊆ convex_join 𝕜 s t₂ :=
convex_join_mono subset.rfl ht

@[simp] lemma convex_join_empty_left (t : set E) : convex_join 𝕜 ∅ t = ∅ := by simp [convex_join]
@[simp] lemma convex_join_empty_right (s : set E) : convex_join 𝕜 s ∅ = ∅ := by simp [convex_join]

@[simp] lemma convex_join_singleton_left (t : set E) (x : E) :
  convex_join 𝕜 {x} t = ⋃ (y ∈ t), segment 𝕜 x y := by simp [convex_join]

@[simp] lemma convex_join_singleton_right (s : set E) (y : E) :
  convex_join 𝕜 s {y} = ⋃ (x ∈ s), segment 𝕜 x y := by simp [convex_join]

@[simp] lemma convex_join_singletons (x : E) : convex_join 𝕜 {x} {y} = segment 𝕜 x y :=
by simp [convex_join]

@[simp] lemma convex_join_union_left (s₁ s₂ t : set E) :
  convex_join 𝕜 (s₁ ∪ s₂) t = convex_join 𝕜 s₁ t ∪ convex_join 𝕜 s₂ t :=
by simp_rw [convex_join, mem_union_eq, Union_or, Union_union_distrib]

@[simp] lemma convex_join_union_right (s t₁ t₂ : set E) :
  convex_join 𝕜 s (t₁ ∪ t₂) = convex_join 𝕜 s t₁ ∪ convex_join 𝕜 s t₂ :=
by simp_rw [convex_join, mem_union_eq, Union_or, Union_union_distrib]

@[simp] lemma convex_join_Union_left (s : ι → set E) (t : set E) :
  convex_join 𝕜 (⋃ i, s i) t = ⋃ i, convex_join 𝕜 (s i) t :=
by { simp_rw [convex_join, mem_Union, Union_exists], exact Union_comm _ }

@[simp] lemma convex_join_Union_right (s : set E) (t : ι → set E) :
  convex_join 𝕜 s (⋃ i, t i) = ⋃ i, convex_join 𝕜 s (t i) :=
by simp_rw [convex_join_comm s, convex_join_Union_left]

lemma segment_subset_convex_join (hx : x ∈ s) (hy : y ∈ t) : segment 𝕜 x y ⊆ convex_join 𝕜 s t :=
(subset_Union₂ y hy).trans (subset_Union₂ x hx)

lemma subset_convex_join_left (h : t.nonempty) : s ⊆ convex_join 𝕜 s t :=
λ x hx, let ⟨y, hy⟩ := h in segment_subset_convex_join hx hy $ left_mem_segment _ _ _

lemma subset_convex_join_right (h : s.nonempty) : t ⊆ convex_join 𝕜 s t :=
λ y hy, let ⟨x, hx⟩ := h in segment_subset_convex_join hx hy $ right_mem_segment _ _ _

lemma convex_join_subset (hs : s ⊆ u) (ht : t ⊆ u) (hu : convex 𝕜 u) : convex_join 𝕜 s t ⊆ u :=
Union₂_subset $ λ x hx, Union₂_subset $ λ y hy, hu.segment_subset (hs hx) (ht hy)

lemma convex_join_subset_convex_hull (s t : set E) : convex_join 𝕜 s t ⊆ convex_hull 𝕜 (s ∪ t) :=
convex_join_subset ((subset_union_left _ _).trans $ subset_convex_hull _ _)
  ((subset_union_right _ _).trans $ subset_convex_hull _ _) $ convex_convex_hull _ _

end ordered_semiring

section linear_ordered_field
variables [linear_ordered_field 𝕜] [add_comm_group E] [module 𝕜 E] {s t u : set E} {x y : E}

lemma segment_subset_convex_hull (hx : x ∈ s) (hy : y ∈ s) : segment 𝕜 x y ⊆ convex_hull 𝕜 s :=
(convex_convex_hull _ _).segment_subset (subset_convex_hull _ _ hx) (subset_convex_hull _ _ hy)

@[simp] lemma convex_hull_pair (x y : E) : convex_hull 𝕜 {x, y} = segment 𝕜 x y :=
begin
  refine (convex_hull_min _ $ convex_segment _ _).antisymm
    (segment_subset_convex_hull (mem_insert _ _) $ mem_insert_of_mem _ $ mem_singleton _),
  rw [insert_subset, singleton_subset_iff],
  exact ⟨left_mem_segment _ _ _, right_mem_segment _ _ _⟩,
end

lemma convex_join_segments (a b c d : E) :
  convex_join 𝕜 (segment 𝕜 a b) (segment 𝕜 c d) = convex_hull 𝕜 {a, b, c, d} :=
begin
  refine (convex_join_subset _ _ $ convex_convex_hull _ _).antisymm (λ x, _),
  any_goals { refine segment_subset_convex_hull _ _;
    simp only [mem_singleton, mem_insert_iff, eq_self_iff_true, true_or, or_true] },
  rw [finite.convex_hull_eq, mem_convex_join],
  swap,
  { simp only [finite.insert, finite_singleton] },
  rintro ⟨w, hw₀, hw₁, hx⟩,
  rw ←hx,
  let y := (1 - w b/(w a + w b)) • a + (w b/(w a + w b)) • b,
  let z := (1 - w d/(w c + w d)) • c + (w d/(w c + w d)) • d,
  have hwa : 0 ≤ w a := hw₀ a (by simp only [true_or, eq_self_iff_true, mem_insert_iff]),
  have hwb : 0 ≤ w b := hw₀ b (by simp only [true_or, or_true, eq_self_iff_true, mem_insert_iff]),
  have hwc : 0 ≤ w c := hw₀ c (by simp only [true_or, or_true, eq_self_iff_true, mem_insert_iff]),
  have hwd : 0 ≤ w d := hw₀ d (by simp only [or_true, eq_self_iff_true, mem_insert_iff,
    mem_singleton_iff]),
  have hwab : 0 ≤ w a + w b := add_nonneg hwa hwb,
  have hwcd : 0 ≤ w c + w d := add_nonneg hwc hwd,
  have hy : y ∈ segment 𝕜 a b,
  { refine ⟨1 - w b / (w a + w b), w b / (w a + w b), _, _, _, rfl⟩,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 hwa) hwab },
    { exact div_nonneg hwb hwab },
    exact sub_add_cancel 1 _ },
  have hz : z ∈ segment 𝕜 c d,
  { refine ⟨1 - w d / (w c + w d), w d / (w c + w d), _, _, _, rfl⟩,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 hwc) hwcd },
    { exact div_nonneg hwd hwcd },
    exact sub_add_cancel 1 _ },
  refine ⟨y, hy, z, hz, w a + w b, w c + w d, hwab, hwcd, _, _⟩,
  { rw ← hw₁,
    classical,
    simp_rw [finite.to_finset_insert', finite.to_finset_singleton],
    sorry,
  },
  sorry
  /-cases s.eq_empty_or_nonempty with hAemp hAnemp,
  { rw [hAemp, convex_join_empty_left],
    exact ht },
  cases t.eq_empty_or_nonempty with hBemp hBnemp,
  { rw [hBemp, convex_join_empty_right],
    exact hs },
  rw convex_join_eq_of_nonempty hAnemp hBnemp,
  rintro x y hx hy wx wy hwx hwy hwxy,
  simp only [mem_Union] at ⊢ hy hx,
  obtain ⟨xa, xb, hxa, hxb, wax, wbx, hwax, hwbx, hwabx, hx⟩ := hx,
  obtain ⟨ya, yb, hya, hyb, way, wby, hway, hwby, hwaby, hy⟩ := hy,
  let az := (1 - wy*way/(wx*wax + wy*way)) • xa + (wy*way/(wx*wax + wy*way)) • ya,
  let bz := (1 - wy*wby/(wx*wbx + wy*wby)) • xb + (wy*wby/(wx*wbx + wy*wby)) • yb,
  have da_nonneg : 0 ≤ wx*wax + wy*way := add_nonneg (mul_nonneg hwx hwax) (mul_nonneg hwy hway),
  have db_nonneg : 0 ≤ wx*wbx + wy*wby := add_nonneg (mul_nonneg hwx hwbx) (mul_nonneg hwy hwby),
  have haz : az ∈ s,
  { apply hs hxa hya,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 (mul_nonneg hwx hwax)) da_nonneg },
    { exact div_nonneg (mul_nonneg hwy hway) da_nonneg },
    exact sub_add_cancel 1 _ },
  have hbz : bz ∈ t,
  { apply ht hxb hyb,
    { rw sub_nonneg,
      exact div_le_one_of_le ((le_add_iff_nonneg_left _).2 (mul_nonneg hwx hwbx)) db_nonneg },
    { exact div_nonneg (mul_nonneg hwy hwby) db_nonneg },
    exact sub_add_cancel 1 _ },
  refine ⟨az, bz, haz, hbz, wx * wax + wy * way, wx * wbx + wy * wby, da_nonneg, db_nonneg, _, _⟩,
  { calc
      wx * wax + wy * way + (wx * wbx + wy * wby)
          = wx * (wax + wbx) + wy * (way + wby) : by ring
      ... = 1 : by rw [hwabx, hwaby, mul_one, mul_one, hwxy]
  },
  rw [←hx, ←hy],
  simp,-/
  /-rw convex_iff_open_segment_subset at ⊢ ht hs,
  simp only [mem_convex_join, mem_Union],
  rintro x y ((hx | hx) | ⟨a, b, ha, hb, hx⟩) hy, --((hy | hy) | ⟨a, b, ha, hb, hy⟩)
  { obtain ((hy | hy) | ⟨a, b, ha, hb, hy⟩) := hy,
    exact subset.trans (hs hx hy) (subset_convex_join_left s t),
  },
  { rintro z hz,
    simp only [mem_convex_join, mem_Union],
    right,
    exact ⟨x, y, hx, hy, hz⟩,
  },
  {

  }-/
end

lemma convex_join_segment_singleton (a b c : E) :
  convex_join 𝕜 (segment 𝕜 a b) {c} = convex_hull 𝕜 {a, b, c} :=
by rw [←pair_eq_singleton, ←convex_join_segments, segment_same, pair_eq_singleton]

lemma convex_join_singleton_segment (a b c : E) :
  convex_join 𝕜 {a} (segment 𝕜 b c) = convex_hull 𝕜 {a, b, c} :=
by rw [←segment_same 𝕜, convex_join_segments, insert_idem]

protected lemma convex.convex_join (hs : convex 𝕜 s) (ht : convex 𝕜 t) :
  convex 𝕜 (convex_join 𝕜 s t) :=
begin
  rw convex_iff_segment_subset at ⊢ ht hs,
  simp_rw mem_convex_join,
  rintro x y ⟨xa, hxa, xb, hxb, hx⟩ ⟨ya, hya, yb, hyb, hy⟩,
  refine (segment_subset_convex_join hx hy).trans _,
  have triv : ({xa, xb, ya, yb} : set E) = {xa, ya, xb, yb} := by simp only [set.insert_comm],
  rw [convex_join_segments, triv, ←convex_join_segments],
  exact convex_join_mono (hs hxa hya) (ht hxb hyb),
end

protected lemma convex.convex_hull_union (hs : convex 𝕜 s) (ht : convex 𝕜 t) (hs₀ : s.nonempty)
  (ht₀ : t.nonempty) :
  convex_hull 𝕜 (s ∪ t) = convex_join 𝕜 s t :=
(convex_hull_min (union_subset (subset_convex_join_left ht₀) $ subset_convex_join_right hs₀) $
  hs.convex_join ht).antisymm $ convex_join_subset_convex_hull _ _

lemma convex_hull_union (hs : s.nonempty) (ht : t.nonempty) :
  convex_hull 𝕜 (s ∪ t) = convex_join 𝕜 (convex_hull 𝕜 s) (convex_hull 𝕜 t) :=
begin
  rw [←convex_hull_convex_hull_union, ←convex_hull_self_union_convex_hull],
  exact (convex_convex_hull 𝕜 s).convex_hull_union (convex_convex_hull 𝕜 t)
    hs.convex_hull ht.convex_hull,
end

lemma convex_hull_insert (hs : s.nonempty) :
  convex_hull 𝕜 (insert x s) = ⋃ a ∈ convex_hull 𝕜 s, segment 𝕜 x a :=
by rw [insert_eq, convex_hull_union (singleton_nonempty _) hs, convex_hull_singleton,
  convex_join_singleton_left]

lemma convex_join_assoc (s t u : set E) :
  convex_join 𝕜 s (convex_join 𝕜 t u) = convex_join 𝕜 (convex_join 𝕜 s t) u :=
sorry

lemma convex_join_left_comm (s t u : set E) :
  convex_join 𝕜 s (convex_join 𝕜 t u) = convex_join 𝕜 t (convex_join 𝕜 s u) :=
by simp_rw [convex_join_assoc, convex_join_comm]

lemma convex_join_right_comm (s t u : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) u = convex_join 𝕜 (convex_join 𝕜 s u) t :=
by simp_rw [←convex_join_assoc, convex_join_comm]

lemma convex_join_convex_join_convex_join_comm (s t u v : set E) :
  convex_join 𝕜 (convex_join 𝕜 s t) (convex_join 𝕜 u v) =
    convex_join 𝕜 (convex_join 𝕜 s u) (convex_join 𝕜 t v) :=
by simp_rw [convex_join_assoc, convex_join_right_comm]

end linear_ordered_field

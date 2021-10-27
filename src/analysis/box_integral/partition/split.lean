/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.basic

/-!
# Split a box along one or more hyperplanes

## Main definitions

A hyperplane `{x : ι → ℝ | x i = a}` splits a rectangular box `I : box_integral.box ι` into two
smaller boxes. If `a ∉ Ioo (I.lower i, I.upper i)`, then one of these boxes is empty, so it is not a
box in the sense of `box_integral.box`.

We introduce the following definitions.

* `box_integral.box.split_lower I i a` and `box_integral.box.split_upper I i a` are these boxes (as
  `with_bot (box_integral.box ι)`);
* `box_integral.prepartition.split I i a` is the partition of `I` made of these two boxes (or of one
   box `I` if one of these boxes is empty);
* `box_integral.prepartition.split_many I s`, where `s : finset (ι × ℝ)` is a finite set of
  hyperplanes `{x : ι → ℝ | x i = a}` encoded as pairs `(i, a)`, is the partition of `I` made by
  cutting it along all the hyperplanes in `s`.

## Main results

The main result `box_integral.prepartition.exists_Union_eq_diff` says that any prepartition `π` of
`I` admits a prepartition `π'` of `I` that covers exactly `I \ π.Union`. One of these prepartitions
is available as `box_integral.prepartition.compl`.

## Tags

rectangular box, partition, hyperplane
-/

noncomputable theory
open_locale classical big_operators filter
open function set filter

namespace box_integral

variables {ι M : Type*} {n : ℕ}

namespace box

variables {I : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_lower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def split_lower (I : box ι) (i : ι) (x : ℝ) : with_bot (box ι) :=
mk' I.lower (update I.upper i (min x (I.upper i)))

@[simp] lemma coe_split_lower : (split_lower I i x : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  rw [split_lower, coe_mk'],
  ext y,
  simp only [mem_univ_pi, mem_Ioc, mem_inter_eq, mem_coe, mem_set_of_eq, forall_and_distrib,
    ← pi.le_def, le_update_iff, le_min_iff, and_assoc, and_forall_ne i, mem_def],
  rw [and_comm (y i ≤ x), pi.le_def]
end

lemma split_lower_le : I.split_lower i x ≤ I := with_bot_coe_subset_iff.1 $ by simp

@[simp] lemma split_lower_eq_bot {i x} : I.split_lower i x = ⊥ ↔ x ≤ I.lower i :=
begin
  rw [split_lower, mk'_eq_bot, exists_update_iff I.upper (λ j y, y ≤ I.lower j)],
  simp [(I.lower_lt_upper _).not_le]
end

@[simp] lemma split_lower_eq_self : I.split_lower i x = I ↔ I.upper i ≤ x :=
by simp [split_lower, update_eq_iff]

lemma split_lower_def [decidable_eq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
  (h' : ∀ j, I.lower j < update I.upper i x j :=
    (forall_update_iff I.upper (λ j y, I.lower j < y)).2 ⟨h.1, λ j hne, I.lower_lt_upper _⟩) :
  I.split_lower i x = (⟨I.lower, update I.upper i x, h'⟩ : box ι) :=
by { simp only [split_lower, mk'_eq_coe, min_eq_left h.2.le], use rfl, congr }

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x` is the box `I ∩ {y | x < y i}`
(if it is nonempty). As usual, we represent a box that may be empty as
`with_bot (box_integral.box ι)`. -/
def split_upper (I : box ι) (i : ι) (x : ℝ) : with_bot (box ι) :=
mk' (update I.lower i (max x (I.lower i))) I.upper

@[simp] lemma coe_split_upper : (split_upper I i x : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  rw [split_upper, coe_mk'],
  ext y,
  simp only [mem_univ_pi, mem_Ioc, mem_inter_eq, mem_coe, mem_set_of_eq, forall_and_distrib,
    forall_update_iff I.lower (λ j z, z < y j), max_lt_iff, and_assoc (x < y i),
    and_forall_ne i, mem_def],
  exact and_comm _ _
end

lemma split_upper_le : I.split_upper i x ≤ I := with_bot_coe_subset_iff.1 $ by simp

@[simp] lemma split_upper_eq_bot {i x} : I.split_upper i x = ⊥ ↔ I.upper i ≤ x :=
begin
  rw [split_upper, mk'_eq_bot, exists_update_iff I.lower (λ j y, I.upper j ≤ y)],
  simp [(I.lower_lt_upper _).not_le]
end

@[simp] lemma split_upper_eq_self : I.split_upper i x = I ↔ x ≤ I.lower i :=
by simp [split_upper, update_eq_iff]

lemma split_upper_def [decidable_eq ι] {i x} (h : x ∈ Ioo (I.lower i) (I.upper i))
  (h' : ∀ j, update I.lower i x j < I.upper j :=
    (forall_update_iff I.lower (λ j y, y < I.upper j)).2 ⟨h.2, λ j hne, I.lower_lt_upper _⟩) :
  I.split_upper i x = (⟨update I.lower i x, I.upper, h'⟩ : box ι) :=
by { simp only [split_upper, mk'_eq_coe, max_eq_left h.1.le], refine ⟨_, rfl⟩, congr }

lemma disjoint_split_lower_split_upper (I : box ι) (i : ι) (x : ℝ) :
  disjoint (I.split_lower i x) (I.split_upper i x) :=
begin
  rw [← disjoint_with_bot_coe, coe_split_lower, coe_split_upper],
  refine (disjoint.inf_left' _ _).inf_right' _,
  exact λ y (hy : y i ≤ x ∧ x < y i), not_lt_of_le hy.1 hy.2
end

lemma split_lower_ne_split_upper (I : box ι) (i : ι) (x : ℝ) :
  I.split_lower i x ≠ I.split_upper i x :=
begin
  cases le_or_lt x (I.lower i),
  { rw [split_upper_eq_self.2 h, split_lower_eq_bot.2 h], exact with_bot.bot_ne_coe _ },
  { refine (disjoint_split_lower_split_upper I i x).ne _,
    rwa [ne.def, split_lower_eq_bot, not_le] }
end
end box

namespace prepartition

variables {I J : box ι} {i : ι} {x : ℝ}

/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : box ι) (i : ι) (x : ℝ) : prepartition I :=
of_with_bot {I.split_lower i x, I.split_upper i x}
  begin
    simp only [finset.mem_insert, finset.mem_singleton],
    rintro J (rfl|rfl),
    exacts [box.split_lower_le, box.split_upper_le]
  end
  begin
    simp only [finset.coe_insert, finset.coe_singleton, true_and, set.mem_singleton_iff,
     pairwise_on_insert_of_symmetric symmetric_disjoint, pairwise_on_singleton],
    rintro J rfl -,
    exact I.disjoint_split_lower_split_upper i x
  end

@[simp] lemma mem_split_iff : J ∈ split I i x ↔ ↑J = I.split_lower i x ∨ ↑J = I.split_upper i x :=
by simp [split]

lemma mem_split_iff' : J ∈ split I i x ↔
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} ∨ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
by simp [mem_split_iff, ← box.with_bot_coe_inj]

@[simp] lemma Union_split (I : box ι) (i : ι) (x : ℝ) : (split I i x).Union = I :=
by simp [split, ← inter_union_distrib_left, ← set_of_or, le_or_lt]

lemma is_partition_split (I : box ι) (i : ι) (x : ℝ) : is_partition (split I i x) :=
is_partition_iff_Union_eq.2 $ Union_split I i x

lemma sum_split_boxes {M : Type*} [add_comm_monoid M] (I : box ι) (i : ι) (x : ℝ) (f : box ι → M) :
  ∑ J in (split I i x).boxes, f J = (I.split_lower i x).elim 0 f + (I.split_upper i x).elim 0 f :=
by rw [split, sum_of_with_bot, finset.sum_pair (I.split_lower_ne_split_upper i x)]

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
lemma split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ :=
begin
  refine ((is_partition_top I).eq_of_boxes_subset (λ J hJ, _)).symm,
  rcases mem_top.1 hJ with rfl, clear hJ,
  rw [mem_boxes, mem_split_iff],
  rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at h,
  cases h; [right, left],
  { rwa [eq_comm, box.split_upper_eq_self] },
  { rwa [eq_comm, box.split_lower_eq_self] }
end

lemma coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : y i ≤ x) :
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
(mem_split_iff'.1 h₁).resolve_right $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_lt h₂.2 }

lemma coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : x < y i) :
  (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
(mem_split_iff'.1 h₁).resolve_left $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_le h₂.2 }

@[simp] lemma restrict_split (h : I ≤ J) (i : ι) (x : ℝ) : (split J i x).restrict I = split I i x :=
begin
  refine ((is_partition_split J i x).restrict h).eq_of_boxes_subset _,
  simp only [finset.subset_iff, mem_boxes, mem_restrict', exists_prop, mem_split_iff'],
  have : ∀ s, (I ∩ s : set (ι → ℝ)) ⊆ J, from λ s, (inter_subset_left _ _).trans h,
  rintro J₁ ⟨J₂, (H₂|H₂), H₁⟩; [left, right]; simp [H₁, H₂, inter_left_comm ↑I, this],
end

lemma inf_split (π : prepartition I) (i : ι) (x : ℝ) :
  π ⊓ split I i x = π.bUnion (λ J, split J i x) :=
bUnion_congr_of_le rfl $ λ J hJ, restrict_split hJ i x

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def split_many (I : box ι) (s : finset (ι × ℝ)) : prepartition I :=
s.inf (λ p, split I p.1 p.2)

@[simp] lemma split_many_empty (I : box ι) : split_many I ∅ = ⊤ := finset.inf_empty

@[simp] lemma split_many_insert (I : box ι) (s : finset (ι × ℝ)) (p : ι × ℝ) :
  split_many I (insert p s) = split_many I s ⊓ split I p.1 p.2 :=
by rw [split_many, finset.inf_insert, inf_comm, split_many]

lemma split_many_le_split (I : box ι) {s : finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
  split_many I s ≤ split I p.1 p.2 :=
finset.inf_le hp

lemma is_partition_split_many (I : box ι) (s : finset (ι × ℝ)) :
  is_partition (split_many I s) :=
finset.induction_on s (by simp only [split_many_empty, is_partition_top]) $
  λ a s ha hs, by simpa only [split_many_insert, inf_split]
    using hs.bUnion (λ J hJ, is_partition_split _ _ _)

@[simp] lemma Union_split_many (I : box ι) (s : finset (ι × ℝ)) : (split_many I s).Union = I :=
(is_partition_split_many I s).Union_eq

lemma inf_split_many {I : box ι} (π : prepartition I) (s : finset (ι × ℝ)) :
  π ⊓ split_many I s = π.bUnion (λ J, split_many J s) :=
begin
  induction s using finset.induction_on with p s hp ihp,
  { simp },
  { simp_rw [split_many_insert, ← inf_assoc, ihp, inf_split, bUnion_assoc] }
end

/-- Let `s : finset (ι × ℝ)` be a set of hyperplanes `{x : ι → ℝ | x i = r}` in `ι → ℝ` encoded as
pairs `(i, r)`. Suppose that this set contains all faces of a box `J`. The hyperplanes of `s` split
a box `I` into subboxes. Let `Js` be one of them. If `J` and `Js` have nonempty intersection, then
`Js` is a subbox of `J`.  -/
lemma not_disjoint_imp_le_of_subset_of_mem_split_many {I J Js : box ι} {s : finset (ι × ℝ)}
  (H : ∀ i, {(i, J.lower i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ split_many I s)
  (Hn : ¬disjoint (J : with_bot (box ι)) Js) : Js ≤ J :=
begin
  simp only [finset.insert_subset, finset.singleton_subset_iff] at H,
  rcases box.not_disjoint_coe_iff_nonempty_inter.mp Hn with ⟨x, hx, hxs⟩,
  refine λ y hy i, ⟨_, _⟩,
  { rcases split_many_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.lower i), Hle⟩,
    have := Hle hxs,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle,
    exact (Hle hy).2 },
  { rcases split_many_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.upper i), Hle⟩,
    have := Hle hxs,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle,
    exact (Hle hy).2 }
end

section fintype

variable [fintype ι]

/-- Let `s` be a finite set of boxes in `ℝⁿ = ι → ℝ`. Then there exists a finite set `t₀` of
hyperplanes (namely, the set of all hyperfaces of boxes in `s`) such that for any `t ⊇ t₀`
and any box `I` in `ℝⁿ` the following holds. The hyperplanes from `t` split `I` into subboxes.
Let `J'` be one of them, and let `J` be one of the boxes in `s`. If these boxes have a nonempty
intersection, then `J' ≤ J`. -/
lemma eventually_not_disjoint_imp_le_of_mem_split_many (s : finset (box ι)) :
  ∀ᶠ t : finset (ι × ℝ) in at_top, ∀ (I : box ι) (J ∈ s) (J' ∈ split_many I t),
    ¬disjoint (J : with_bot (box ι)) J' → J' ≤ J :=
begin
  refine eventually_at_top.2
    ⟨s.bUnion (λ J, finset.univ.bUnion (λ i, {(i, J.lower i), (i, J.upper i)})),
      λ t ht I J hJ J' hJ', not_disjoint_imp_le_of_subset_of_mem_split_many (λ i, _) hJ'⟩,
  exact λ p hp, ht (finset.mem_bUnion.2 ⟨J, hJ, finset.mem_bUnion.2 ⟨i, finset.mem_univ _, hp⟩⟩)
end

lemma eventually_split_many_inf_eq_filter (π : prepartition I) :
  ∀ᶠ t : finset (ι × ℝ) in at_top,
    π ⊓ (split_many I t) = (split_many I t).filter (λ J, ↑J ⊆ π.Union) :=
begin
  refine (eventually_not_disjoint_imp_le_of_mem_split_many π.boxes).mono (λ t ht, _),
  refine le_antisymm ((bUnion_le_iff _).2 $ λ J hJ, _) (le_inf (λ J hJ, _) (filter_le _ _)),
  { refine of_with_bot_mono _,
    simp only [finset.mem_image, exists_prop, mem_boxes, mem_filter],
    rintro _ ⟨J₁, h₁, rfl⟩ hne,
    refine ⟨_, ⟨J₁, ⟨h₁, subset.trans _ (π.subset_Union hJ)⟩, rfl⟩, le_rfl⟩,
    exact ht I J hJ J₁ h₁ (mt disjoint_iff.1 hne) },
  { rw mem_filter at hJ,
    rcases set.mem_bUnion_iff.1 (hJ.2 J.upper_mem) with ⟨J', hJ', hmem⟩,
    refine ⟨J', hJ', ht I _ hJ' _ hJ.1 $ box.not_disjoint_coe_iff_nonempty_inter.2 _⟩,
    exact ⟨J.upper, hmem, J.upper_mem⟩  }
end

lemma exists_split_many_inf_eq_filter_of_finite (s : set (prepartition I)) (hs : s.finite) :
  ∃ t : finset (ι × ℝ), ∀ π ∈ s,
    π ⊓ (split_many I t) = (split_many I t).filter (λ J, ↑J ⊆ π.Union) :=
begin
  have := λ π (hπ : π ∈ s), eventually_split_many_inf_eq_filter π,
  exact (hs.eventually_all.2 this).exists
end

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`split_many I s ≤ π`. -/
lemma is_partition.exists_split_many_le {I : box ι} {π : prepartition I}
  (h : is_partition π) : ∃ s, split_many I s ≤ π :=
(eventually_split_many_inf_eq_filter π).exists.imp $ λ s hs,
  by { rwa [h.Union_eq, filter_of_true, inf_eq_right] at hs, exact λ J hJ, le_of_mem _ hJ }

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.Union`. -/
lemma exists_Union_eq_diff (π : prepartition I) :
  ∃ π' : prepartition I, π'.Union = I \ π.Union :=
begin
  rcases π.eventually_split_many_inf_eq_filter.exists with ⟨s, hs⟩,
  use (split_many I s).filter (λ J, ¬(J : set (ι → ℝ)) ⊆ π.Union),
  simp [← hs]
end

/-- If `π` is a prepartition of `I`, then `π.compl` is a prepartition of `I`
such that `π.compl.Union = I \ π.Union`. -/
def compl (π : prepartition I) : prepartition I := π.exists_Union_eq_diff.some

@[simp] lemma Union_compl (π : prepartition I) : π.compl.Union = I \ π.Union :=
π.exists_Union_eq_diff.some_spec

/-- Since the definition of `box_integral.prepartition.compl` uses `Exists.some`,
the result depends only on `π.Union`. -/
lemma compl_congr {π₁ π₂ : prepartition I} (h : π₁.Union = π₂.Union) :
  π₁.compl = π₂.compl :=
by { dunfold compl, congr' 1, rw h }

lemma is_partition.compl_eq_bot {π : prepartition I} (h : is_partition π) : π.compl = ⊥ :=
by rw [← Union_eq_empty, Union_compl, h.Union_eq, diff_self]

@[simp] lemma compl_top : (⊤ : prepartition I).compl = ⊥ := (is_partition_top I).compl_eq_bot

end fintype

end prepartition

end box_integral

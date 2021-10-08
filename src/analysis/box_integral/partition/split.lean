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
  `part (box_integral.box ι)`);
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
open_locale classical big_operators
open function set

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

lemma split_lower_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_lower i x = ⊥ :=
begin
  rw [← with_bot_coe_inj, coe_split_lower, coe_bot, eq_empty_iff_forall_not_mem],
  rintro y ⟨hy : y ∈ I, hyi : y i ≤ x⟩,
  exact (hyi.trans h).not_lt (hy i).1
end

lemma split_lower_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_lower i x = I :=
begin
  rw [← with_bot_coe_inj, coe_split_lower, coe_coe, inter_eq_left_iff_subset],
  exact λ y hy, (hy i).2.trans h
end

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

lemma split_upper_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_upper i x = I :=
begin
  rw [← with_bot_coe_inj, coe_split_upper, coe_coe, inter_eq_left_iff_subset],
  exact λ y hy, h.trans_lt (hy i).1
end

lemma split_upper_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_upper i x = ⊥ :=
begin
  rw [← with_bot_coe_inj, coe_split_upper, coe_bot, eq_empty_iff_forall_not_mem],
  rintro y ⟨hy : y ∈ I, hyi : x < y i⟩,
  exact (h.trans_lt hyi).not_le (hy i).2
end

lemma disjoint_split_lower_split_upper (I : box ι) (i : ι) (x : ℝ) :
  disjoint (I.split_lower i x) (I.split_upper i x) :=
begin
  rw [← disjoint_with_bot_coe, coe_split_lower, coe_split_upper],
  refine (disjoint.inf_left' _ _).inf_right' _,
  exact λ y (hy : y i ≤ x ∧ x < y i), not_lt_of_le hy.1 hy.2
end

@[simp] lemma face_split_lower_get_same (I : box (fin (n + 1))) (i x hx) :
  face ((split_lower I i x).get hx) i = face I i :=
begin
  simp only [face, split_lower_get_lower, split_lower_get_upper, funext_iff, (∘)],
  exact ⟨λ _, rfl, λ j, update_noteq (fin.succ_above_ne _ _) _ _⟩
end

@[simp] lemma face_split_upper_get_same (I : box (fin (n + 1))) (i x hx) :
  face ((split_upper I i x).get hx) i = face I i :=
begin
  simp only [face, split_upper_get_lower, split_upper_get_upper, funext_iff, (∘)],
  exact ⟨λ j, update_noteq (fin.succ_above_ne _ _) _ _, λ _, rfl⟩
end

@[simp] lemma face_split_lower_succ_above_get (I : box (fin (n + 1))) (i : fin (n + 1))
  (j : fin n) (x : ℝ) (hx : I.lower (i.succ_above j) < x) :
  face ((split_lower I (i.succ_above j) x).get hx) i =
    (split_lower (face I i) j x).get hx :=
begin
  simp only [face, split_lower, eq_self_iff_true, true_and, eq_update_iff, (∘), update_same],
  intros k hk,
  convert update_noteq (i.succ_above.injective.ne hk) _ _
end

@[simp] lemma face_split_upper_succ_above_get (I : box (fin (n + 1))) (i : fin (n + 1))
  (j : fin n) (x : ℝ) (hx : x < I.upper (i.succ_above j)) :
  face ((split_upper I (i.succ_above j) x).get hx) i =
    (split_upper (face I i) j x).get hx :=
begin
  simp only [face, split_upper, eq_self_iff_true, true_and, and_true, eq_update_iff,
    (∘), update_same],
  intros k hk,
  convert update_noteq (i.succ_above.injective.ne hk) _ _
end

end box

namespace prepartition

variables {I J : box ι} {i : ι} {x : ℝ}

/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : box ι) (i : ι) (x : ℝ) : prepartition I :=
{ boxes := (I.split_lower i x).to_finset ∪ (I.split_upper i x).to_finset,
  le_of_mem' :=
    begin
      simp only [finset.mem_union, part.mem_to_finset],
      rintro J (⟨H, rfl⟩|⟨H, rfl⟩),
      exacts [I.split_lower_get_le, I.split_upper_get_le]
    end,
  pairwise_disjoint :=
    begin
      simp only [finset.coe_union, part.coe_to_finset,
        pairwise_on_union_of_symmetric (symmetric_disjoint.comap _),
        set.subsingleton.pairwise_on, part.subsingleton, true_and, mem_set_of_eq],
      exact λ J₁ h₁ J₂ h₂ _, box.disjoint_of_mem_split_lower_of_mem_split_upper h₁ h₂
    end }

@[simp] lemma mem_split_iff : J ∈ split I i x ↔ J ∈ I.split_lower i x ∨ J ∈ I.split_upper i x :=
by simp [split]

lemma mem_split_iff' : J ∈ split I i x ↔
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} ∨ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
by simp [mem_split_iff, box.mem_split_lower, box.mem_split_upper]

lemma is_partition_split (I : box ι) (i : ι) (x : ℝ) : is_partition (split I i x) :=
begin
  intros y hy,
  simp only [exists_prop, mem_split_iff],
  cases le_or_lt (y i) x with hle hlt,
  exacts [⟨_, or.inl $ part.get_mem _, I.mem_split_lower_get hy hle⟩,
    ⟨_, or.inr $ part.get_mem _, I.mem_split_upper_get hy hlt⟩]
end

@[simp] lemma Union_split (I : box ι) (i : ι) (x : ℝ) : (split I i x).Union = I :=
(is_partition_split I i x).Union_eq

/-- If `I.lower i < x < I.upper i`, then the hyperplane `{y | y i = x}` splits `I` into two
boxes. -/
lemma split_boxes_of_mem_Ioo (h : x ∈ Ioo (I.lower i) (I.upper i)) :
  (split I i x).boxes = {(I.split_lower i x).get h.1, (I.split_upper i x).get h.2} :=
begin
  ext J,
  simp only [finset.mem_insert, finset.mem_singleton, mem_boxes, mem_split_iff, part.eq_get_iff_mem]
end

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
lemma split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ :=
begin
  refine ((is_partition_top I).eq_of_boxes_subset (λ J hJ, _)).symm,
  rcases mem_top.1 hJ with rfl, clear hJ,
  rw [mem_boxes, mem_split_iff],
  rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at h,
  cases h; [right, left];
    simp only [box.split_lower_of_upper_le, box.split_upper_of_le_lower, h, part.mem_some]
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
  simp only [restrict_boxes, finset.pimage_subset, mem_split_iff, mem_boxes],
  have : ∀ s, (I ∩ s : set (ι → ℝ)) ⊆ J, from λ s, (inter_subset_left _ _).trans h,
  rintro J' (⟨H₁, rfl⟩|⟨H₂, rfl⟩) J ⟨hJ, rfl⟩; [left, right];
    simp [box.mem_split_lower, box.mem_split_upper, inter_left_comm ↑I, this]
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
lemma nonempty_inter_imp_le_of_subset_of_mem_split_many {I J Js : box ι} {s : finset (ι × ℝ)}
  (H : ∀ i, {(i, J.lower i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ split_many I s)
  (Hn : (J ∩ Js : set (ι → ℝ)).nonempty) : Js ≤ J :=
begin
  simp only [finset.insert_subset, finset.singleton_subset_iff] at H,
  rcases Hn with ⟨x, hx, hxs⟩,
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
lemma exists_split_many_forall_nonempty_imp_le (s : finset (box ι)) :
  ∃ t₀ : finset (ι × ℝ), ∀ (t ⊇ t₀) (I : box ι) (J ∈ s) (J' ∈ split_many I t),
    (J ∩ J' : set (ι → ℝ)).nonempty → J' ≤ J :=
begin
  refine ⟨s.bUnion (λ J, finset.univ.bUnion (λ i, {(i, J.lower i), (i, J.upper i)})),
    λ t ht I J hJ J' hJ', nonempty_inter_imp_le_of_subset_of_mem_split_many (λ i, _) hJ'⟩,
  exact λ p hp, ht (finset.mem_bUnion.2 ⟨J, hJ, finset.mem_bUnion.2 ⟨i, finset.mem_univ _, hp⟩⟩)
end

lemma exists_split_many_inf_eq_filter (π : prepartition I) :
  ∃ s : finset (ι × ℝ), ∀ t ⊇ s,
    π ⊓ (split_many I t) = (split_many I t).filter (λ J, ↑J ⊆ π.Union) :=
begin
  refine (exists_split_many_forall_nonempty_imp_le π.boxes).imp (λ s hs t ht, _),
  refine eq_of_boxes_subset_Union_superset _ _,
  { simp only [finset.subset_iff, mem_inf, mem_boxes, mem_filter],
    rintro J ⟨J₁, h₁, J₂, h₂, h⟩,
    have := hs t ht I J₁ h₁ J₂ h₂ h.fst, rw [box.inter_of_ge this, part.mem_some_iff] at h, subst J,
    exact ⟨h₂, (box.coe_subset_coe.2 this).trans (π.subset_Union h₁)⟩ },
  { simp only [set.subset_def, mem_Union, exists_prop, mem_filter],
    rintro x ⟨J, ⟨hJs, hJ⟩, hx⟩, rcases hJ x hx with ⟨J', hJ', hx'⟩,
    exact ⟨_, mem_inf.2 ⟨J', hJ', J, hJs, _, rfl⟩, box.mem_inter_get hx' hx⟩ }
end

lemma exists_split_many_inf_eq_filter_of_finite (s : set (prepartition I)) (hs : s.finite) :
  ∃ t : finset (ι × ℝ), ∀ π ∈ s,
    π ⊓ (split_many I t) = (split_many I t).filter (λ J, ↑J ⊆ π.Union) :=
begin
  choose t ht using (λ π : prepartition I, exists_split_many_inf_eq_filter π),
  refine ⟨hs.to_finset.sup t, λ π hπ, ht π _ _⟩,
  change t π ≤ _,
  exact finset.le_sup (hs.mem_to_finset.2 hπ)
end

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`split_many I s ≤ π`. -/
lemma is_partition.exists_split_many_le {I : box ι} {π : prepartition I}
  (h : is_partition π) : ∃ s, split_many I s ≤ π :=
(exists_split_many_forall_nonempty_imp_le π.boxes).imp $ λ s hs, h.le_iff.2 $
  λ Js hJs J hJ Hne, hs s (finset.subset.refl _) I J hJ _ hJs (Hne.mono (inter_comm _ _).subset)

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.Union`. -/
lemma exists_Union_eq_diff (π : prepartition I) :
  ∃ π' : prepartition I, π'.Union = I \ π.Union :=
begin
  rcases π.exists_split_many_inf_eq_filter with ⟨s, hs⟩,
  use (split_many I s).filter (λ J, ¬(J : set (ι → ℝ)) ⊆ π.Union),
  simp [← hs s (finset.subset.refl _)],
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

/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.basic
import analysis.normed_space.operator_norm
import data.set.intervals.proj_Icc

/-!
# Box additive functions

We say that a function `f : box ι → M` from boxes in `ℝⁿ` to a commutative additive monoid `M` is
*box additive* on subboxes of `I₀ : with_bot (box ι)` if for any box `J`, `↑J ≤ I₀`, and a partition
`π` of `J`, `f J = ∑ J' in π.boxes, f J'`.

Examples of box-additive functions include the measure of a box and the integral of a fixed
integrable function over a box.

In this file we define box-additive functions and prove that a function such that
`f J = f (J ∩ {x | x i < y}) + f (J ∩ {x | y ≤ x i})` is box-additive. We also prove that for any
prepartition `π` of a box `I`, there exists a prepartition `π'` such that `π'.Union = I \ π.Union`
and define `π.compl` to be one of these prepartitions.

### Tags

rectangular box, additive function
-/

noncomputable theory
open_locale classical big_operators
open function set

namespace box_integral

variables {ι M : Type*} {n : ℕ}

namespace box

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_lower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). -/
@[simps dom get_lower {fully_applied := ff}] def split_lower (I : box ι) (i : ι) (x : ℝ) :
  part (box ι) :=
{ dom := I.lower i < x,
  get := λ hx, ⟨I.lower, update I.upper i (min x (I.upper i)),
    (forall_update_iff _ (λ j z, I.lower j < z)).2
      ⟨lt_min hx $ I.lower_lt_upper i, λ j _, I.lower_lt_upper j⟩⟩ }

@[simp] lemma split_lower_get_upper [decidable_eq ι] (I : box ι) (i : ι) (x : ℝ)
  (hx : I.lower i < x) :
  ((I.split_lower i x).get hx).upper = update I.upper i (min x (I.upper i)) :=
by { simp only [split_lower], congr }

@[simp] lemma mem_split_lower_get_iff (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ (I.split_lower i x).get hx ↔ y ∈ I ∧ y i ≤ x :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_lower, and_assoc],
  refine and_congr_right (λ H, (@le_update_iff _ _ _ _ y I.upper i _).trans _),
  rw [le_min_iff, and_assoc, and_forall_ne i, and_comm]
end

lemma mem_split_lower_get (I : box ι) {i x} {y : ι → ℝ} (h₁ : y ∈ I) (h₂ : y i ≤ x) :
  y ∈ (I.split_lower i x).get ((h₁ i).1.trans_le h₂) :=
I.mem_split_lower_get_iff.2 ⟨h₁, h₂⟩

@[simp] lemma coe_split_lower_get (I : box ι) {i x hx} :
  ((I.split_lower i x).get hx : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
set.ext $ λ y, I.mem_split_lower_get_iff

lemma split_lower_get_le (I : box ι) {i x hx} : (I.split_lower i x).get hx ≤ I :=
coe_subset_coe.1 $ by simp only [coe_split_lower_get, inter_subset_left]

lemma mem_split_lower {I J : box ι} {i x} :
  J ∈ I.split_lower i x ↔ (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_lower_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H] at this,
    exact (this.1 i).1.trans_le this.2 },
  { rw [coe_split_lower_get, H] }
end

@[simp] lemma Union_coe_mem_split_lower (I : box ι) (i : ι) (x : ℝ) :
  (⋃ J ∈ I.split_lower i x, ↑J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  ext y, simp only [mem_Union], fsplit,
  { rintro ⟨J, hJ, hy⟩, rwa mem_split_lower.1 hJ at hy },
  { exact λ hy, ⟨_, ⟨_, rfl⟩, I.mem_split_lower_get hy.1 hy.2⟩ }
end

lemma split_lower_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_lower i x = part.none :=
part.eq_none_iff'.2 h.not_lt

lemma split_lower_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_lower i x = part.some I :=
begin
  rw ← @part.get_eq_iff_eq_some _ (I.split_lower i x) ((I.lower_lt_upper i).trans_le h),
  ext y, simpa using (show y ∈ I → y i ≤ x, from λ hy, (hy i).2.trans h)
end

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x hx` is the box `I ∩ {y | x < y i}`
(if it is nonempty). -/
@[simps dom get_upper {fully_applied := ff}] def split_upper (I : box ι) (i : ι) (x : ℝ) :
  part (box ι) :=
{ dom := x < I.upper i,
  get := λ hx, ⟨update I.lower i (max x (I.lower i)), I.upper,
    (forall_update_iff _ (λ j z, z < I.upper j)).2
      ⟨max_lt hx $ I.lower_lt_upper i, λ j _, I.lower_lt_upper j⟩⟩ }

@[simp] lemma split_upper_get_lower [decidable_eq ι] (I : box ι) (i : ι) (x : ℝ)
  (h : x < I.upper i) :
  ((I.split_upper i x).get h).lower = update I.lower i (max x (I.lower i)) :=
by { simp only [split_upper], congr }

@[simp] lemma mem_split_upper_get_iff (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ (I.split_upper i x).get hx ↔ y ∈ I ∧ x < y i :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_upper,
    forall_update_iff _ (λ j z, z < y j)],
  rw [max_lt_iff, and_assoc (x < y i), and_forall_ne i, and_assoc, and_comm]
end

@[simp] lemma mem_split_upper_get (I : box ι) {i x} {y : ι → ℝ} (h₁ : y ∈ I) (h₂ : x < y i) :
  y ∈ (I.split_upper i x).get (h₂.trans_le (h₁ i).2) :=
I.mem_split_upper_get_iff.2 ⟨h₁, h₂⟩

@[simp] lemma coe_split_upper_get (I : box ι) {i x hx} :
  ((I.split_upper i x).get hx : set (ι → ℝ)) = I ∩ {y | x < y i} :=
set.ext $ λ y, I.mem_split_upper_get_iff

lemma split_upper_get_le (I : box ι) {i x hx} : (I.split_upper i x).get hx ≤ I :=
coe_subset_coe.1 $ by simp only [coe_split_upper_get, inter_subset_left]

lemma mem_split_upper {I J : box ι} {i x} :
  J ∈ I.split_upper i x ↔ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_upper_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H, set.mem_inter_eq, mem_set_of_eq] at this,
    exact lt_of_lt_of_le this.2 (this.1 i).2 },
  { rw [coe_split_upper_get, H] }
end

@[simp] lemma Union_coe_mem_split_upper (I : box ι) (i : ι) (x : ℝ) :
  (⋃ J ∈ I.split_upper i x, ↑J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  ext y, simp only [mem_Union], fsplit,
  { rintro ⟨J, hJ, hy⟩, rwa mem_split_upper.1 hJ at hy },
  { exact λ hy, ⟨_, ⟨_, rfl⟩, I.mem_split_upper_get hy.1 hy.2⟩ }
end

lemma split_upper_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_upper i x = part.some I :=
begin
  rw ← @part.get_eq_iff_eq_some _ (I.split_upper i x) (h.trans_lt (I.lower_lt_upper i)),
  ext y, simpa using (show y ∈ I → x < y i, from λ hy, h.trans_lt (hy i).1)
end

lemma split_upper_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_upper i x = part.none :=
part.eq_none_iff'.2 h.not_lt

lemma disjoint_of_mem_split_lower_of_mem_split_upper {I Jl Ju : box ι} {i : ι} {x : ℝ}
  (Hl : Jl ∈ I.split_lower i x) (Hu : Ju ∈ I.split_upper i x) :
  disjoint (Jl : set (ι → ℝ)) Ju :=
begin
  rw [mem_split_lower.1 Hl, mem_split_upper.1 Hu],
  refine (disjoint.inf_left' _ _).inf_right' _,
  exact λ y hy, @not_lt_of_le _ _ (y i) x hy.1 hy.2
end

lemma ne_of_mem_split_lower_of_mem_split_upper {I Jl Ju : box ι} {i : ι} {x : ℝ}
  (hl : Jl ∈ I.split_lower i x) (hu : Ju ∈ I.split_upper i x) : Jl ≠ Ju :=
ne_of_disjoint_coe (disjoint_of_mem_split_lower_of_mem_split_upper hl hu)

lemma disjoint_split_lower_get_split_upper_get {I : box ι} {i : ι} {x : ℝ} (hl hu) :
  disjoint ((I.split_lower i x).get hl : set (ι → ℝ)) ((I.split_upper i x).get hu) :=
disjoint_of_mem_split_lower_of_mem_split_upper (part.get_mem _) (part.get_mem _)

lemma split_lower_get_ne_split_upper_get {I : box ι} {i : ι} {x : ℝ} (hl hu) :
  (I.split_lower i x).get hl ≠ (I.split_upper i x).get hu :=
ne_of_mem_split_lower_of_mem_split_upper (part.get_mem _) (part.get_mem _)

lemma map_split_lower_add_upper_get_or_else_zero {M : Type*} [add_zero_class M] (I : box ι) (i : ι)
  (x : ℝ) (f : box ι → M) :
  ((I.split_lower i x).map f).get_or_else 0 + ((I.split_upper i x).map f).get_or_else 0 =
    if h : x ∈ Ioo (I.lower i) (I.upper i) then
      f ((I.split_lower i x).get (and.left h)) + f ((I.split_upper i x).get (and.right h))
    else f I :=
begin
  split_ifs with hx,
  { rw [part.get_or_else, part.get_or_else, dif_pos, dif_pos, part.map_get, part.map_get] },
  { rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at hx, cases hx,
    { simp [split_upper_of_le_lower _ hx, split_lower_of_le_lower _ hx] },
    { simp [split_upper_of_upper_le _ hx, split_lower_of_upper_le _ hx] } }
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
(exists_split_many_forall_nonempty_imp_le π.boxes).imp $ λ s hs, h.ge_iff.2 $
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

/-- A function on `box ι` is called box additive if for every box `I` and a hyperplane
`{y | y i = x}` we have `f (I ∩ {y | y i ≤ x}) + f (I ∩ {y | x < y i}) = f I`. We formualte this
property in terms of `box_integral.box.split_lower` and `box_integral.box.split_upper`.

This property implies that for any partition `π` of a box `I` into smaller boxes we have
`f I = ∑ J in π.boxes, f J`. -/
structure box_additive_map (ι M : Type*) [add_comm_monoid M] (I : with_top (box ι)) :=
(to_fun : box ι → M)
(sum_partition_boxes' : ∀ J : box ι, ↑J ≤ I → ∀ π : prepartition J, π.is_partition →
  ∑ J' in π.boxes, to_fun J' = to_fun J)

notation ι ` →ᵇᵃ `:25 M := box_additive_map ι M ⊤
notation ι ` →ᵇᵃ[`:25 I `] ` M := box_additive_map ι M I

namespace box_additive_map

open box prepartition finset

variables {N : Type*} [add_comm_monoid M] [add_comm_monoid N] {I₀ : with_top (box ι)}
  {I J : box ι} {i : ι}

instance : has_coe_to_fun (ι →ᵇᵃ[I₀] M) := ⟨_, to_fun⟩

initialize_simps_projections box_integral.box_additive_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : ι →ᵇᵃ[I₀] M) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f h) : ⇑(mk f h : ι →ᵇᵃ[I₀] M) = f := rfl

lemma coe_injective : injective (λ (f : ι →ᵇᵃ[I₀] M) x, f x) :=
by { rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g), refl }

@[simp] lemma coe_inj {f g : ι →ᵇᵃ[I₀] M} : (f : box ι → M) = g ↔ f = g :=
coe_injective.eq_iff

lemma sum_partition_boxes (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π : prepartition I}
  (h : π.is_partition) :
  ∑ J in π.boxes, f J = f I :=
f.sum_partition_boxes' I hI π h

@[simps { fully_applied := ff }] instance : has_zero (ι →ᵇᵃ[I₀] M) :=
⟨⟨0, λ I hI π hπ, sum_const_zero⟩⟩

instance : inhabited (ι →ᵇᵃ[I₀] M) := ⟨0⟩

instance : has_add (ι →ᵇᵃ[I₀] M) :=
⟨λ f g, ⟨f + g, λ I hI π hπ,
  by simp only [pi.add_apply, sum_add_distrib, sum_partition_boxes _ hI hπ]⟩⟩

instance : add_comm_monoid (ι →ᵇᵃ[I₀] M) :=
function.injective.add_comm_monoid _ coe_injective rfl (λ _ _, rfl)

@[simp] lemma map_split_add (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {x : ℝ} (hl : I.lower i < x)
  (hu : x < I.upper i) :
  f ((I.split_lower i x).get hl) + f ((I.split_upper i x).get hu) = f I :=
begin
  rw [← f.sum_partition_boxes hI (is_partition_split I i x),
    split_boxes_of_mem_Ioo ⟨hl, hu⟩, sum_pair],
  exact box.split_lower_get_ne_split_upper_get hl hu
end

/-- If `f` is box-additive on subboxes of `I₀`, then it is box-additive on subboxes of any
`I ≤ I₀`. -/
@[simps] def restrict (f : ι →ᵇᵃ[I₀] M) (I : with_top (box ι)) (hI : I ≤ I₀) : ι →ᵇᵃ[I] M :=
⟨f, λ J hJ, f.2 J (hJ.trans hI)⟩

/-- If `f : box ι → M` is box additive on partitions of the form `split I i x`, then it is box
additive. -/
def of_map_split_add [fintype ι] (f : box ι → M) (I₀ : with_top (box ι))
  (hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ {i x} hl hu,
    f ((I.split_lower i x).get hl) + f ((I.split_upper i x).get hu) = f I) :
  ι →ᵇᵃ[I₀] M :=
begin
  refine ⟨f, _⟩,
  replace hf : ∀ I : box ι, ↑I ≤ I₀ → ∀ s, ∑ J in (split_many I s).boxes, f J = f I,
  { intros I hI s,
    induction s using finset.induction_on with a s ha ihs, { simp },
    rw [split_many_insert, inf_split, ← ihs, bUnion_boxes, sum_bUnion_boxes],
    refine finset.sum_congr rfl (λ J' hJ', _),
    by_cases h : a.2 ∈ Ioo (J'.lower a.1) (J'.upper a.1),
    { rw [split_boxes_of_mem_Ioo h, sum_pair (box.split_lower_get_ne_split_upper_get _ _)],
      exact hf _ ((with_top.coe_le_coe.2 $ le_of_mem _ hJ').trans hI) _ _ },
    { rw [split_of_not_mem_Ioo h, top_boxes, finset.sum_singleton] } },
  intros I hI π hπ,
  have Hle : ∀ J ∈ π, ↑J ≤ I₀, from λ J hJ, (with_top.coe_le_coe.2 $ π.le_of_mem hJ).trans hI,
  rcases hπ.exists_split_many_le with ⟨s, hs⟩,
  rw [← hf _ hI, ← inf_of_le_right hs, inf_split_many, bUnion_boxes, sum_bUnion_boxes],
  exact finset.sum_congr rfl (λ J hJ, (hf _ (Hle _ hJ) _).symm)
end

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps { fully_applied := ff }] def map (f : ι →ᵇᵃ[I₀] M) (g : M →+ N) :
  ι →ᵇᵃ[I₀] N :=
{ to_fun := g ∘ f,
  sum_partition_boxes' := λ I hI π hπ, by rw [← g.map_sum, f.sum_partition_boxes hI hπ] }

/-- If `f` is a box additive function on subboxes of `I` and `π₁`, `π₂` are two prepartitions of
`I` that cover the same part of `I`, then `∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J`. -/
lemma sum_boxes_congr [fintype ι] (f : ι →ᵇᵃ[I₀] M) (hI : ↑I ≤ I₀) {π₁ π₂ : prepartition I}
  (h : π₁.Union = π₂.Union) :
  ∑ J in π₁.boxes, f J = ∑ J in π₂.boxes, f J :=
begin
  rcases exists_split_many_inf_eq_filter_of_finite {π₁, π₂} ((finite_singleton _).insert _)
    with ⟨s, hs⟩, simp only [inf_split_many] at hs,
  rcases ⟨hs _ (or.inl rfl), hs _ (or.inr rfl)⟩ with ⟨h₁, h₂⟩, clear hs,
  rw h at h₁,
  calc ∑ J in π₁.boxes, f J = ∑ J in π₁.boxes, ∑ J' in (split_many J s).boxes, f J' :
    finset.sum_congr rfl (λ J hJ, (f.sum_partition_boxes _ (is_partition_split_many _ _)).symm)
  ... = ∑ J in (π₁.bUnion (λ J, split_many J s)).boxes, f J   : (sum_bUnion_boxes _ _ _).symm
  ... = ∑ J in (π₂.bUnion (λ J, split_many J s)).boxes, f J   : by rw [h₁, h₂]
  ... = ∑ J in π₂.boxes, ∑ J' in (split_many J s).boxes, f J' : sum_bUnion_boxes _ _ _
  ... = ∑ J in π₂.boxes, f J :
    finset.sum_congr rfl (λ J hJ, (f.sum_partition_boxes _ (is_partition_split_many _ _))),
  exacts [(with_top.coe_le_coe.2 $ π₁.le_of_mem hJ).trans hI,
    (with_top.coe_le_coe.2 $ π₂.le_of_mem hJ).trans hI]
end

section to_smul

variables {E : Type*} [normed_group E] [normed_space ℝ E]

/-- If `f` is a box-additive map, then so is the map sending `I` to the scalar multiplication
by `f I` as a continuous linear map from `E` to itself. -/
def to_smul (f : ι →ᵇᵃ[I₀] ℝ) : ι →ᵇᵃ[I₀] (E →L[ℝ] E) :=
f.map (continuous_linear_map.lsmul ℝ ℝ).to_linear_map.to_add_monoid_hom

@[simp] lemma to_smul_apply (f : ι →ᵇᵃ[I₀] ℝ) (I : box ι) (x : E) : f.to_smul I x = f I • x := rfl

end to_smul

/-- Given a box `I₀` in `ℝⁿ⁺¹`, `f x : box (fin n) → G` is a family of functions and for
`x ∈ [I₀.lower i, I₀.upper i]`, `f x` is box-additive on subboxes of `i`-th face of `I₀`, then
`λ J, f (J.upper i) (J.face i) - f (J.lower i) (J.face i)` is box-additive on subboxes of `I₀`. -/
@[simps] def {u} upper_sub_lower {G : Type u} [add_comm_group G]
  (I₀ : box (fin (n + 1))) (i : fin (n + 1)) (f : ℝ → box (fin n) → G)
  (fb : Icc (I₀.lower i) (I₀.upper i) → fin n →ᵇᵃ[I₀.face i] G)
  (hf : ∀ x (hx : x ∈ Icc (I₀.lower i) (I₀.upper i)) J, f x J = fb ⟨x, hx⟩ J) :
  fin (n + 1) →ᵇᵃ[I₀] G :=
of_map_split_add
  (λ J : box (fin (n + 1)), f (J.upper i) (J.face i) - f (J.lower i) (J.face i)) I₀
  begin
    rintros J hJ j x (hl : J.lower j < x) (hu : x < J.upper j),
    rw with_top.coe_le_coe at hJ,
    simp only [split_lower_get_lower, split_lower_get_upper, split_upper_get_lower,
      split_upper_get_upper, min_eq_left hu.le, max_eq_left hl.le],

    rcases eq_or_ne j i with rfl|hne,
    { simp },
    { rcases fin.exists_succ_above_eq hne with ⟨j, rfl⟩,
      simp only [face_split_lower_succ_above_get, face_split_upper_succ_above_get,
        update_noteq hne.symm, sub_add_comm],
      have : J.face i ≤ I₀.face i, from face_mono hJ i,
      rw le_iff_Icc at hJ,
      simp only [hf (J.upper i) ⟨(hJ J.upper_mem_Icc).1 i, (hJ J.upper_mem_Icc).2 i⟩,
        hf (J.lower i) ⟨(hJ J.lower_mem_Icc).1 i, (hJ J.lower_mem_Icc).2 i⟩,
        (fb _).map_split_add (with_top.coe_le_coe.2 this),
        (fb _).map_split_add (with_top.coe_le_coe.2 this)] }
  end

end box_additive_map

end box_integral

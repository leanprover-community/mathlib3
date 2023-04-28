/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.pi.algebra
import data.set.intervals.basic
import data.set.intervals.unordered_interval
import data.set.lattice

/-!
# Intervals in `pi`-space

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this we prove various simple lemmas about intervals in `Π i, α i`. Closed intervals (`Ici x`,
`Iic x`, `Icc x y`) are equal to products of their projections to `α i`, while (semi-)open intervals
usually include the corresponding products as proper subsets.
-/

variables {ι : Type*} {α : ι → Type*}

namespace set

section pi_preorder

variables [Π i, preorder (α i)] (x y : Π i, α i)

@[simp] lemma pi_univ_Ici : pi univ (λ i, Ici (x i)) = Ici x :=
ext $ λ y, by simp [pi.le_def]

@[simp] lemma pi_univ_Iic : pi univ (λ i, Iic (x i)) = Iic x :=
ext $ λ y, by simp [pi.le_def]

@[simp] lemma pi_univ_Icc : pi univ (λ i, Icc (x i) (y i)) = Icc x y :=
ext $ λ y, by simp [pi.le_def, forall_and_distrib]

lemma piecewise_mem_Icc {s : set ι} [Π j, decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : Π i, α i}
  (h₁ : ∀ i ∈ s, f₁ i ∈ Icc (g₁ i) (g₂ i)) (h₂ : ∀ i ∉ s, f₂ i ∈ Icc (g₁ i) (g₂ i)) :
  s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
⟨le_piecewise (λ i hi, (h₁ i hi).1) (λ i hi, (h₂ i hi).1),
  piecewise_le (λ i hi, (h₁ i hi).2) (λ i hi, (h₂ i hi).2)⟩

lemma piecewise_mem_Icc' {s : set ι} [Π j, decidable (j ∈ s)] {f₁ f₂ g₁ g₂ : Π i, α i}
  (h₁ : f₁ ∈ Icc g₁ g₂) (h₂ : f₂ ∈ Icc g₁ g₂) :
  s.piecewise f₁ f₂ ∈ Icc g₁ g₂ :=
piecewise_mem_Icc (λ i hi, ⟨h₁.1 _, h₁.2 _⟩) (λ i hi, ⟨h₂.1 _, h₂.2 _⟩)

section nonempty

variable [nonempty ι]

lemma pi_univ_Ioi_subset : pi univ (λ i, Ioi (x i)) ⊆ Ioi x :=
λ z hz, ⟨λ i, le_of_lt $ hz i trivial,
  λ h, nonempty.elim ‹nonempty ι› $ λ i, (h i).not_lt (hz i trivial)⟩

lemma pi_univ_Iio_subset : pi univ (λ i, Iio (x i)) ⊆ Iio x :=
@pi_univ_Ioi_subset ι (λ i, (α i)ᵒᵈ) _ x _

lemma pi_univ_Ioo_subset : pi univ (λ i, Ioo (x i) (y i)) ⊆ Ioo x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

lemma pi_univ_Ioc_subset : pi univ (λ i, Ioc (x i) (y i)) ⊆ Ioc x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, λ i, (hx i trivial).2⟩

lemma pi_univ_Ico_subset : pi univ (λ i, Ico (x i) (y i)) ⊆ Ico x y :=
λ x hx, ⟨λ i, (hx i trivial).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

end nonempty

variable [decidable_eq ι]

open function (update)

lemma pi_univ_Ioc_update_left {x y : Π i, α i} {i₀ : ι} {m : α i₀} (hm : x i₀ ≤ m) :
  pi univ (λ i, Ioc (update x i₀ m i) (y i)) = {z | m < z i₀} ∩ pi univ (λ i, Ioc (x i) (y i)) :=
begin
  have : Ioc m (y i₀) = Ioi m ∩ Ioc (x i₀) (y i₀),
    by rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, ← inter_assoc,
      inter_eq_self_of_subset_left (Ioi_subset_Ioi hm)],
  simp_rw [univ_pi_update i₀ _ _ (λ i z, Ioc z (y i)), ← pi_inter_compl ({i₀} : set ι),
    singleton_pi', ← inter_assoc, this],
  refl
end

lemma pi_univ_Ioc_update_right {x y : Π i, α i} {i₀ : ι} {m : α i₀} (hm : m ≤ y i₀) :
  pi univ (λ i, Ioc (x i) (update y i₀ m i)) = {z | z i₀ ≤ m} ∩ pi univ (λ i, Ioc (x i) (y i)) :=
begin
  have : Ioc (x i₀) m = Iic m ∩ Ioc (x i₀) (y i₀),
    by rw [← Ioi_inter_Iic, ← Ioi_inter_Iic, inter_left_comm,
      inter_eq_self_of_subset_left (Iic_subset_Iic.2 hm)],
  simp_rw [univ_pi_update i₀ y m (λ i z, Ioc (x i) z), ← pi_inter_compl ({i₀} : set ι),
    singleton_pi', ← inter_assoc, this],
  refl
end

lemma disjoint_pi_univ_Ioc_update_left_right {x y : Π i, α i} {i₀ : ι} {m : α i₀} :
  disjoint (pi univ (λ i, Ioc (x i) (update y i₀ m i)))
    (pi univ (λ i, Ioc (update x i₀ m i) (y i))) :=
begin
  rw disjoint_left,
  rintro z h₁ h₂,
  refine (h₁ i₀ (mem_univ _)).2.not_lt _,
  simpa only [function.update_same] using (h₂ i₀ (mem_univ _)).1
end

end pi_preorder

section pi_partial_order
variables [decidable_eq ι] [Π i, partial_order (α i)]

lemma pi_image_update_Icc (f : Π i, α i) (i : ι) (a b : α i) :
  f.update i '' Icc a b = Icc (f.update i a) (f.update i b) :=
begin
  ext,
  rw ←set.pi_univ_Icc,
  refine ⟨_, λ h, ⟨x i, _, _⟩⟩,
  { rintro ⟨c, hc, rfl⟩,
    simpa [update_le_update_iff] },
  { simpa only [function.update_same] using h i (mem_univ i) },
  { ext j,
    obtain rfl | hij := eq_or_ne i j,
    { exact function.update_same _ _ _ },
    { simpa only [function.update_noteq hij.symm, le_antisymm_iff] using h j (mem_univ j) } }
end

lemma pi_image_update_Ico (f : Π i, α i) (i : ι) (a b : α i) :
  f.update i '' Ico a b = Ico (f.update i a) (f.update i b) :=
by rw [←Icc_diff_right, ←Icc_diff_right, image_diff (f.update_injective _), image_singleton,
  pi_image_update_Icc]

lemma pi_image_update_Ioc (f : Π i, α i) (i : ι) (a b : α i) :
  f.update i '' Ioc a b = Ioc (f.update i a) (f.update i b) :=
by rw [←Icc_diff_left, ←Icc_diff_left, image_diff (f.update_injective _), image_singleton,
  pi_image_update_Icc]

lemma pi_image_update_Ioo (f : Π i, α i) (i : ι) (a b : α i) :
  f.update i '' Ioo a b = Ioo (f.update i a) (f.update i b) :=
by rw [←Ico_diff_left, ←Ico_diff_left, image_diff (f.update_injective _), image_singleton,
  pi_image_update_Ico]

lemma pi_image_update_Icc_left (f : Π i, α i) (i : ι) (a : α i) :
  f.update i '' Icc a (f i) = Icc (f.update i a) f :=
by simpa using pi_image_update_Icc f i a (f i)

lemma pi_image_update_Ico_left (f : Π i, α i) (i : ι) (a : α i) :
  f.update i '' Ico a (f i) = Ico (f.update i a) f :=
by simpa using pi_image_update_Ico f i a (f i)

lemma pi_image_update_Ioc_left (f : Π i, α i) (i : ι) (a : α i) :
  f.update i '' Ioc a (f i) = Ioc (f.update i a) f :=
by simpa using pi_image_update_Ioc f i a (f i)

lemma pi_image_update_Ioo_left (f : Π i, α i) (i : ι) (a : α i) :
  f.update i '' Ioo a (f i) = Ioo (f.update i a) f :=
by simpa using pi_image_update_Ioo f i a (f i)

lemma pi_image_update_Icc_right (f : Π i, α i) (i : ι) (b : α i) :
  f.update i '' Icc (f i) b = Icc f (f.update i b) :=
by simpa using pi_image_update_Icc f i (f i) b

lemma pi_image_update_Ico_right (f : Π i, α i) (i : ι) (b : α i) :
  f.update i '' Ico (f i) b = Ico f (f.update i b) :=
by simpa using pi_image_update_Ico f i (f i) b

lemma pi_image_update_Ioc_right (f : Π i, α i) (i : ι) (b : α i) :
  f.update i '' Ioc (f i) b = Ioc f (f.update i b) :=
by simpa using pi_image_update_Ioc f i (f i) b

lemma pi_image_update_Ioo_right (f : Π i, α i) (i : ι) (b : α i) :
  f.update i '' Ioo (f i) b = Ioo f (f.update i b) :=
by simpa using pi_image_update_Ioo f i (f i) b

variables [Π i, has_one (α i)]

@[to_additive]
lemma pi_image_mul_single_Icc (i : ι) (a b : α i) :
  pi.mul_single i '' Icc a b = Icc (pi.mul_single i a) (pi.mul_single i b) :=
pi_image_update_Icc _ _ _ _

@[to_additive]
lemma pi_image_mul_single_Ico (i : ι) (a b : α i) :
  pi.mul_single i '' Ico a b = Ico (pi.mul_single i a) (pi.mul_single i b) :=
pi_image_update_Ico _ _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioc (i : ι) (a b : α i) :
  pi.mul_single i '' Ioc a b = Ioc (pi.mul_single i a) (pi.mul_single i b) :=
pi_image_update_Ioc _ _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioo (i : ι) (a b : α i) :
  pi.mul_single i '' Ioo a b = Ioo (pi.mul_single i a) (pi.mul_single i b) :=
pi_image_update_Ioo _ _ _ _

@[to_additive]
lemma pi_image_mul_single_Icc_left (i : ι) (a : α i) :
  pi.mul_single i '' Icc a 1 = Icc (pi.mul_single i a) 1 :=
pi_image_update_Icc_left _ _ _

@[to_additive]
lemma pi_image_mul_single_Ico_left (i : ι) (a : α i) :
  pi.mul_single i '' Ico a 1 = Ico (pi.mul_single i a) 1 :=
pi_image_update_Ico_left _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioc_left (i : ι) (a : α i) :
  pi.mul_single i '' Ioc a 1 = Ioc (pi.mul_single i a) 1 :=
pi_image_update_Ioc_left _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioo_left (i : ι) (a : α i) :
  pi.mul_single i '' Ioo a 1 = Ioo (pi.mul_single i a) 1 :=
pi_image_update_Ioo_left _ _ _

@[to_additive]
lemma pi_image_mul_single_Icc_right (i : ι) (b : α i) :
  pi.mul_single i '' Icc 1 b = Icc 1 (pi.mul_single i b) :=
pi_image_update_Icc_right _ _ _

@[to_additive]
lemma pi_image_mul_single_Ico_right (i : ι) (b : α i) :
  pi.mul_single i '' Ico 1 b = Ico 1 (pi.mul_single i b) :=
pi_image_update_Ico_right _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioc_right (i : ι) (b : α i) :
  pi.mul_single i '' Ioc 1 b = Ioc 1 (pi.mul_single i b) :=
pi_image_update_Ioc_right _ _ _

@[to_additive]
lemma pi_image_mul_single_Ioo_right (i : ι) (b : α i) :
  pi.mul_single i '' Ioo 1 b = Ioo 1 (pi.mul_single i b) :=
pi_image_update_Ioo_right _ _ _

end pi_partial_order

section pi_lattice
variables [Π i, lattice (α i)]

@[simp] lemma pi_univ_uIcc (a b : Π i, α i) : pi univ (λ i, uIcc (a i) (b i)) = uIcc a b :=
pi_univ_Icc _ _

variables [decidable_eq ι]

lemma pi_image_update_uIcc (f : Π i, α i) (i : ι) (a b : α i) :
  f.update i '' uIcc a b = uIcc (f.update i a) (f.update i b) :=
(pi_image_update_Icc _ _ _ _).trans $ by simp_rw [uIcc, f.update_sup, f.update_inf]

lemma pi_image_update_uIcc_left (f : Π i, α i) (i : ι) (a : α i) :
  f.update i '' uIcc a (f i) = uIcc (f.update i a) f :=
by simpa using pi_image_update_uIcc f i a (f i)

lemma pi_image_update_uIcc_right (f : Π i, α i) (i : ι) (b : α i) :
  f.update i '' uIcc (f i) b = uIcc f (f.update i b) :=
by simpa using pi_image_update_uIcc f i (f i) b

variables [Π i, has_one (α i)]

@[to_additive]
lemma pi_image_mul_single_uIcc (i : ι) (a b : α i) :
  pi.mul_single i '' uIcc a b = uIcc (pi.mul_single i a) (pi.mul_single i b) :=
pi_image_update_uIcc _ _ _ _

@[to_additive]
lemma pi_image_mul_single_uIcc_left (i : ι) (a : α i) :
  pi.mul_single i '' uIcc a 1 = uIcc (pi.mul_single i a) 1 :=
pi_image_update_uIcc_left _ _ _

@[to_additive]
lemma pi_image_mul_single_uIcc_right (i : ι) (b : α i) :
  pi.mul_single i '' uIcc 1 b = uIcc 1 (pi.mul_single i b) :=
pi_image_update_uIcc_right _ _ _

end pi_lattice

variables [decidable_eq ι] [Π i, linear_order (α i)]

open function (update)

lemma pi_univ_Ioc_update_union (x y : Π i, α i) (i₀ : ι) (m : α i₀) (hm : m ∈ Icc (x i₀) (y i₀)) :
  pi univ (λ i, Ioc (x i) (update y i₀ m i)) ∪ pi univ (λ i, Ioc (update x i₀ m i) (y i)) =
    pi univ (λ i, Ioc (x i) (y i)) :=
by simp_rw [pi_univ_Ioc_update_left hm.1, pi_univ_Ioc_update_right hm.2,
  ← union_inter_distrib_right, ← set_of_or, le_or_lt, set_of_true, univ_inter]

/-- If `x`, `y`, `x'`, and `y'` are functions `Π i : ι, α i`, then
the set difference between the box `[x, y]` and the product of the open intervals `(x' i, y' i)`
is covered by the union of the following boxes: for each `i : ι`, we take
`[x, update y i (x' i)]` and `[update x i (y' i), y]`.

E.g., if `x' = x` and `y' = y`, then this lemma states that the difference between a closed box
`[x, y]` and the corresponding open box `{z | ∀ i, x i < z i < y i}` is covered by the union
of the faces of `[x, y]`. -/
lemma Icc_diff_pi_univ_Ioo_subset (x y x' y' : Π i, α i) :
  Icc x y \ pi univ (λ i, Ioo (x' i) (y' i)) ⊆
    (⋃ i : ι, Icc x (update y i (x' i))) ∪ ⋃ i : ι, Icc (update x i (y' i)) y :=
begin
  rintros a ⟨⟨hxa, hay⟩, ha'⟩,
  simpa [le_update_iff, update_le_iff, hxa, hay, hxa _, hay _, ← exists_or_distrib,
    not_and_distrib] using ha'
end

/-- If `x`, `y`, `z` are functions `Π i : ι, α i`, then
the set difference between the box `[x, z]` and the product of the intervals `(y i, z i]`
is covered by the union of the boxes `[x, update z i (y i)]`.

E.g., if `x = y`, then this lemma states that the difference between a closed box
`[x, y]` and the product of half-open intervals `{z | ∀ i, x i < z i ≤ y i}` is covered by the union
of the faces of `[x, y]` adjacent to `x`. -/
lemma Icc_diff_pi_univ_Ioc_subset (x y z : Π i, α i) :
  Icc x z \ pi univ (λ i, Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (update z i (y i)) :=
begin
  rintros a ⟨⟨hax, haz⟩, hay⟩,
  simpa [not_and_distrib, hax, le_update_iff, haz _] using hay
end

end set

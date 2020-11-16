/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury Kudryashov
-/
import data.set.intervals.basic
import data.set.lattice

/-!
# Intervals in `pi`-space

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

variable [nonempty ι]

lemma pi_univ_Ioi_subset : pi univ (λ i, Ioi (x i)) ⊆ Ioi x :=
λ z hz, ⟨λ i, le_of_lt $ hz i trivial,
  λ h, nonempty.elim ‹nonempty ι› $ λ i, (h i).not_lt (hz i trivial)⟩

lemma pi_univ_Iio_subset : pi univ (λ i, Iio (x i)) ⊆ Iio x :=
@pi_univ_Ioi_subset ι (λ i, order_dual (α i)) _ x _

lemma pi_univ_Ioo_subset : pi univ (λ i, Ioo (x i) (y i)) ⊆ Ioo x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

lemma pi_univ_Ioc_subset : pi univ (λ i, Ioc (x i) (y i)) ⊆ Ioc x y :=
λ x hx, ⟨pi_univ_Ioi_subset _ $ λ i hi, (hx i hi).1, λ i, (hx i trivial).2⟩

lemma pi_univ_Ico_subset : pi univ (λ i, Ico (x i) (y i)) ⊆ Ico x y :=
λ x hx, ⟨λ i, (hx i trivial).1, pi_univ_Iio_subset _ $ λ i hi, (hx i hi).2⟩

end pi_preorder

lemma Icc_diff_pi_univ_Ioc_subset [decidable_eq ι] [Π i, linear_order (α i)] (x y z : Π i, α i) :
  Icc x z \ pi univ (λ i, Ioc (y i) (z i)) ⊆ ⋃ i : ι, Icc x (function.update z i (y i)) :=
begin
  rintros a ⟨⟨hax, haz⟩, hay⟩,
  simp only [mem_Ioc, mem_univ_pi, not_forall, not_and_distrib, not_lt] at hay,
  rcases hay with ⟨i, hi⟩,
  replace hi : a i ≤ y i := hi.elim id (λ h, (h $ haz i).elim),
  refine mem_Union.2 ⟨i, ⟨hax, λ j, _⟩⟩,
  by_cases hj : j = i,
  { subst j, simpa },
  { simp [hj, haz j] }
end

end set

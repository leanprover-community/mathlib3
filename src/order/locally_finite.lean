/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.lattice
import data.finset.preimage
import data.finset.sort
import data.set.finite
import data.set.intervals.basic
import data.int.basic

/-!
# Locally finite preorders
-/

universe u

open set

@[algebra] class locally_finite_order (α : Type u) [preorder α] :=
(finset_Icc : α → α → finset α)
(coe_finset_Icc : ∀ x y : α, (finset_Icc x y : set α) = Icc x y)

/-
@[algebra] class locally_finite_order (α : Type u) [preorder α] :=
(list_Icc : α → α → list α)
(mem_Icc : ∀ {x y z}, z ∈ list_Icc x y ↔ z ∈ Icc x y)
-/

/-
@[algebra] class is_locally_finite_order (α : Type u) [preorder α] : Prop :=
(Icc_finite : ∀ {x y : α}, (Icc x y).finite)
-/

variables {α : Type*}

noncomputable def locally_finite_order_of_finite_Icc [preorder α]
  (h : ∀ x y : α, (Icc x y).finite) :
  locally_finite_order α :=
{ finset_Icc := λ x y, (h x y).to_finset,
  coe_finset_Icc := λ x y, (h x y).coe_to_finset }

section
variables [preorder α] [locally_finite_order α]

lemma Icc_finite (a b : α) : (Icc a b).finite :=
begin
  rw ←locally_finite_order.coe_finset_Icc,
  exact (locally_finite_order.finset_Icc a b).finite_to_set,
end

lemma Ico_finite (a b : α) : (Ico a b).finite :=
(Icc_finite a b).subset Ico_subset_Icc_self

lemma Ioc_finite (a b : α) : (Ioc a b).finite :=
(Icc_finite a b).subset Ioc_subset_Icc_self

lemma Ioo_finite (a b : α) : (Ioo a b).finite :=
(Icc_finite a b).subset Ioo_subset_Icc_self

end

namespace finset
variables [partial_order α] [locally_finite_order α] [decidable_eq α]

/-- `set.Icc a b` as a finset -/
def Icc (a b : α) : finset α :=
locally_finite_order.finset_Icc a b

/-- `set.Icc a b` as a finset -/
def Ico (a b : α) : finset α :=
(Icc a b).erase b

/-- `set.Icc a b` as a finset -/
def Ioc (a b : α) : finset α :=
(Icc a b).erase a

/-- `set.Icc a b` as a finset -/
def Ioo (a b : α) : finset α :=
(Ioc a b).erase b

@[simp] lemma coe_Icc (a b : α) : (Icc a b : set α) = set.Icc a b :=
locally_finite_order.coe_finset_Icc a b

@[simp] lemma coe_Ico (a b : α) : (Ico a b : set α) = set.Ico a b :=
by rw [Ico, coe_erase, coe_Icc, Icc_diff_right]

@[simp] lemma coe_Ioc (a b : α) : (Ioc a b : set α) = set.Ioc a b :=
by rw [Ioc, coe_erase, coe_Icc, Icc_diff_left]

@[simp] lemma coe_Ioo (a b : α) : (Ioo a b : set α) = set.Ioo a b :=
by rw [Ioo, coe_erase, coe_Ioc, Ioc_diff_right]

@[simp] lemma mem_Icc_iff {a b x : α} : x ∈ Icc a b ↔ x ∈ set.Icc a b :=
by rw [←coe_Icc, mem_coe]

@[simp] lemma mem_Ico_iff {a b x : α} : x ∈ Ico a b ↔ x ∈ set.Ico a b :=
by rw [←coe_Ico, mem_coe]

@[simp] lemma mem_Ioc_iff {a b x : α} : x ∈ Ioc a b ↔ x ∈ set.Ioc a b :=
by rw [←coe_Ioc, mem_coe]

@[simp] lemma mem_Ioo_iff {a b x : α} : x ∈ Ioo a b ↔ x ∈ set.Ioo a b :=
by rw [←coe_Ioo, mem_coe]

end finset

namespace list
variables [partial_order α] [locally_finite_order α] [decidable_eq α]
  [decidable_rel ((≤) : α → α → Prop)]

/-/-- `set.Icc a b` as a finset -/
def Icc (a b : α) : list α :=
(finset.Icc a b).sort (≤)-/



end list

lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin
  have h : (finset.Ioc x ub).nonempty := ⟨ub, by rwa [finset.mem_Ioc_iff, right_mem_Ioc]⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  {
    have := finset.min'_mem _ h,
    simp * at *,
  },
  rintro y hxy,
  obtain hy | hy := le_or_lt y ub,
  apply finset.min'_le,
  simp * at *,
  have := finset.min'_mem _ h,
end

/-! ### Instances -/

variables {β : Type*} [partial_order β] [locally_finite_order β] [decidable_eq β]

noncomputable def order_embedding.locally_finite_order [partial_order α] [decidable_eq α]
  (f : α ↪o β) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (finset.Icc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  coe_finset_Icc := λ a b, begin
    ext,
    simp only [finset.coe_Icc, finset.coe_preimage, iff_self, mem_preimage, mem_Icc,
      order_embedding.le_iff_le],
  end }

@[priority 900]
instance fintype.locally_finite_order [preorder α] [fintype α] : locally_finite_order α :=
{ finset_Icc := λ a b, (finite.of_fintype (Icc a b)).to_finset,
  coe_finset_Icc := λ a b, finite.coe_to_finset _ }

private def range : ℤ → ℕ → list ℤ
| z 0       := []
| z (n + 1) := z :: range (z + 1) n

instance int.locally_finite_order : locally_finite_order ℤ :=
{ Icc_finite := λ a b, begin
  let s := (range a (b - a).to_nat).to_finset,
  apply (finset.finite_to_set s).subset,
  rintro z hz,
  apply set.finite_mem_finset,
  refine set.finite.of_fintype _,
end }

instance nat.locally_finite_order : locally_finite_order ℕ :=
{ Icc_finite := λ x y, begin

end }

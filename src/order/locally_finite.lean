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
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of `Ici`/`Ioi`
(resp. `Iic`/`Iio`).

## Main declarations

In a `locally_finite_order`,
* `list`/`multiset`/`finset` dot `Icc`/`Ico`/`Ioc`/`Ioo`: Closed/open-closed/open interval as a
  list/multiset/finset.
* `list`/`multiset`/`finset` dot `Ici`/`Ioi`: Closed/open-infinite interval as a
  list/multiset/finset if the order is also an `order_top`.
* `list`/`multiset`/`finset` dot `Iic`/`Iio`: Infinite-closed/open interval as a
  list/multiset/finset if the order is also an `order_bot`.

## Instances

We provide a `locally_finite_order` instance for
* ℕ, see `nat.locally_finite_order`
* ℤ, see `int.locally_finite_order`
* any fintype (but it is noncomputable), see `fintype.locally_finite_order`

## TODO

Once we have the `has_enum` typeclass (any non-top element has a least greater element or any
non-bot element has a greatest lesser element), we can provide an `has_enum` typeclass using

lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  {
    have := finset.min'_mem _ h,
    simp * at *,
  },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end

Note that the converse is not true. Consider `{0} ∪ {2^z | z : ℤ}`. Any element is either ⊥ or has
a greatest lesser element, so it `has_enum`, but it's not locally finite as `Icc 0 1` is infinite.

/- more `has_enum` gibberish
def nth [linear_order α] [locally_finite_order α] {ub : α → option α}
  (hub : ∀ a b, ub a = some b → a < b) (a : α) : ℕ → option α
| 0       := some a
| (n + 1) := match nth n with
  | option.none     := none
  | (option.some a) := match ub a with
    | option.none := none
    | (option.some b) := classical.some (exists_min_greater (hub a b begin sorry end))

def nth' [linear_order α] [no_top_order α] [locally_finite_order α] (a : α) : ℕ → α
| 0       := a
| (n + 1) := classical.some (exists_min_greater (classical.some_spec (no_top a)))
-/

From `linear_order α`, `no_top_order α`, `locally_finite_order α`, we can also define an order
isomorphism `α ≃ ℕ` or `α ≃ ℤ` depending on whether we have `order_bot α` or `no_bot_order α`.
-/

open set

class locally_finite_order (α : Type*) [preorder α] :=
(finset_Icc : α → α → finset α)
(coe_finset_Icc : ∀ x y : α, (finset_Icc x y : set α) = Icc x y)

/-
class locally_finite_order (α : Type u) [preorder α] :=
(list_Icc : α → α → list α)
(mem_Icc : ∀ {x y z}, z ∈ list_Icc x y ↔ z ∈ Icc x y)
-/

/-
class is_locally_finite_order (α : Type u) [preorder α] : Prop :=
(Icc_finite : ∀ {x y : α}, (Icc x y).finite)
-/

variables {α : Type*}

noncomputable def locally_finite_order_of_finite_Icc [preorder α]
  (h : ∀ x y : α, (Icc x y).finite) :
  locally_finite_order α :=
{ finset_Icc := λ x y, (h x y).to_finset,
  coe_finset_Icc := λ x y, (h x y).coe_to_finset }

section preorder
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

end preorder

namespace finset
section partial_order
variables [decidable_eq α] [partial_order α] [locally_finite_order α]

/-- `set.Icc a b` as a finset -/
def Icc (a b : α) : finset α :=
locally_finite_order.finset_Icc a b

/-- `set.Ico a b` as a finset -/
def Ico (a b : α) : finset α :=
(Icc a b).erase b

/-- `set.Ioc a b` as a finset -/
def Ioc (a b : α) : finset α :=
(Icc a b).erase a

/-- `set.Ioo a b` as a finset -/
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

@[simp] lemma mem_Icc_iff {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
by rw [←set.mem_Icc, ←coe_Icc, mem_coe]

@[simp] lemma mem_Ico_iff {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
by rw [←set.mem_Ico, ←coe_Ico, mem_coe]

@[simp] lemma mem_Ioc_iff {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
by rw [←set.mem_Ioc, ←coe_Ioc, mem_coe]

@[simp] lemma mem_Ioo_iff {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
by rw [←set.mem_Ioo, ←coe_Ioo, mem_coe]

@[simp] lemma right_mem_Ioc {a b : α} : b ∈ Ioc a b ↔ a < b :=
begin
  simp,
end

end partial_order

section order_top
variables [decidable_eq α] [order_top α] [locally_finite_order α]

/-- `set.Ici a b` as a finset -/
def Ici (a : α) : finset α :=
Icc a ⊤

/-- `set.Ioi a b` as a finset -/
def Ioi (a : α) : finset α :=
Ioc a ⊤

end order_top

section order_bot
variables [decidable_eq α] [order_bot α] [locally_finite_order α]

/-- `set.Iic a b` as a finset -/
def Iic (a : α) : finset α :=
Icc ⊥ a

/-- `set.Iio a b` as a finset -/
def Iio (a : α) : finset α :=
Ico ⊥ a

end order_bot

end finset

/-
namespace list
variables [decidable_eq α] [partial_order α] [locally_finite_order α]
  [decidable_rel ((≤) : α → α → Prop)]

/-- `set.Icc a b` as a list -/
def Icc (a b : α) : list α :=
(finset.Icc a b).sort (≤)

end list
-/

/-! ### Instances -/

/-
def locally_finite_order.order_iso_ℕ [order_bot α] [no_top_order α] [locally_finite_order α] :
  order_iso α ℕ :=
begin

end-/

private def range₂ [semiring α] [decidable_eq α] : α → ℕ → finset α
| a 0       := ∅
| a (n + 1) := insert a (range₂ (a + 1) n)

private lemma mem_range₂_ℤ (x : ℤ) : ∀ a n, x ∈ range₂ a n ↔ a ≤ x ∧ x < a + n
| a 0     := by simp only [range₂, finset.not_mem_empty, add_zero, imp_self, false_iff,
  int.coe_nat_zero, not_and, not_lt]
| a (n + 1) := begin
  have h : x = a ∨ x < a + (↑n + 1) ↔ x < a + (↑n + 1),
  { rw or_iff_right_iff_imp,
    rintro rfl,
    exact int.lt_add_succ _ _ },
  rw [range₂, finset.mem_insert, le_iff_eq_or_lt, mem_range₂_ℤ _ n, int.coe_nat_succ, add_assoc,
    add_comm (1 : ℤ), @eq_comm _ a, or_and_distrib_left, h],
  refl,
end

private lemma mem_range₂_ℕ (x : ℕ) : ∀ a n, x ∈ range₂ a n ↔ a ≤ x ∧ x < a + n
| a 0     := by simp only [range₂, finset.not_mem_empty, add_zero, imp_self, false_iff,
      int.coe_nat_zero, not_and, not_lt]
| a (n + 1) := begin
    have h : x = a ∨ x < a + (n + 1) ↔ x < a + (n + 1),
    { rw or_iff_right_iff_imp,
      rintro rfl,
      exact (lt_add_iff_pos_right _).2 nat.succ_pos' },
    rw [range₂, finset.mem_insert, le_iff_eq_or_lt, mem_range₂_ℕ _ n, add_assoc,
      add_comm 1, @eq_comm _ a, or_and_distrib_left, h],
    refl,
  end

instance int.locally_finite_order : locally_finite_order ℤ :=
{ finset_Icc := λ a b, range₂ a (b + 1 - a).to_nat,
  coe_finset_Icc := λ a b, begin
    ext,
    rw [finset.mem_coe, mem_range₂_ℤ, set.mem_Icc],
    cases le_or_lt a b,
    { rw [int.to_nat_of_nonneg (sub_nonneg.2 (h.trans (lt_add_one _).le)), ←add_sub_assoc,
        add_sub_cancel', int.lt_add_one_iff] },
    rw [int.to_nat_of_nonpos (sub_nonpos.2 h), int.coe_nat_zero, add_zero],
    exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)),
  end }

instance nat.locally_finite_order : locally_finite_order ℕ :=
{ finset_Icc := λ a b, range₂ a (b + 1 - a),
  coe_finset_Icc := λ a b, begin
    ext,
    rw [finset.mem_coe, mem_range₂_ℕ, set.mem_Icc],
    cases le_or_lt a b,
    { rw [nat.add_sub_cancel' (nat.lt_succ_of_le h).le, nat.lt_succ_iff] },
    rw [nat.sub_eq_zero_iff_le.2 h, add_zero],
    exact iff_of_false (λ hx, hx.2.not_le hx.1) (λ hx, h.not_le (hx.1.trans hx.2)),
end }

@[priority 900]
noncomputable instance fintype.locally_finite_order [preorder α] [fintype α] :
  locally_finite_order α :=
{ finset_Icc := λ a b, (finite.of_fintype (Icc a b)).to_finset,
  coe_finset_Icc := λ a b, finite.coe_to_finset _ }

noncomputable def order_embedding.locally_finite_order {β : Type*} [partial_order β]
  [locally_finite_order β] [decidable_eq β] [partial_order α] [decidable_eq α] (f : α ↪o β) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (finset.Icc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  coe_finset_Icc := λ a b, begin
    ext,
    simp only [finset.coe_Icc, finset.coe_preimage, iff_self, mem_preimage, mem_Icc,
      order_embedding.le_iff_le],
  end }

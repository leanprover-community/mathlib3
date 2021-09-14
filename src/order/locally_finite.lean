/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.finset.preimage
import data.set.finite
import data.set.intervals.basic

/-!
# Locally finite orders

This file defines locally finite orders.

A locally finite order is an order for which all bounded intervals are finite. This allows to make
sense of `Icc`/`Ico`/`Ioc`/`Ioo` as lists, multisets, or finsets.
Further, if the order is bounded above (resp. below), then we can also make sense of the
"unbounded" intervals `Ici`/`Ioi` (resp. `Iic`/`Iio`).

## Main declarations

In a `locally_finite_order`,
* `finset.Icc`: Closed-closed interval as a finset.
* `finset.Ico`: Closed-open interval as a finset.
* `finset.Ioc`: Open-closed interval as a finset.
* `finset.Ioo`: Open-open interval as a finset.
* `multiset.Icc`: Closed-closed interval as a multiset.
* `multiset.Ico`: Closed-open interval as a multiset.
* `multiset.Ioc`: Open-closed interval as a multiset.
* `multiset.Ioo`: Open-open interval as a finset.

When it's also an `order_top`,
* `finset.Ici`: Closed-infinite interval as a finset.
* `finset.Ioi`: Open-infinite interval as a finset.
* `multiset.Ici`: Closed-infinite interval as a multiset.
* `multiset.Ioi`: Open-infinite interval as a multiset.

When it's also an `order_bot`,
* `finset.Iic`: Infinite-open interval as a finset.
* `finset.Iio`: Infinite-closed interval as a finset.
* `multiset.Iic`: Infinite-open interval as a multiset.
* `multiset.Iio`: Infinite-closed interval as a multiset.

## Instances

We provide a `locally_finite_order` instance for
* a subtype of a locally finite order
* any fintype (but it is noncomputable), see `fintype.locally_finite_order`

Instances for concrete types are proved in their respective files:
* `data.nat.intervals` for `ℕ`
* `data.int.intervals` for `ℤ`
* `data.pnat.intervals` for `ℕ+`
Along, you will find lemmas about the cardinality of those finite intervals.

## TODO

Provide the `locally_finite_order` instance for `lex α β`.z

From `linear_order α`, `no_top_order α`, `locally_finite_order α`, we can also define an
order isomorphism `α ≃ ℕ` or `α ≃ ℤ`, depending on whether we have `order_bot α` or
`no_bot_order α` and `nonempty α`. When `order_bot α`, we can match `a : α` to `(Iio a).card`.

Once we have the `succ_order` typeclass (any non-top element has a least greater element), we
can provide `succ_order α` from `linear_order α` and `locally_finite_order α` using

```lean
lemma exists_min_greater [linear_order α] [locally_finite_order α] {x ub : α} (hx : x < ub) :
  ∃ lub, x < lub ∧ ∀ y, x < y → lub ≤ y :=
begin -- very non golfed
  have h : (finset.Ioc x ub).nonempty := ⟨ub, finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩⟩,
  use finset.min' (finset.Ioc x ub) h,
  split,
  { have := finset.min'_mem _ h,
    simp * at * },
  rintro y hxy,
  obtain hy | hy := le_total y ub,
  apply finset.min'_le,
  simp * at *,
  exact (finset.min'_le _ _ (finset.mem_Ioc_iff.2 ⟨hx, le_rfl⟩)).trans hy,
end
```
Note that the converse is not true. Consider `{-2^z | z : ℤ} ∪ {2^z | z : ℤ}`. Any element has a
successor (and actually a predecessor as well), so it is a `succ_order`, but it's not locally finite
as `Icc (-1) 1` is infinite.
-/

lemma and_and_and_comm (a b c d : Prop) : (a ∧ b) ∧ c ∧ d ↔ (a ∧ c) ∧ b ∧ d :=
by rw [←and_assoc, @and.right_comm a, and_assoc]

@[simp] protected lemma list.nodup.erase_dup {α : Type*} [decidable_eq α] {l : list α}
  (h : l.nodup) :
  l.erase_dup = l :=
list.erase_dup_eq_self.2 h

open finset

class locally_finite_order (α : Type*) [preorder α] [decidable_rel ((≤) : α → α → Prop)] :=
(finset_Icc : α → α → finset α)
(finset_Ico : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬b ≤ x))
(finset_Ioc : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a))
(finset_Ioo : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a ∧ ¬b ≤ x))
(finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b)
(finset_mem_Ico : ∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b)
(finset_mem_Ioc : ∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b)
(finset_mem_Ioo : ∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b)

variables {α β : Type*}

/-! ### Intervals as finsets -/

namespace finset
section preorder
variables [preorder α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The finset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a finset.
-/
def Icc (a b : α) : finset α :=
locally_finite_order.finset_Icc a b

/-- The finset of elements `x` such that `a ≤ x` and `x < b`. Basically `set.Ico a b` as a finset.
-/
def Ico (a b : α) : finset α :=
locally_finite_order.finset_Ico a b

/-- The finset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a finset.
-/
def Ioc (a b : α) : finset α :=
locally_finite_order.finset_Ioc a b

/-- The finset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a finset.
-/
def Ioo (a b : α) : finset α :=
locally_finite_order.finset_Ioo a b

@[simp] lemma mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
locally_finite_order.finset_mem_Icc a b x

@[simp] lemma mem_Ico {a b x : α} : x ∈ Ico a b ↔ a ≤ x ∧ x < b :=
locally_finite_order.finset_mem_Ico a b x

@[simp] lemma mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
locally_finite_order.finset_mem_Ioc a b x

@[simp] lemma mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
locally_finite_order.finset_mem_Ioo a b x

@[simp, norm_cast] lemma coe_Icc (a b : α) : (Icc a b : set α) = set.Icc a b :=
by { ext, rw [mem_coe, mem_Icc, set.mem_Icc] }

@[simp, norm_cast] lemma coe_Ico (a b : α) : (Ico a b : set α) = set.Ico a b :=
by { ext, rw [mem_coe, mem_Ico, set.mem_Ico] }

@[simp, norm_cast] lemma coe_Ioc (a b : α) : (Ioc a b : set α) = set.Ioc a b :=
by { ext, rw [mem_coe, mem_Ioc, set.mem_Ioc] }

@[simp, norm_cast] lemma coe_Ioo (a b : α) : (Ioo a b : set α) = set.Ioo a b :=
by { ext, rw [mem_coe, mem_Ioo, set.mem_Ioo] }

theorem Ico_subset_Ico {a₁ b₁ a₂ b₂ : α} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
  Ico a₁ b₁ ⊆ Ico a₂ b₂ :=
begin
  rintro x hx,
  rw mem_Ico at ⊢ hx,
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩,
end

end preorder

section partial_order
variables [partial_order α] [decidable_rel ((≤) : α → α → Prop)]
  [locally_finite_order α]

end partial_order

section order_top
variables [order_top α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The finset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a finset. -/
def Ici (a : α) : finset α :=
Icc a ⊤

/-- The finset of elements `x` such that `a < x`. Basically `set.Ioi a` as a finset. -/
def Ioi (a : α) : finset α :=
Ioc a ⊤

@[simp, norm_cast] lemma coe_Ici (a : α) : (Ici a : set α) = set.Ici a :=
by rw [Ici, coe_Icc, set.Icc_top]

@[simp, norm_cast] lemma coe_Ioi (a : α) : (Ioi a : set α) = set.Ioi a :=
by rw [Ioi, coe_Ioc, set.Ioc_top]

@[simp] lemma mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x :=
by rw [←set.mem_Ici, ←coe_Ici, mem_coe]

@[simp] lemma mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x :=
by rw [←set.mem_Ioi, ←coe_Ioi, mem_coe]

end order_top

section order_bot
variables [order_bot α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The finset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a finset. -/
def Iic (b : α) : finset α :=
Icc ⊥ b

/-- The finset of elements `x` such that `x < b`. Basically `set.Iio b` as a finset. -/
def Iio (b : α) : finset α :=
Ico ⊥ b

@[simp, norm_cast] lemma coe_Iic (b : α) : (Iic b : set α) = set.Iic b :=
by rw [Iic, coe_Icc, set.Icc_bot]

@[simp, norm_cast] lemma coe_Iio (b : α) : (Iio b : set α) = set.Iio b :=
by rw [Iio, coe_Ico, set.Ico_bot]

@[simp] lemma mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b :=
by rw [←set.mem_Iic, ←coe_Iic, mem_coe]

@[simp] lemma mem_Iio {b x : α} : x ∈ Iio b ↔ x < b :=
by rw [←set.mem_Iio, ←coe_Iio, mem_coe]

end order_bot
end finset

/-! ### Intervals as multisets -/

namespace multiset
section preorder
variables [preorder α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The multiset of elements `x` such that `a ≤ x` and `x ≤ b`. Basically `set.Icc a b` as a
multiset. -/
def Icc (a b : α) : multiset α :=
(finset.Icc a b).val

-- TODO@Yaël: Nuke `data.multiset.intervals` and redefine `multiset.Ico` here

/-- The multiset of elements `x` such that `a < x` and `x ≤ b`. Basically `set.Ioc a b` as a
multiset. -/
def Ioc (a b : α) : multiset α :=
(finset.Ioc a b).val

/-- The multiset of elements `x` such that `a < x` and `x < b`. Basically `set.Ioo a b` as a
multiset. -/
def Ioo (a b : α) : multiset α :=
(finset.Ioo a b).val

@[simp] lemma mem_Icc {a b x : α} : x ∈ Icc a b ↔ a ≤ x ∧ x ≤ b :=
by rw [Icc, ←finset.mem_def, finset.mem_Icc]

@[simp] lemma mem_Ioc {a b x : α} : x ∈ Ioc a b ↔ a < x ∧ x ≤ b :=
by rw [Ioc, ←finset.mem_def, finset.mem_Ioc]

@[simp] lemma mem_Ioo {a b x : α} : x ∈ Ioo a b ↔ a < x ∧ x < b :=
by rw [Ioo, ←finset.mem_def, finset.mem_Ioo]

end preorder

section order_top
variables [order_top α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The multiset of elements `x` such that `a ≤ x`. Basically `set.Ici a` as a multiset. -/
def Ici (a : α) : multiset α :=
(finset.Ici a).val

/-- The multiset of elements `x` such that `a < x`. Basically `set.Ioi a` as a multiset. -/
def Ioi (a : α) : multiset α :=
(finset.Ioi a).val

@[simp] lemma mem_Ici {a x : α} : x ∈ Ici a ↔ a ≤ x :=
by rw [Ici, ←finset.mem_def, finset.mem_Ici]

@[simp] lemma mem_Ioi {a x : α} : x ∈ Ioi a ↔ a < x :=
by rw [Ioi, ←finset.mem_def, finset.mem_Ioi]

end order_top

section order_bot
variables [order_bot α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]

/-- The multiset of elements `x` such that `x ≤ b`. Basically `set.Iic b` as a multiset. -/
def Iic (b : α) : multiset α :=
(finset.Iic b).val

/-- The multiset of elements `x` such that `x < b`. Basically `set.Iio b` as a multiset. -/
def Iio (b : α) : multiset α :=
(finset.Iio b).val

@[simp] lemma mem_Iic {b x : α} : x ∈ Iic b ↔ x ≤ b :=
by rw [Iic, ←finset.mem_def, finset.mem_Iic]

@[simp] lemma mem_Iio {b x : α} : x ∈ Iio b ↔ x < b :=
by rw [Iio, ←finset.mem_def, finset.mem_Iio]

end order_bot
end multiset

/-! ### Finiteness of `set` intervals -/

namespace set
section preorder
variables [preorder α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α] (a b : α)

instance fintype_Icc : fintype (Icc a b) :=
fintype.of_finset (finset.Icc a b) (λ x, by rw [finset.mem_Icc, mem_Icc])

instance fintype_Ico : fintype (Ico a b) :=
fintype.of_finset (finset.Ico a b) (λ x, by rw [finset.mem_Ico, mem_Ico])

instance fintype_Ioc : fintype (Ioc a b) :=
fintype.of_finset (finset.Ioc a b) (λ x, by rw [finset.mem_Ioc, mem_Ioc])

instance fintype_Ioo : fintype (Ioo a b) :=
fintype.of_finset (finset.Ioo a b) (λ x, by rw [finset.mem_Ioo, mem_Ioo])

lemma finite_Icc : (Icc a b).finite :=
⟨set.fintype_Icc a b⟩

lemma finite_Ico : (Ico a b).finite :=
⟨set.fintype_Ico a b⟩

lemma finite_Ioc : (Ioc a b).finite :=
⟨set.fintype_Ioc a b⟩

lemma finite_Ioo : (Ioo a b).finite :=
⟨set.fintype_Ioo a b⟩

end preorder

section order_top
variables [order_top α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α] (a : α)

instance fintype_Ici : fintype (Ici a) :=
fintype.of_finset (finset.Ici a) (λ x, by rw [finset.mem_Ici, mem_Ici])

instance fintype_Ioi : fintype (Ioi a) :=
fintype.of_finset (finset.Ioi a) (λ x, by rw [finset.mem_Ioi, mem_Ioi])

lemma finite_Ici : (Ici a).finite :=
⟨set.fintype_Ici a⟩

lemma finite_Ioi : (Ioi a).finite :=
⟨set.fintype_Ioi a⟩

end order_top

section order_bot
variables [order_bot α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α] (b : α)

instance fintype_Iic : fintype (Iic b) :=
fintype.of_finset (finset.Iic b) (λ x, by rw [finset.mem_Iic, mem_Iic])

instance fintype_Iio : fintype (Iio b) :=
fintype.of_finset (finset.Iio b) (λ x, by rw [finset.mem_Iio, mem_Iio])

lemma finite_Iic : (Iic b).finite :=
⟨set.fintype_Iic b⟩

lemma finite_Iio : (Iio b).finite :=
⟨set.fintype_Iio b⟩

end order_bot

end set

/-! ### Instances -/

open finset

section preorder
variables [preorder α] [decidable_rel ((≤) : α → α → Prop)]

noncomputable def locally_finite_order_of_finite_Icc
  (h : ∀ a b : α, (set.Icc a b).finite) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (h a b).to_finset,
  finset_Ico := λ a b, ((h a b).subset set.Ico_subset_Icc_self).to_finset,
  finset_Ioc := λ a b, ((h a b).subset set.Ioc_subset_Icc_self).to_finset,
  finset_Ioo := λ a b, ((h a b).subset set.Ioo_subset_Icc_self).to_finset,
  finset_mem_Icc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Icc],
  finset_mem_Ico := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ico],
  finset_mem_Ioc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioc],
  finset_mem_Ioo := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioo] }

noncomputable def fintype.to_locally_finite_order [fintype α] :
  locally_finite_order α :=
{ finset_Icc := λ a b, (set.finite.of_fintype (set.Icc a b)).to_finset,
  finset_Ico := λ a b, (set.finite.of_fintype (set.Ico a b)).to_finset,
  finset_Ioc := λ a b, (set.finite.of_fintype (set.Ioc a b)).to_finset,
  finset_Ioo := λ a b, (set.finite.of_fintype (set.Ioo a b)).to_finset,
  finset_mem_Icc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Icc],
  finset_mem_Ico := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ico],
  finset_mem_Ioc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioc],
  finset_mem_Ioo := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Ioo] }

instance [locally_finite_order α] (p : α → Prop) [decidable_pred p] :
  locally_finite_order (subtype p) :=
{ finset_Icc := λ a b, (Icc a.val b.val).subtype p,
  finset_Ico := λ a b, (Ico a.val b.val).subtype p,
  finset_Ioc := λ a b, (Ioc a.val b.val).subtype p,
  finset_Ioo := λ a b, (Ioo a.val b.val).subtype p,
  finset_mem_Icc := λ a b x, by simp_rw [finset.mem_subtype, mem_Icc, subtype.val_eq_coe,
    subtype.coe_le_coe],
  finset_mem_Ico := λ a b x, by simp_rw [finset.mem_subtype, mem_Ico, subtype.val_eq_coe,
    subtype.coe_le_coe, subtype.coe_lt_coe],
  finset_mem_Ioc := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioc, subtype.val_eq_coe,
    subtype.coe_le_coe, subtype.coe_lt_coe],
  finset_mem_Ioo := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioo, subtype.val_eq_coe,
    subtype.coe_lt_coe] }

variables [preorder β] [decidable_rel ((≤) : β → β → Prop)] [locally_finite_order β]

-- Should this be called `locally_finite_order.lift`?
/-- Given an order embedding `α ↪o β`, pulls back the `locally_finite_order` on `β` to `α`. -/
noncomputable def order_embedding.locally_finite_order (f : α ↪o β) :
  locally_finite_order α :=
{ finset_Icc := λ a b, (Icc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ico := λ a b, (Ico (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ioc := λ a b, (Ioc (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_Ioo := λ a b, (Ioo (f a) (f b)).preimage f (f.to_embedding.injective.inj_on _),
  finset_mem_Icc := λ a b x, by rw [mem_preimage, mem_Icc, f.le_iff_le, f.le_iff_le],
  finset_mem_Ico := λ a b x, by rw [mem_preimage, mem_Ico, f.le_iff_le, f.lt_iff_lt],
  finset_mem_Ioc := λ a b x, by rw [mem_preimage, mem_Ioc, f.lt_iff_lt, f.le_iff_le],
  finset_mem_Ioo := λ a b x, by rw [mem_preimage, mem_Ioo, f.lt_iff_lt, f.lt_iff_lt] }

end preorder

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
* `multiset.Ico`: Closed-open interval as a multiset. Currently only for `ℕ`.
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

Provide the `locally_finite_order` instance for `lex α β`.

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

/-!
### Arguments autofilling tactics

`locally_finite_order` has fields for all of `Icc`, `Ico`, `Ioc`, `Ioo` to let control over
definitional equality. But all fields can be recovered from `Icc` (or any other actually, but we had
to make a choice here). Hence we provide default values for `locally_finite_order.finset_Ico`,
`locally_finite_order.finset_Ioc`, `locally_finite_order.finset_Ioo` and three corresponding tactics
to fill in the three corresponding proofs.

This is analogous to the default definition of `(<)` in terms of `(≤)`. There, the default proof of
`lt_iff_le_not_le` is provided by `order_laws_tac`, which just tries to call `refl`. Here, the
situation is more complicated, as we need to call an hypothesis (namely
`locally_finite_order.mem_finset_Icc`) that doesn't appear a priori in the type of the proof. Whence
our use of `id_annotate` to force it to appear there.
-/

section tactic
open tactic

variables {α : Type*} [preorder α] [decidable_rel ((≤) : α → α → Prop)]
  {finset_Icc : α → α → finset α} (finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b)

/-- Auxiliary lemma to provide `locally_finite_order.mem_finset_Ico` when
`locally_finite_order.finset_Ico` is the default value. -/
lemma locally_finite_order.mem_Ico_of_mem_Icc :
  id_annotate finset_mem_Icc
    (∀ a b x : α, x ∈ (finset_Icc a b).filter (λ x, ¬b ≤ x) ↔ a ≤ x ∧ x < b) :=
λ a b x, by rw [finset.mem_filter, finset_mem_Icc, and_assoc, lt_iff_le_not_le]

/-- Auxiliary lemma to provide `locally_finite_order.mem_finset_Ioc` when
`locally_finite_order.finset_Ioc` is the default value. -/
lemma locally_finite_order.mem_Ioc_of_mem_Icc :
  id_annotate finset_mem_Icc
    (∀ a b x : α, x ∈ (finset_Icc a b).filter (λ x, ¬x ≤ a) ↔ a < x ∧ x ≤ b) :=
λ a b x, by rw [finset.mem_filter, finset_mem_Icc, and.right_comm, lt_iff_le_not_le]

/-- Auxiliary lemma to provide `locally_finite_order.mem_finset_Ioo` when
`locally_finite_order.finset_Ico` is the default value. -/
lemma locally_finite_order.mem_Ioo_of_mem_Icc :
  id_annotate finset_mem_Icc
    (∀ a b x : α, x ∈ (finset_Icc a b).filter (λ x, ¬x ≤ a ∧ ¬b ≤ x) ↔ a < x ∧ x < b) :=
λ a b x, by rw [finset.mem_filter, finset_mem_Icc, and_and_and_comm, lt_iff_le_not_le,
  lt_iff_le_not_le]

/-- Here to make `locally_finite_order.finset_Ico` an optional field. Tries to prove
`locally_finite_order.mem_finset_Ico` -/
meta def finset_Ico_laws_tac : tactic unit :=
`[exact locally_finite_order.mem_Ico_of_mem_Icc _]

/-- Here to make `locally_finite_order.finset_Ioc` an optional field. Tries to prove
`locally_finite_order.mem_finset_Ioc` -/
meta def finset_Ioc_laws_tac : tactic unit :=
`[exact locally_finite_order.mem_Ioc_of_mem_Icc _]

/-- Here to make `locally_finite_order.finset_Ioo` an optional field. Tries to prove
`locally_finite_order.mem_finset_Ioo` -/
meta def finset_Ioo_laws_tac : tactic unit :=
`[exact locally_finite_order.mem_Ioo_of_mem_Icc _]

end tactic

open finset

class locally_finite_order (α : Type*) [preorder α] [decidable_rel ((≤) : α → α → Prop)] :=
(finset_Icc : α → α → finset α)
(finset_Ico : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬b ≤ x))
(finset_Ioc : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a))
(finset_Ioo : α → α → finset α := λ a b, (finset_Icc a b).filter (λ x, ¬x ≤ a ∧ ¬b ≤ x))
(finset_mem_Icc : ∀ a b x : α, x ∈ finset_Icc a b ↔ a ≤ x ∧ x ≤ b)
(finset_mem_Ico : id_annotate finset_mem_Icc (∀ a b x : α, x ∈ finset_Ico a b ↔ a ≤ x ∧ x < b)
  . finset_Ico_laws_tac)
(finset_mem_Ioc : id_annotate finset_mem_Icc (∀ a b x : α, x ∈ finset_Ioc a b ↔ a < x ∧ x ≤ b)
  . finset_Ioc_laws_tac)
(finset_mem_Ioo : id_annotate finset_mem_Icc (∀ a b x : α, x ∈ finset_Ioo a b ↔ a < x ∧ x < b)
  . finset_Ioo_laws_tac)

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

lemma Ici_eq_Icc (a : α) : Ici a = Icc a ⊤ := rfl
lemma Ioi_eq_Ioc (a : α) : Ioi a = Ioc a ⊤ := rfl

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

lemma Iic_eq_Icc : Iic = Icc (⊥ : α) := rfl
lemma Iio_eq_Ico : Iio = Ico (⊥ : α) := rfl

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
  finset_mem_Icc := λ a b x, by rw [set.finite.mem_to_finset, set.mem_Icc] }

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

variables [locally_finite_order α]

instance : locally_finite_order (α × β) :=
{ finset_Icc := λ a b, (Icc a.fst b.fst).product (Icc a.snd b.snd),
  finset_mem_Icc := λ a b x, by { rw [mem_product, mem_Icc, mem_Icc, and_and_and_comm], refl } }

end preorder

/-! #### Subtype of a locally finite -/

variables [preorder α] [decidable_rel ((≤) : α → α → Prop)] [locally_finite_order α]
  (p : α → Prop) [decidable_pred p]

instance :
  locally_finite_order (subtype p) :=
{ finset_Icc := λ a b, (Icc (a : α) b).subtype p,
  finset_Ico := λ a b, (Ico (a : α) b).subtype p,
  finset_Ioc := λ a b, (Ioc (a : α) b).subtype p,
  finset_Ioo := λ a b, (Ioo (a : α) b).subtype p,
  finset_mem_Icc := λ a b x, by simp_rw [finset.mem_subtype, mem_Icc, subtype.coe_le_coe],
  finset_mem_Ico := λ a b x, by simp_rw [finset.mem_subtype, mem_Ico, subtype.coe_le_coe,
    subtype.coe_lt_coe],
  finset_mem_Ioc := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioc, subtype.coe_le_coe,
    subtype.coe_lt_coe],
  finset_mem_Ioo := λ a b x, by simp_rw [finset.mem_subtype, mem_Ioo, subtype.coe_lt_coe] }

variables [decidable_eq α] (a b : subtype p)

namespace finset

lemma subtype_Icc_eq : Icc a b = (Icc (a : α) b).subtype p := rfl
lemma subtype_Ico_eq : Ico a b = (Ico (a : α) b).subtype p := rfl
lemma subtype_Ioc_eq : Ioc a b = (Ioc (a : α) b).subtype p := rfl
lemma subtype_Ioo_eq : Ioo a b = (Ioo (a : α) b).subtype p := rfl

variables (hp : ∀ ⦃a b x⦄, a ≤ x → x ≤ b → p a → p b → p x)
include hp

lemma map_subtype_embedding_Icc : (Icc a b).map (function.embedding.subtype p) = Icc (a : α) b :=
begin
  rw subtype_Icc_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Icc at hx,
  exact hp hx.1 hx.2 a.prop b.prop,
end

lemma map_subtype_embedding_Ico : (Ico a b).map (function.embedding.subtype p) = Ico (a : α) b :=
begin
  rw subtype_Ico_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ico at hx,
  exact hp hx.1 hx.2.le a.prop b.prop,
end

lemma map_subtype_embedding_Ioc : (Ioc a b).map (function.embedding.subtype p) = Ioc (a : α) b :=
begin
  rw subtype_Ioc_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ioc at hx,
  exact hp hx.1.le hx.2 a.prop b.prop,
end

lemma map_subtype_embedding_Ioo : (Ioo a b).map (function.embedding.subtype p) = Ioo (a : α) b :=
begin
  rw subtype_Ioo_eq,
  refine finset.subtype_map_of_mem (λ x hx, _),
  rw mem_Ioo at hx,
  exact hp hx.1.le hx.2.le a.prop b.prop,
end


end finset

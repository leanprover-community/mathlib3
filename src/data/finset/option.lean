/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Mario Carneiro, Sean Leather
-/
import data.finset.basic
import order.preorder_hom

/-!
# Finite sets in `option α`

In this file we define

* `option.to_finset`: construct an empty or singleton `finset α` from an `option α`;
* `finset.insert_none`: given `s : finset α`, lift it to a finset on `option α` using `option.some`
  and then insert `option.none`;
* `finset.erase_none`: given `s : finset (option α)`, returns `t : finset α` such that
  `x ∈ t ↔ some x ∈ s`.

Then we prove some basic lemmas about these definitions.

## Tags

finset, option
-/

variables {α β : Type*}

open function

namespace option

/-- Construct an empty or singleton finset from an `option` -/
def to_finset (o : option α) : finset α := o.elim ∅ singleton

@[simp] theorem to_finset_none : none.to_finset = (∅ : finset α) := rfl

@[simp] theorem to_finset_some {a : α} : (some a).to_finset = {a} := rfl

@[simp] theorem mem_to_finset {a : α} {o : option α} : a ∈ o.to_finset ↔ a ∈ o :=
by cases o; simp [eq_comm]

theorem card_to_finset (o : option α) : o.to_finset.card = o.elim 0 1 :=
by cases o; refl

end option

namespace finset

/-- Given a finset on `α`, lift it to being a finset on `option α`
using `option.some` and then insert `option.none`. -/
def insert_none : finset α ↪o finset (option α) :=
order_embedding.of_map_le_iff (λ s, cons none (s.map embedding.some) $ by simp) $ λ s t,
  cons_subset_cons.trans map_subset_map

/-⟨none ::ₘ s.1.map some, multiset.nodup_cons.2
  ⟨by simp, multiset.nodup_map (λ a b, option.some.inj) s.2⟩⟩-/

@[simp] theorem mem_insert_none {s : finset α} : ∀ {o : option α},
  o ∈ s.insert_none ↔ ∀ a ∈ o, a ∈ s
| none     := iff_of_true (multiset.mem_cons_self _ _) (λ a h, by cases h)
| (some a) := multiset.mem_cons.trans $ by simp; refl

theorem some_mem_insert_none {s : finset α} {a : α} :
  some a ∈ s.insert_none ↔ a ∈ s := by simp

@[simp] theorem card_insert_none (s : finset α) : s.insert_none.card = s.card + 1 :=
by simp [insert_none]

/-- Given `s : finset (option α)`, `s.erase_none : finset α` is the set of `x : α` such that
`some x ∈ s`. -/
def erase_none : finset (option α) →ₘ finset α :=
(finset.map_embedding (equiv.option_is_some_equiv α).to_embedding).to_preorder_hom.comp
  ⟨finset.subtype _, subtype_mono⟩

@[simp] lemma mem_erase_none {s : finset (option α)} {x : α} :
  x ∈ s.erase_none ↔ some x ∈ s :=
by simp [erase_none]

lemma erase_none_eq_bUnion [decidable_eq α] (s : finset (option α)) :
  s.erase_none = s.bUnion option.to_finset :=
by { ext, simp }

@[simp] lemma erase_none_map_some (s : finset α) : (s.map embedding.some).erase_none = s :=
by { ext, simp }

@[simp] lemma erase_none_image_some [decidable_eq (option α)] (s : finset α) :
  (s.image some).erase_none = s :=
by simpa only [map_eq_image] using erase_none_map_some s

@[simp] lemma coe_erase_none (s : finset (option α)) :
  (s.erase_none : set α) = some ⁻¹' s :=
set.ext $ λ x, mem_erase_none

@[simp] lemma erase_none_union [decidable_eq (option α)] [decidable_eq α]
  (s t : finset (option α)) :
  (s ∪ t).erase_none = s.erase_none ∪ t.erase_none :=
by { ext, simp }

@[simp] lemma erase_none_inter [decidable_eq (option α)] [decidable_eq α]
  (s t : finset (option α)) :
  (s ∩ t).erase_none = s.erase_none ∩ t.erase_none :=
by { ext, simp }

@[simp] lemma erase_none_empty : (∅ : finset (option α)).erase_none = ∅ := by { ext, simp }

@[simp] lemma erase_none_none : ({none} : finset (option α)).erase_none = ∅ := by { ext, simp }

@[simp] lemma image_some_erase_none [decidable_eq (option α)] (s : finset (option α)) :
  s.erase_none.image some = s.erase none :=
by ext (_|x); simp

@[simp] lemma map_some_erase_none [decidable_eq (option α)] (s : finset (option α)) :
  s.erase_none.map embedding.some = s.erase none :=
by rw [map_eq_image, embedding.some_apply, image_some_erase_none]

@[simp] lemma insert_none_erase_none [decidable_eq (option α)] (s : finset (option α)) :
  insert_none (erase_none s) = insert none s :=
by ext (_|x); simp

@[simp] lemma erase_none_insert_none (s : finset α) : erase_none (insert_none s) = s :=
by { ext, simp }

end finset

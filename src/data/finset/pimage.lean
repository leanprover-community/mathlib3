/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.finset.basic
import data.pfun

/-!
# Image of a `finset α` under a partially defined function

In this file we defile `part.to_finset` and `
-/

variables {α β : Type*}

namespace part

/-- Convert a `o : part α` with decidable `part.dom o` to `finset α`. -/
def to_finset (o : part α) [decidable o.dom] : finset α := o.to_option.to_finset

@[simp] lemma mem_to_finset {o : part α} [decidable o.dom] {x : α} :
  x ∈ o.to_finset ↔ x ∈ o :=
by simp [to_finset]

@[simp] theorem to_finset_none : none.to_finset = (∅ : finset α) := rfl

@[simp] theorem to_finset_some {a : α} : (some a).to_finset = {a} := rfl

end part

namespace finset

variables [decidable_eq β] {f : α →. β} [∀ x, decidable (f x).dom] {s t : finset α} {b : β}

/-- Image of `s : finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, decidable (f x).dom] (s : finset α) : finset β :=
s.bUnion (λ x, (f x).to_finset)

@[simp] lemma mem_pimage : b ∈ s.pimage f ↔ ∃ (a ∈ s), b ∈ f a := by simp [pimage]

@[simp, norm_cast] lemma coe_pimage : (s.pimage f : set β) = f.image s :=
set.ext $ λ x, mem_pimage

/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
lemma pimage_eq_image_filter : s.pimage f =
  (filter (λ x, (f x).dom) s).attach.image (λ x, (f x).get (mem_filter.1 x.coe_prop).2) :=
by { ext x, simp [part.mem_eq, and.exists, -exists_prop] }

lemma pimage_union [decidable_eq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
coe_inj.1 $ by simp only [coe_pimage, pfun.image_union, coe_union]

@[simp] lemma pimage_empty : pimage f ∅ = ∅ := by { ext, simp }

end finset

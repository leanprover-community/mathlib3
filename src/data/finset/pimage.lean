/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import data.finset.basic
import data.pfun

/-!
# Image of a `finset α` under a partially defined function

In this file we define `part.to_finset` and `finset.pimage`. We also prove some trivial lemmas about
these definitions.

## Tags

finite set, image, partial function
-/

variables {α β : Type*}

namespace part

/-- Convert a `o : part α` with decidable `part.dom o` to `finset α`. -/
def to_finset (o : part α) [decidable o.dom] : finset α := o.to_option.to_finset

@[simp] lemma mem_to_finset {o : part α} [decidable o.dom] {x : α} :
  x ∈ o.to_finset ↔ x ∈ o :=
by simp [to_finset]

@[simp] theorem to_finset_none [decidable (none : part α).dom] :
  none.to_finset = (∅ : finset α) :=
by simp [to_finset]

@[simp] theorem to_finset_some {a : α} [decidable (some a).dom] :
  (some a).to_finset = {a} :=
by simp [to_finset]

@[simp] lemma coe_to_finset (o : part α) [decidable o.dom] :
  (o.to_finset : set α) = {x | x ∈ o} :=
set.ext $ λ x, mem_to_finset

end part

namespace finset

variables [decidable_eq β] {f g : α →. β} [∀ x, decidable (f x).dom]
  [∀ x, decidable (g x).dom] {s t : finset α} {b : β}

/-- Image of `s : finset α` under a partially defined function `f : α →. β`. -/
def pimage (f : α →. β) [∀ x, decidable (f x).dom] (s : finset α) : finset β :=
s.bUnion (λ x, (f x).to_finset)

@[simp] lemma mem_pimage : b ∈ s.pimage f ↔ ∃ (a ∈ s), b ∈ f a := by simp [pimage]

@[simp, norm_cast] lemma coe_pimage : (s.pimage f : set β) = f.image s :=
set.ext $ λ x, mem_pimage

@[simp] lemma pimage_some (s : finset α) (f : α → β) [∀ x, decidable (part.some $ f x).dom] :
  s.pimage (λ x, part.some (f x)) = s.image f :=
by { ext, simp [eq_comm] }

lemma pimage_congr (h₁ : s = t) (h₂ : ∀ x ∈ t, f x = g x) : s.pimage f = t.pimage g :=
by { subst s, ext y, simp [h₂] { contextual := tt } }

/-- Rewrite `s.pimage f` in terms of `finset.filter`, `finset.attach`, and `finset.image`. -/
lemma pimage_eq_image_filter : s.pimage f =
  (filter (λ x, (f x).dom) s).attach.image (λ x, (f x).get (mem_filter.1 x.coe_prop).2) :=
by { ext x, simp [part.mem_eq, and.exists, -exists_prop] }

lemma pimage_union [decidable_eq α] : (s ∪ t).pimage f = s.pimage f ∪ t.pimage f :=
coe_inj.1 $ by simp only [coe_pimage, pfun.image_union, coe_union]

@[simp] lemma pimage_empty : pimage f ∅ = ∅ := by { ext, simp }

lemma pimage_subset {t : finset β} : s.pimage f ⊆ t ↔ ∀ (x ∈ s) (y ∈ f x), y ∈ t :=
by simp [subset_iff, @forall_swap _ β]

@[mono] lemma pimage_mono (h : s ⊆ t) : s.pimage f ⊆ t.pimage f :=
pimage_subset.2 $ λ x hx y hy, mem_pimage.2 ⟨x, h hx, hy⟩

lemma pimage_inter [decidable_eq α] : (s ∩ t).pimage f ⊆ s.pimage f ∩ t.pimage f :=
by simp only [← coe_subset, coe_pimage, coe_inter, pfun.image_inter]

end finset

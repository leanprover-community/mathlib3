/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import algebra.star.basic
import algebra.pointwise
/-!
# Pointwise star operation on sets

This file defines the star operation pointwise on sets and provides the basic API.
Besides basic facts about about how the star operation acts on sets (e.g., `(s ∩ t)⋆ = s⋆ ∩ t⋆`),
if `s t : set α`, then under suitable assumption on `α`, it is shown

* `(s + t)⋆ = s⋆ + t⋆`
* `(s * t)⋆ = t⋆ + s⋆`
* `(s⁻¹)⋆ = (s⋆)⁻¹`
-/

namespace set

open_locale pointwise

local postfix `⋆`:std.prec.max_plus := star

variables {α : Type*} {s t : set α} {a : α}

/-- The set `(star s : set α)` is defined as `{x | star x ∈ s}` in locale `pointwise`.
In the usual case where `star` is involutive, it is equal to `{star s | x ∈ s}`, see
`set.image_star`. -/
protected def has_star [has_star α] : has_star (set α) :=
⟨preimage has_star.star⟩

localized "attribute [instance] set.has_star" in pointwise

@[simp]
lemma star_empty [has_star α] : (∅ : set α)⋆ = ∅ := rfl

@[simp]
lemma star_univ [has_star α] : (univ : set α)⋆ = univ := rfl

@[simp]
lemma nonempty_star [has_involutive_star α] {s : set α} : (s⋆).nonempty ↔ s.nonempty :=
star_involutive.surjective.nonempty_preimage

lemma nonempty.star [has_involutive_star α] {s : set α} (h : s.nonempty) :
  (s⋆).nonempty :=
nonempty_star.2 h

@[simp]
lemma mem_star [has_star α] : a ∈ s⋆ ↔ a⋆ ∈ s := iff.rfl

lemma star_mem_star [has_involutive_star α] : a⋆ ∈ s⋆ ↔ a ∈ s :=
by simp only [mem_star, star_star]

@[simp]
lemma star_preimage [has_star α] : has_star.star ⁻¹' s = s⋆ := rfl

@[simp]
lemma image_star [has_involutive_star α] : has_star.star '' s = s⋆ :=
by { simp only [← star_preimage], rw [image_eq_preimage_of_inverse]; intro; simp only [star_star] }

@[simp]
lemma inter_star [has_star α] : (s ∩ t)⋆ = s⋆ ∩ t⋆ := preimage_inter

@[simp]
lemma union_star [has_star α] : (s ∪ t)⋆ = s⋆ ∪ t⋆ := preimage_union

@[simp]
lemma Inter_star {ι : Sort*} [has_star α] (s : ι → set α) : (⋂ i, s i)⋆ = ⋂ i, (s i)⋆ :=
preimage_Inter

@[simp]
lemma Union_star {ι : Sort*} [has_star α] (s : ι → set α) : (⋃ i, s i)⋆ = ⋃ i, (s i)⋆ :=
preimage_Union

@[simp]
lemma compl_star [has_star α] : (sᶜ)⋆ = (s⋆)ᶜ := preimage_compl

@[simp]
instance [has_involutive_star α] : has_involutive_star (set α) :=
{ star := has_star.star,
  star_involutive :=
    λ s, by { simp only [← star_preimage, preimage_preimage, star_star, preimage_id'] } }

@[simp]
lemma star_subset_star [has_involutive_star α] {s t : set α} : s⋆ ⊆ t⋆ ↔ s ⊆ t :=
equiv.star.surjective.preimage_subset_preimage_iff

lemma star_subset [has_involutive_star α] {s t : set α} : s⋆ ⊆ t ↔ s ⊆ t⋆ :=
by { rw [← star_subset_star, star_star] }

lemma finite.star [has_involutive_star α] {s : set α} (hs : finite s) : finite s⋆ :=
hs.preimage $ star_injective.inj_on _

lemma star_singleton {β : Type*} [has_involutive_star β] (x : β) : ({x} : set β)⋆ = {x⋆} :=
by { ext1 y, rw [mem_star, mem_singleton_iff, mem_singleton_iff, star_eq_iff_star_eq, eq_comm], }

protected lemma star_mul [monoid α] [star_monoid α] (s t : set α) :
  (s * t)⋆ = t⋆ * s⋆ :=
by simp_rw [←image_star, ←image2_mul, image_image2, image2_image_left, image2_image_right,
              star_mul, image2_swap _ s t]

protected lemma star_add [add_monoid α] [star_add_monoid α] (s t : set α) :
  (s + t)⋆ = s⋆ + t⋆ :=
by simp_rw [←image_star, ←image2_add, image_image2, image2_image_left, image2_image_right, star_add]

@[simp]
instance [has_star α] [has_trivial_star α] : has_trivial_star (set α) :=
{ star_trivial := λ s, by { rw [←star_preimage], ext1, simp [star_trivial] } }

protected lemma star_inv [group α] [star_monoid α] (s : set α) : (s⁻¹)⋆ = (s⋆)⁻¹ :=
by { ext, simp only [mem_star, mem_inv, star_inv] }

protected lemma star_inv' [division_ring α] [star_ring α] (s : set α) : (s⁻¹)⋆ = (s⋆)⁻¹ :=
by { ext, simp only [mem_star, mem_inv, star_inv'] }

end set

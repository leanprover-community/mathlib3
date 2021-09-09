/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import order.galois_connection

/-!
# Relations

This file defines bundled relations. A relation between `α` and `β` is a function `α → β → Prop`.
Relations are also known as set-valued functions, or partial multifunctions.

## Main declarations

* `rel α β`: Relation between `α` and `β`.
* `rel.inv`: `r.inv` is the `rel β α` obtained by swapping the arguments of `r`.
* `rel.dom`: Domain of a relation. `x ∈ r.dom` iff there exists `y` such that `r x y`.
* `rel.codom`: Codomain, aka range, of a relation. `y ∈ r.codom` iff there exists `x` such that
  `r x y`.
* `rel.comp`: Relation composition. Note that the arguments order follows the `category_theory/`
  one, so `r.comp s x z ↔ ∃ y, r x y ∧ s y z`.
* `rel.image`: Image of a set under a relation. `r.image s` is the set of `f x` over all `x ∈ s`.
* `rel.preimage`: Preimage of a set under a relation. Note that `r.preimage = r.inv.image`.
* `rel.core`: Core of a set. For `s : set β`, `r.core s` is the set of `x : α` such that all `y`
  related to `x` are in `s`.
* `rel.restrict_domain`: Domain-restriction of a relation to a subtype.
* `function.graph`: Graph of a function as a relation.
-/

variables {α β γ : Type*}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
@[derive complete_lattice, derive inhabited]
def rel (α β : Type*) := α → β → Prop

namespace rel

variables {δ : Type*} (r : rel α β)

/-- The inverse relation : `r.inv x y ↔ r y x`. Note that this is *not* a groupoid inverse. -/
def inv : rel β α := flip r

lemma inv_def (x : α) (y : β) : r.inv y x ↔ r x y := iff.rfl

lemma inv_inv : inv (inv r) = r := by { ext x y, reflexivity }

/-- Domain of a relation -/
def dom := {x | ∃ y, r x y}

/-- Codomain aka range of a relation -/
def codom := {y | ∃ x, r x y}

lemma codom_inv : r.inv.codom = r.dom := by { ext x y, reflexivity }

lemma dom_inv : r.inv.dom = r.codom := by { ext x y, reflexivity}

/-- Composition of relation; note that it follows the `category_theory/` order of arguments. -/
def comp (r : rel α β) (s : rel β γ) : rel α γ :=
λ x z, ∃ y, r x y ∧ s y z

local infixr ` ∘ ` := rel.comp

lemma comp_assoc (r : rel α β) (s : rel β γ) (t : rel γ δ) :
  (r ∘ s) ∘ t = r ∘ s ∘ t :=
begin
  unfold comp, ext x w, split,
  { rintros ⟨z, ⟨y, rxy, syz⟩, tzw⟩, exact ⟨y, rxy, z, syz, tzw⟩ },
  rintros ⟨y, rxy, z, syz, tzw⟩, exact ⟨z, ⟨y, rxy, syz⟩, tzw⟩
end

@[simp]
lemma comp_right_id (r : rel α β) : r ∘ @eq β = r :=
by { unfold comp, ext y, simp }

@[simp]
lemma comp_left_id (r : rel α β) : @eq α ∘ r = r :=
by { unfold comp, ext x, simp }

lemma inv_id : inv (@eq α) = @eq α :=
by { ext x y, split; apply eq.symm }

lemma inv_comp (r : rel α β) (s : rel β γ) : inv (r ∘ s) = inv s ∘ inv r :=
by { ext x z, simp [comp, inv, flip, and.comm] }

/-- Image of a set under a relation -/
def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

lemma mem_image (y : β) (s : set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
iff.rfl

lemma image_subset : ((⊆) ⇒ (⊆)) r.image r.image :=
λ s t h y ⟨x, xs, rxy⟩, ⟨x, h xs, rxy⟩

lemma image_mono : monotone r.image := r.image_subset

lemma image_inter (s t : set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
r.image_mono.map_inf_le s t

lemma image_union (s t : set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
le_antisymm
  (λ y ⟨x, xst, rxy⟩, xst.elim (λ xs, or.inl ⟨x, ⟨xs, rxy⟩⟩) (λ xt, or.inr ⟨x, ⟨xt, rxy⟩⟩))
  (r.image_mono.le_map_sup s t)

@[simp]
lemma image_id (s : set α) : image (@eq α) s = s :=
by { ext x, simp [mem_image] }

lemma image_comp (s : rel β γ) (t : set α) : image (r ∘ s) t = image s (image r t) :=
begin
  ext z, simp only [mem_image, comp], split,
  { rintros ⟨x, xt, y, rxy, syz⟩, exact ⟨y, ⟨x, xt, rxy⟩, syz⟩ },
  rintros ⟨y, ⟨x, xt, rxy⟩, syz⟩, exact ⟨x, xt, y, rxy, syz⟩
end

lemma image_univ : r.image set.univ = r.codom := by { ext y, simp [mem_image, codom] }

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : set β) : set α := r.inv.image s

lemma mem_preimage (x : α) (s : set β) : x ∈ r.preimage s ↔ ∃ y ∈ s, r x y :=
iff.rfl

lemma preimage_def (s : set β) : preimage r s = {x | ∃ y ∈ s, r x y} :=
set.ext $ λ x, mem_preimage _ _ _

lemma preimage_mono {s t : set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
image_mono _ h

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
image_inter _ s t

lemma preimage_union (s t : set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
image_union _ s t

lemma preimage_id (s : set α) : preimage (@eq α) s = s :=
by simp only [preimage, inv_id, image_id]

lemma preimage_comp (s : rel β γ) (t : set γ) :
  preimage (r ∘ s) t = preimage r (preimage s t) :=
by simp only [preimage, inv_comp, image_comp]

lemma preimage_univ : r.preimage set.univ = r.dom :=
by { rw [preimage, image_univ, codom_inv] }

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only*
to elements of `s`. Other generalization of `function.preimage`. -/
def core (s : set β) := {x | ∀ y, r x y → y ∈ s}

lemma mem_core (x : α) (s : set β) : x ∈ r.core s ↔ ∀ y, r x y → y ∈ s :=
iff.rfl

lemma core_subset : ((⊆) ⇒ (⊆)) r.core r.core :=
λ s t h x h' y rxy, h (h' y rxy)

lemma core_mono : monotone r.core := r.core_subset

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
set.ext (by simp [mem_core, imp_and_distrib, forall_and_distrib])

lemma core_union (s t : set β) : r.core s ∪ r.core t ⊆ r.core (s ∪ t) :=
r.core_mono.le_map_sup s t

@[simp] lemma core_univ : r.core set.univ = set.univ := set.ext (by simp [mem_core])

lemma core_id (s : set α) : core (@eq α) s = s :=
by simp [core]

lemma core_comp (s : rel β γ) (t : set γ) :
  core (r ∘ s) t = core r (core s t) :=
begin
  ext x, simp [core, comp], split,
  { exact λ h y rxy z, h z y rxy },
  { exact λ h z y rzy, h y rzy z }
end

/-- Restrict the domain of a relation to a subtype. -/
def restrict_domain (s : set α) : rel {x // x ∈ s} β :=
λ x y, r x.val y

theorem image_subset_iff (s : set α) (t : set β) : image r s ⊆ t ↔ s ⊆ core r t :=
iff.intro
  (λ h x xs y rxy, h ⟨x, xs, rxy⟩)
  (λ h y ⟨x, xs, rxy⟩, h xs y rxy)

theorem image_core_gc : galois_connection r.image r.core :=
image_subset_iff _

end rel

namespace function

/-- The graph of a function as a relation. -/
def graph (f : α → β) : rel α β := λ x y, f x = y

end function

namespace set

-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional

lemma image_eq (f : α → β) (s : set α) : f '' s = (function.graph f).image s :=
by simp [set.image, function.graph, rel.image]

lemma preimage_eq (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph f).preimage s :=
by simp [set.preimage, function.graph, rel.preimage, rel.inv, flip, rel.image]

lemma preimage_eq_core (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph f).core s :=
 by simp [set.preimage, function.graph, rel.core]

end set

/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad

Operations on set-valued functions, aka partial multifunctions, aka relations.
-/
import tactic.basic data.set.lattice order.complete_lattice

variables {α : Type*} {β : Type*} {γ : Type*}

@[derive lattice.complete_lattice]
def rel (α : Type*) (β : Type*) := α → β → Prop

namespace rel

variables {δ : Type*} (r : rel α β)

/-- The converse relation : `r.flip x y ↔ r y x` -/
protected def flip : rel β α := flip r

lemma flip_def (x : α) (y : β) : r.flip y x ↔ r x y := iff.rfl

lemma flip_flip : flip (flip r) = r := by { ext x y, reflexivity }

def dom := {x | ∃ y, r x y}

def codom := {y | ∃ x, r x y}

lemma codom_flip : r.flip.codom = r.dom := by { ext x y, reflexivity }

lemma dom_flip : r.flip.dom = r.codom := by { ext x y, reflexivity}

def comp (r : rel α β) (s : rel β γ) : rel α γ :=
λ x z, ∃ y, r x y ∧ s y z

local infixr ` ∘ ` :=rel.comp

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

lemma flip_id : rel.flip (@eq α) = @eq α :=
by { ext x y, split; apply eq.symm }

lemma flip_comp (r : rel α β) (s : rel β γ) : (r ∘ s).flip = s.flip ∘ r.flip :=
by { ext x z, simp [comp, rel.flip, flip, and.comm] }

def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

lemma mem_image (y : β) (s : set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
iff.refl _

lemma image_mono {s t : set α} (h : s ⊆ t) : r.image s ⊆ r.image t :=
assume y ⟨x, xs, rxy⟩, ⟨x, h xs, rxy⟩

lemma image_inter (s t : set α) : r.image (s ∩ t) ⊆ r.image s ∩ r.image t :=
assume y ⟨x, ⟨xs, xt⟩, rxy⟩, ⟨⟨x, xs, rxy⟩, ⟨x, xt, rxy⟩⟩

lemma image_union (s t : set α) : r.image (s ∪ t) = r.image s ∪ r.image t :=
set.subset.antisymm
  (λ y ⟨x, xst, rxy⟩,
    begin
      cases xst with xs xt,
      { left, exact ⟨x, xs, rxy⟩ },
      right, exact ⟨x, xt, rxy⟩
    end)
  (λ y ymem,
    begin
      rcases ymem with ⟨x, xs, rxy⟩ | ⟨x, xt, rxy⟩; existsi x,
      { split, { left, exact xs }, exact rxy},
      split, { right, exact xt }, exact rxy
    end)

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

def preimage (s : set β) : set α := r.flip.image s

lemma mem_preimage (x : α) (s : set β) : x ∈ preimage r s ↔ ∃ y ∈ s, r x y :=
iff.refl _

lemma preimage_def (s : set β) : preimage r s = {x | ∃ y ∈ s, r x y} :=
set.ext $ λ x, mem_preimage _ _ _

lemma preimage_mono {s t : set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
image_mono _ h

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
image_inter _ s t

lemma preimage_union (s t : set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
image_union _ s t

lemma preimage_id (s : set α) : preimage (@eq α) s = s :=
by simp only [preimage, flip_id, image_id]

lemma preimage_comp (s : rel β γ) (t : set γ) :
  preimage (r ∘ s) t = preimage r (preimage s t) :=
by simp only [preimage, flip_comp, image_comp]

lemma preimage_univ : r.preimage set.univ = r.dom :=
by { rw [preimage, image_univ, codom_flip] }

def core (s : set β) := {x | ∀ y, r x y → y ∈ s}

lemma mem_core (x : α) (s : set β) : x ∈ core r s ↔ ∀ y, r x y → y ∈ s :=
iff.refl _

lemma core_mono {s t : set β} (h : s ⊆ t) : r.core s ⊆ r.core t :=
assume x h' y rxy, h (h' y rxy)

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
set.ext (by simp [mem_core, imp_and_distrib, forall_and_distrib])

lemma core_union (s t : set β) : r.core (s ∪ t) ⊇ r.core s ∪ r.core t :=
λ x,
  begin
    simp [mem_core], intro h, cases h with hs ht; intros y rxy,
    { left, exact hs y rxy },
    right, exact ht y rxy
  end

lemma core_univ : r.core set.univ = set.univ := set.ext (by simp [mem_core])

lemma core_id (s : set α) : core (@eq α) s = s :=
by simp [core]

lemma core_comp (s : rel β γ) (t : set γ) :
  core (r ∘ s) t = core r (core s t) :=
begin
  ext x, simp [core, comp], split,
  { intros h y rxy z syz, exact h z y rxy syz },
  intros h z y rzy syz, exact h y rzy z syz
end

def restrict_domain (s : set α) : rel {x // x ∈ s} β :=
λ x y, r x.val y

theorem image_subset_iff (s : set α) (t : set β) : image r s ⊆ t ↔ s ⊆ core r t :=
iff.intro
  (λ h x xs y rxy, h ⟨x, xs, rxy⟩)
  (λ h y ⟨x, xs, rxy⟩, h xs y rxy)

theorem core_preimage_gc : galois_connection (image r) (core r) :=
image_subset_iff _

end rel

namespace function

def graph (f : α → β) : rel α β := λ x y, f x = y

end function

namespace set

-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional

lemma image_eq (f : α → β) (s : set α) : f '' s = (function.graph f).image s :=
by simp [set.image, function.graph, rel.image]

lemma preimage_eq (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph f).preimage s :=
by simp [set.preimage, function.graph, rel.preimage, rel.flip, flip, rel.image]

lemma preimage_eq_core (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph f).core s :=
 by simp [set.preimage, function.graph, rel.core]

end set

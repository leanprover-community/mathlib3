/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import tactic.basic data.set.lattice order.complete_lattice

/-!
# Operations on relations

## Main definitions

* `rel α β := α → β → Prop` : set-valued functions, aka partial multifunctions, aka relations.
* `rel.graph` : reinterpret the relation as a subset of `α × β`.
* `rel.inv` : the inverse relation, aka `flip r`.
* `rel.dom`, ` : the set of `x : α` that are related to at least one `y : β`
* `rel.codom` : the set of `y : β` that are related to at least one `x : α`
* `rel.image` : the image of a set `s : set α` is the set of `y : β` that are related
  to at least one `x ∈ s`.
* `rel.comp` : composition of relations, `(r₁.comp r₂) x z = ∃ y, r₁ x y ∧ r₂ y z`.
* `rel.preimage` : the preimage of a set `s : set β` is the set of `x : α` that are related
  to at least one `y ∈ s`.
* `rel.core` : the core of a set `s : set β` is the set of `x : α` such that 
-/

variables {α : Type*} {β : Type*} {γ : Type*}

/-- A relation on `α` and `β`, aka a set-valued function, aka a partial multifunction --/
def rel (α : Type*) (β : Type*) := α → β → Prop

namespace rel

variables {δ : Type*} (r : rel α β)

instance : lattice.complete_lattice (rel α β) :=
by unfold rel; apply_instance

/-- Graph of a relation -/
def graph : set (α × β) := function.uncurry' r

lemma mem_graph {x : α × β} : x ∈ r.graph ↔ r x.fst x.snd :=
iff.rfl

lemma mk_mem_graph {x : α} {y : β} : (x, y) ∈ r.graph ↔ r x y :=
iff.rfl

/-- Inverse relation -/
def inv : rel β α := flip r

lemma inv_def (x : α) (y : β) : r.inv y x ↔ r x y := iff.rfl

lemma inv_inv : inv (inv r) = r := rfl

/-- Domain of a relation -/
def dom : set α := {x | ∃ y, r x y}

/-- Codomain of a relation. TODO: codomain or range? -/
def codom : set β := {y | ∃ x, r x y}

lemma codom_inv : r.inv.codom = r.dom := rfl

lemma dom_inv : r.inv.dom = r.codom := rfl

/-- Composition of relations -/
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
by { ext, apply exists_eq_right }

@[simp]
lemma comp_left_id (r : rel α β) : @eq α ∘ r = r :=
by { ext, apply exists_eq_left' }

lemma inv_id : inv (@eq α) = @eq α :=
by { ext x y, split; apply eq.symm }

lemma inv_comp (r : rel α β) (s : rel β γ) : inv (r ∘ s) = inv s ∘ inv r :=
by { ext x z, simp only [comp, inv, flip, and.comm] }

/-- Image of a set under a relation -/
def image (s : set α) : set β := {y | ∃ x ∈ s, r x y}

lemma mem_image (y : β) (s : set α) : y ∈ image r s ↔ ∃ x ∈ s, r x y :=
iff.rfl

lemma image_def (s : set α) : image r s = {y | ∃ x ∈ s, r x y} := rfl

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

lemma image_singleton (x : α) : r.image {x} = set_of (r x) :=
by ext y; simp [rel.image, set.mem_singleton_iff, exists_prop, exists_eq_left]

@[simp]
lemma image_id (s : set α) : image (@eq α) s = s :=
by { ext x, simp [mem_image] }

lemma image_comp (s : rel β γ) (t : set α) : image (r ∘ s) t = image s (image r t) :=
begin
  ext z, split,
  { rintros ⟨x, xt, y, rxy, syz⟩, exact ⟨y, ⟨x, xt, rxy⟩, syz⟩ },
  rintros ⟨y, ⟨x, xt, rxy⟩, syz⟩, exact ⟨x, xt, y, rxy, syz⟩
end

lemma image_univ : r.image set.univ = r.codom := by { ext y, simp [mem_image, codom] }

/-- Preimage of a set under a relation `r`. Same as the image of `s` under `r.inv` -/
def preimage (s : set β) : set α := r.inv.image s

lemma mem_preimage (x : α) (s : set β) : x ∈ preimage r s ↔ ∃ y ∈ s, r x y :=
iff.rfl

lemma preimage_def (s : set β) : preimage r s = {x | ∃ y ∈ s, r x y} :=
rfl

lemma preimage_mono {s t : set β} (h : s ⊆ t) : r.preimage s ⊆ r.preimage t :=
image_mono _ h

lemma preimage_inter (s t : set β) : r.preimage (s ∩ t) ⊆ r.preimage s ∩ r.preimage t :=
image_inter _ s t

lemma preimage_union (s t : set β) : r.preimage (s ∪ t) = r.preimage s ∪ r.preimage t :=
image_union _ s t

lemma preimage_singleton (y : β) : r.preimage {y} = set_of (flip r y) :=
r.inv.image_singleton y

lemma preimage_id (s : set α) : preimage (@eq α) s = s :=
by simp only [preimage, inv_id, image_id]

lemma preimage_comp (s : rel β γ) (t : set γ) :
  preimage (r ∘ s) t = preimage r (preimage s t) :=
by simp only [preimage, inv_comp, image_comp]

lemma preimage_univ : r.preimage set.univ = r.dom :=
r.inv.image_univ

/-- Core of a set `s : set β` w.r.t `r : rel α β` is the set of `x : α` that are related *only* to elements of `s`. -/
def core (s : set β) := {x | ∀ y, r x y → y ∈ s}

lemma mem_core (x : α) (s : set β) : x ∈ core r s ↔ ∀ y, r x y → y ∈ s :=
iff.rfl

lemma core_mono {s t : set β} (h : s ⊆ t) : r.core s ⊆ r.core t :=
assume x h' y rxy, h (h' y rxy)

lemma core_inter (s t : set β) : r.core (s ∩ t) = r.core s ∩ r.core t :=
set.ext (by simp [mem_core, imp_and_distrib, forall_and_distrib])

lemma core_union (s t : set β) : r.core (s ∪ t) ⊇ r.core s ∪ r.core t :=
set.union_subset (r.core_mono $ s.subset_union_left t) (r.core_mono $ s.subset_union_right t)

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

/-- Restrict the domain of a relation -/
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

/-- The graph of a function as a relation -/
def graph' (f : α → β) : rel α β := λ x y, f x = y

theorem graph'_id : graph' (@id α) = @eq α := rfl

theorem graph'_comp (f : α → β) (g : β → γ) : graph' (g ∘ f) = (graph' f).comp (graph' g) :=
by { ext x z, symmetry, apply exists_eq_left' }

theorem graph'_mk (f : α → β) (x : α) : graph' f x (f x) := eq.refl (f x)

theorem graph'_inj : function.injective $ @function.graph' α β :=
λ f g h, funext $
assume x,
show graph' f x (g x),
from h.symm ▸ graph'_mk g x

/-- The graph of a function `f : α → β` as a set in `α × β` -/
def graph (f : α → β) : set (α × β) := (function.graph' f).graph

lemma graph_def (f : α → β) : function.graph f = { x : α × β | f x.1 = x.2 } := rfl

end function

namespace set

-- TODO: if image were defined with bounded quantification in corelib, the next two would
-- be definitional

lemma image_eq (f : α → β) (s : set α) : f '' s = (function.graph' f).image s :=
by simp only [set.image, function.graph', rel.image, exists_prop]

lemma preimage_eq (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph' f).preimage s :=
by simp only [set.preimage, function.graph', rel.preimage_def, exists_prop, exists_eq_right']

lemma preimage_eq_core (f : α → β) (s : set β) :
  f ⁻¹' s = (function.graph' f).core s :=
by simp only [set.preimage, function.graph', rel.core, forall_eq']

end set

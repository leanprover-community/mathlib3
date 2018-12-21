/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Johannes Hölzl, Reid Barton

Defines a category, as a typeclass parametrised by the type of objects.
Introduces notations
  `X ⟶ Y` for the morphism spaces,
  `f ≫ g` for composition in the 'arrows' convention.

Users may like to add `f ⊚ g` for composition in the standard convention, using
```
local notation f ` ⊚ `:80 g:80 := category.comp g f    -- type as \oo
```
-/

import tactic.restate_axiom
import tactic.replacer
import tactic.interactive
import tactic.tidy

namespace category_theory

universes u v

/-
The propositional fields of `category` are annotated with the auto_param `obviously`,
which is defined here as a
[`replacer` tactic](https://github.com/leanprover/mathlib/blob/master/docs/tactics.md#def_replacer).
We then immediately set up `obviously` to call `tidy`. Later, this can be replaced with more
powerful tactics.
-/
def_replacer obviously
@[obviously] meta def obviously' := tactic.tidy

/--
The typeclass `category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `category.{u v} C`. (See also `large_category` and `small_category`.)
-/
class category (obj : Type u) : Type (max u (v+1)) :=
(hom      : obj → obj → Type v)
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, hom X Y → hom Y Z → hom X Z)
(id_comp' : ∀ {X Y : obj} (f : hom X Y), comp (id X) f = f . obviously)
(comp_id' : ∀ {X Y : obj} (f : hom X Y), comp f (id Y) = f . obviously)
(assoc'   : ∀ {W X Y Z : obj} (f : hom W X) (g : hom X Y) (h : hom Y Z),
  comp (comp f g) h = comp f (comp g h) . obviously)

notation `𝟙` := category.id -- type as \b1
infixr ` ≫ `:80 := category.comp -- type as \gg
infixr ` ⟶ `:10 := category.hom -- type as \h

-- `restate_axiom` is a command that creates a lemma from a structure field,
-- discarding any auto_param wrappers from the type.
-- (It removes a backtick from the name, if it finds one, and otherwise adds "_lemma".)
restate_axiom category.id_comp'
restate_axiom category.comp_id'
restate_axiom category.assoc'
attribute [simp] category.id_comp category.comp_id category.assoc
attribute [trans] category.comp

lemma category.assoc_symm {C : Type u} [category.{u v} C] {W X Y Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
  f ≫ (g ≫ h) = (f ≫ g) ≫ h :=
by rw ←category.assoc

/--
A `large_category` has objects in one universe level higher than the universe level of
the morphisms. It is useful for examples such as the category of types, or the category
of groups, etc.
-/
abbreviation large_category (C : Type (u+1)) : Type (u+1) := category.{u+1 u} C
/--
A `small_category` has objects and morphisms in the same universe level.
-/
abbreviation small_category (C : Type u)     : Type (u+1) := category.{u u} C

structure bundled (c : Type u → Type v) :=
(α : Type u)
(str : c α)

instance (c : Type u → Type v) : has_coe_to_sort (bundled c) :=
{ S := Type u, coe := bundled.α }

def mk_ob {c : Type u → Type v} (α : Type u) [str : c α] : bundled c :=
@bundled.mk c α str

/-- `concrete_category hom` collects the evidence that a type constructor `c` and a morphism
predicate `hom` can be thought of as a concrete category.
In a typical example, `c` is the type class `topological_space` and `hom` is `continuous`. -/
structure concrete_category {c : Type u → Type v}
  (hom : out_param $ ∀{α β : Type u}, c α → c β → (α → β) → Prop) :=
(hom_id : ∀{α} (ia : c α), hom ia ia id)
(hom_comp : ∀{α β γ} (ia : c α) (ib : c β) (ic : c γ) {f g},
  hom ia ib f → hom ib ic g → hom ia ic (g ∘ f))
attribute [class] concrete_category

instance {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] : category (bundled c) :=
{ hom   := λa b, subtype (hom a.2 b.2),
  id    := λa, ⟨@id a.1, h.hom_id a.2⟩,
  comp  := λa b c f g, ⟨g.1 ∘ f.1, h.hom_comp a.2 b.2 c.2 f.2 g.2⟩ }

@[simp] lemma concrete_category_id
  {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] (X : bundled c) : subtype.val (𝟙 X) = id := rfl
@[simp] lemma concrete_category_comp
  {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) :
  subtype.val (f ≫ g) = g.val ∘ f.val := rfl

instance {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] {R S : bundled c} : has_coe_to_fun (R ⟶ S) :=
{ F := λ f, R → S,
  coe := λ f, f.1 }

@[simp] lemma bundled_hom_coe
  {c : Type u → Type v} (hom : ∀{α β : Type u}, c α → c β → (α → β) → Prop)
  [h : concrete_category @hom] {R S : bundled c} (val : R → S) (prop) (r : R) :
  (⟨val, prop⟩ : R ⟶ S) r = val r := rfl

section
variables {C : Type u} [𝒞 : category.{u v} C] {X Y Z : C}
include 𝒞

class epi  (f : X ⟶ Y) : Prop :=
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) : Prop :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h :=
⟨ λ p, epi.left_cancellation g h p, begin intro a, subst a end ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h :=
⟨ λ p, mono.right_cancellation g h p, begin intro a, subst a end ⟩
end

section
variable (C : Type u)
variable [category.{u v} C]

universe u'

instance ulift_category : category.{(max u u') v} (ulift.{u'} C) :=
{ hom  := λ X Y, (X.down ⟶ Y.down),
  id   := λ X, 𝟙 X.down,
  comp := λ _ _ _ f g, f ≫ g }

-- We verify that this previous instance can lift small categories to large categories.
example (D : Type u) [small_category D] : large_category (ulift.{u+1} D) := by apply_instance
end

variables (α : Type u)

instance [preorder α] : small_category α :=
{ hom  := λ U V, ulift (plift (U ≤ V)),
  id   := λ X, ⟨ ⟨ le_refl X ⟩ ⟩,
  comp := λ X Y Z f g, ⟨ ⟨ le_trans f.down.down g.down.down ⟩ ⟩ }

section
variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞

def End (X : C) := X ⟶ X

instance {X : C} : monoid (End X) := by refine { one := 𝟙 X, mul := λ x y, x ≫ y, .. } ; obviously
end

end category_theory

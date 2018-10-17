/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and type class instance.
-/

import category_theory.category

universes u v

namespace category_theory
variables {c d : Type u → Type v} {α : Type u}

/--
`concrete_category @hom` collects the evidence that a type constructor `c` and a
morphism predicate `hom` can be thought of as a concrete category.

In a typical example, `c` is the type class `topological_space` and `hom` is `continuous`.
-/
structure concrete_category (hom : out_param $ ∀ {α β : Type u}, c α → c β → (α → β) → Prop) :=
(hom_id : ∀ {α} (ia : c α), hom ia ia id)
(hom_comp : ∀ {α β γ} (ia : c α) (ib : c β) (ic : c γ) {f g}, hom ia ib f → hom ib ic g → hom ia ic (g ∘ f))

attribute [class] concrete_category

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Type u → Type v) : Type (max (u+1) v) :=
(α : Type u)
(inst : c α)

/-
Note on the definition of `bundled`:

It is possible to define `bundled` with square brackets for the instance:

  structure bundled (c : Type u → Type v) :=
  (α : Type u)
  [inst : c α]

The result is a constructor with this type:

  mk : ∀ (c : Type u → Type v) (α : Type u) [c α], bundled c

However, that leads to needing `@mk` in practice and does not appear to provide
any benefit. Therefore, we defined the constructor without square brackets.
-/

namespace bundled

instance : has_coe_to_sort (bundled c) :=
{ S := Type u, coe := bundled.α }

/-- Map over the bundled instance -/
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
⟨b.α, f b.inst⟩

section concrete_category
variables (hom : ∀ {α β : Type u}, c α → c β → (α → β) → Prop)
variables [h : concrete_category @hom]
include h

instance : category (bundled c) :=
{ hom   := λ a b, subtype (hom a.2 b.2),
  id    := λ a, ⟨@id a.1, h.hom_id a.2⟩,
  comp  := λ a b c f g, ⟨g.1 ∘ f.1, h.hom_comp a.2 b.2 c.2 f.2 g.2⟩ }

@[simp] lemma concrete_category_id (X : bundled c) : subtype.val (𝟙 X) = id :=
rfl

variables {X Y Z : bundled c}

instance : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X → Y,
  coe := λ f, f.1 }

@[simp] lemma concrete_category_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
  subtype.val (f ≫ g) = g.val ∘ f.val :=
rfl

end concrete_category

end bundled

end category_theory

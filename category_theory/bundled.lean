/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and type class instance.
-/

import category_theory.category

universes u v

namespace category_theory

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
variables {c d : Type u → Type v} {α : Type u}

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
{ hom   := λa b, subtype (hom a.2 b.2),
  id    := λa, ⟨@id a.1, h.hom_id a.2⟩,
  comp  := λa b c f g, ⟨g.1 ∘ f.1, h.hom_comp a.2 b.2 c.2 f.2 g.2⟩ }

@[simp] lemma concrete_category_id (X : bundled c) : subtype.val (𝟙 X) = id :=
rfl

@[simp] lemma concrete_category_comp {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) :
  subtype.val (f ≫ g) = g.val ∘ f.val :=
rfl

instance {R S : bundled c} : has_coe_to_fun (R ⟶ S) :=
{ F   := λ f, R → S,
  coe := λ f, f.1 }

end concrete_category

end bundled

end category_theory

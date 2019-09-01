/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and structure.
-/
import category_theory.types
import category_theory.bundled

universes u v

namespace category_theory
variables {c d : Type u → Type v} {α : Type u}


/--
`concrete_category @hom` collects the evidence that a type constructor `c` and a
morphism predicate `hom` can be thought of as a concrete category.

In a typical example, `c` is the type class `topological_space` and `hom` is
`continuous`.
-/
structure concrete_category (hom : out_param $ ∀ {α β}, c α → c β → (α → β) → Prop) :=
(hom_id : ∀ {α} (ia : c α), hom ia ia id)
(hom_comp : ∀ {α β γ} (ia : c α) (ib : c β) (ic : c γ) {g f}, hom ib ic g → hom ia ib f → hom ia ic (g ∘ f))

attribute [class] concrete_category

namespace bundled

variables (hom : ∀ {α β : Type u}, c α → c β → (α → β) → Prop)
variables [h : concrete_category @hom]
include h

instance : category.{u+1} (bundled c) :=
{ hom   := λ a b, subtype (hom a.2 b.2),
  id    := λ a, ⟨@id a.1, h.hom_id a.2⟩,
  comp  := λ a b c f g, ⟨g.1 ∘ f.1, h.hom_comp a.2 b.2 c.2 g.2 f.2⟩ }

variables {hom}
variables {X Y Z : bundled c}

@[simp] lemma concrete_category_id (X : bundled c) : subtype.val (𝟙 X) = id := rfl

@[simp] lemma concrete_category_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
  subtype.val (f ≫ g) = g.val ∘ f.val := rfl

instance : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X → Y,
  coe := λ f, f.1 }

@[extensionality] lemma hom_ext  {f g : X ⟶ Y} : (∀ x : X, f x = g x) → f = g :=
λ w, subtype.ext.2 $ funext w

@[simp] lemma coe_id {X : bundled c} : ((𝟙 X) : X → X) = id := rfl
@[simp] lemma coe_comp {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x) := rfl
@[simp] lemma bundled_hom_coe (val : X → Y) (prop) (x : X) :
  (⟨val, prop⟩ : X ⟶ Y) x = val x := rfl

end bundled

def concrete_functor
  {C : Type u → Type v} {hC : ∀{α β}, C α → C β → (α → β) → Prop} [concrete_category @hC]
  {D : Type u → Type v} {hD : ∀{α β}, D α → D β → (α → β) → Prop} [concrete_category @hD]
  (m : ∀{α}, C α → D α) (h : ∀{α β} {ia : C α} {ib : C β} {f}, hC ia ib f → hD (m ia) (m ib) f) :
  bundled C ⥤ bundled D :=
{ obj := bundled.map @m,
  map := λ X Y f, ⟨ f, h f.2 ⟩ }

section forget
variables {C : Type u → Type v} {hom : ∀α β, C α → C β → (α → β) → Prop} [i : concrete_category hom]
include i

/-- The forgetful functor from a bundled category to `Sort`. -/
def forget : bundled C ⥤ Type u := { obj := bundled.α, map := λ a b h, h.1 }

instance forget.faithful : faithful (forget : bundled C ⥤ Type u) :=
{ injectivity' :=
  begin
    rintros X Y ⟨f,_⟩ ⟨g,_⟩ p,
    congr, exact p,
  end }

end forget

end category_theory

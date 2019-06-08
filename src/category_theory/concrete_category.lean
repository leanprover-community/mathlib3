/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather

Bundled type and structure.
-/
import category_theory.functor
import category_theory.types

universes u v

namespace category_theory
variables {c d : Sort u → Sort v} {α : Sort u}

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

/-- `bundled` is a type bundled with a type class instance for that type. Only
the type class is exposed as a parameter. -/
structure bundled (c : Sort u → Sort v) : Sort (max (u+1) v) :=
(α : Sort u)
(str : c α . tactic.apply_instance)

def mk_ob {c : Sort u → Sort v} (α : Sort u) [str : c α] : bundled c := ⟨α, str⟩

namespace bundled

instance : has_coe_to_sort (bundled c) :=
{ S := Sort u, coe := bundled.α }

/-- Map over the bundled structure -/
def map (f : ∀ {α}, c α → d α) (b : bundled c) : bundled d :=
⟨b.α, f b.str⟩

section concrete_category
variables (hom : ∀ {α β : Sort u}, c α → c β → (α → β) → Prop)
variables [h : concrete_category @hom]
include h

instance category : category (bundled c) :=
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
@[simp] lemma bundled_hom_coe (val : X → Y) (prop) (x : X) :
  (⟨val, prop⟩ : X ⟶ Y) x = val x := rfl

end concrete_category

end bundled

def concrete_functor
  {C : Sort u → Sort v} {hC : ∀{α β}, C α → C β → (α → β) → Prop} [concrete_category @hC]
  {D : Sort u → Sort v} {hD : ∀{α β}, D α → D β → (α → β) → Prop} [concrete_category @hD]
  (m : ∀{α}, C α → D α) (h : ∀{α β} {ia : C α} {ib : C β} {f}, hC ia ib f → hD (m ia) (m ib) f) :
  bundled C ⥤ bundled D :=
{ obj := bundled.map @m,
  map := λ X Y f, ⟨ f, h f.2 ⟩ }

section forget
variables {C : Sort u → Sort v} {hom : ∀α β, C α → C β → (α → β) → Prop} [i : concrete_category hom]
include i

/-- The forgetful functor from a bundled category to `Sort`. -/
def forget : bundled C ⥤ Sort u := { obj := bundled.α, map := λ a b h, h.1 }

instance forget.faithful : faithful (forget : bundled C ⥤ Sort u) :=
{ injectivity' :=
  begin
    rintros X Y ⟨f,_⟩ ⟨g,_⟩ p,
    congr, exact p,
  end }

end forget

end category_theory

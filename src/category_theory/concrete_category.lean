/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Johannes Hölzl, Reid Barton, Sean Leather, Yury Kudryashov
-/
import category_theory.types category_theory.full_subcategory category_theory.bundled

/-!
# Concrete categories

A concrete category is a category `C` with a fixed faithful functor
`forget : C ⥤ Sort*`.

## Main definitions

### Concrete categories

We define concrete categories using a `class concrete_category`.

In particular, we impose no restrictions on the carrier type `C`, so
`Type` is a concrete category with the identity forgetful functor.

### `bundled` carrier type

Since algebraic structures (`monoid`, `group`, `ring`, `field`) in
Lean use unbundled classes, we define a unified way to bundle them.
Given a function `c : Type u → Type v`, `bundled c` is the structure
of pairs `(α, str)`, where `α : Type u`, and `str : c α`.

For a concrete category on `bundled c`, it makes sense to require that
`forget.obj X = X.α`. Some parts of mathlib use bundled morphism
structures, other parts use unbundled morphism classes. We provide
convenience functions to define concrete categories in both cases.

In both cases this is done using the `bundled_category` class. Its
default constructor assumes the bundled morphisms approach, and requires 

* an injective `to_fun : hom (ia : c α) (ib : c β) → α → β` projection;
* `id` and `comp g f` morphisms that project to `id` and `g ∘ f`.

Note that the argument order agrees with `function.comp`, not
`category_theory.comp`. This way we can directly use
`@monoid_hom.comp` as an argument to `bundled_category.mk`.

For a full concrete subcategory `D = bundled d` of a bundled category
`C = bundled c` we provide `bundled_category.restrict_str`
constructor. This constructor agrees with `induced_category` but also
allows us to automatically prove that the `induced_functor : C ⥤ D` is
a “partially forgetting” functor, i.e., `induced_functor ⋙ forget D =
forget C`.

For unbundled morphisms we provide a convenience constructor
`bundled_category.of_hom_class`. It accepts a morphism class `hom : Π
α β (ia : c α) (ib : c β), (α → β) → Prop` together with proofs of
`hom id` and `hom g → hom f → hom (g ∘ f)`, and creates a
`bundled_category` instance using `subtype hom` as the bundled
morphisms type.

## Forgetful functors

Each concrete category `C` comes with a canonical faithful functor
`forget C : C ⥤ Sort*`. We say that a concrete category `C` admits a
forgetful functor to a concrete category `D`, if it has a functor
`forget₂ C D : C ⥤ D` such that `(forget₂ C D) ⋙ (forget D) = forget
C`, see `class has_forget`.

We provide convenience constructors `has_forget.mk'` and
`bundled_has_forget` to create instances of this class.

-/

universes v u₁ u₂ u₃

namespace category_theory

/-- A concrete category is a category `C` with a fixed faithful functor `forget : C ⥤ Type`. -/
class concrete_category (C : Type u₂) extends category.{v} C :=
(forget : C ⥤ Sort u₁)
[forget_faithful : faithful forget]

@[reducible] def forget (C : Type u₂) [concrete_category C] := concrete_category.forget C

attribute [instance] concrete_category.forget_faithful

instance concrete_category.types : concrete_category (Sort u₂) :=
{ forget := 𝟭 _ }

class has_forget (C : Type u₂) (D : Type u₃) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D] :=
(forget₂ : C ⥤ D)
(forget_comp : forget₂ ⋙ (forget D) = forget C)

@[reducible] def forget₂ (C D : Type u₂) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  [has_forget C D] : C ⥤ D :=
has_forget.forget₂ C D

instance forget_faithful (C D : Type u₂) [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  [has_forget C D] : faithful (forget₂ C D) :=
(has_forget.forget_comp C D).faithful_of_comp

instance induced_category.concrete_category {C : Type u₂} {D : Type u₃} [concrete_category D] (f : C → D) :
  concrete_category (induced_category f) :=
{ forget := induced_functor f ⋙ forget D }

instance induced_category.has_forget {C : Type u₂} {D : Type u₃} [concrete_category D] (f : C → D) :
  has_forget (induced_category f) D :=
{ forget₂ := induced_functor f,
  forget_comp := rfl }

def has_forget.mk' {C D : Type u₂} [concrete_category.{v u₁} C] [concrete_category.{v u₁} D]
  (obj : C → D) (h_obj : ∀ X, (forget D).obj (obj X) = (forget C).obj X)
  (map : ∀ {X Y}, (X ⟶ Y) → (obj X ⟶ obj Y))
  (h_map : ∀ {X Y} {f : X ⟶ Y}, (forget D).map (map f) == (forget C).map f) :
has_forget C D :=
{ forget₂ := faithful.div _ _ _ @h_obj _ @h_map,
  forget_comp := by apply faithful.div_comp }

instance (C : Type u₂) [concrete_category.{u₂ u₂} C] : has_forget C (Sort u₂) :=
{ forget₂ := forget C,
  forget_comp := functor.comp_id _ }

namespace bundled

class bundled_category {c : Type u₂ → Type u₁} (hom : Π {α β}, c α → c β → Sort v) :=
(to_fun : Π {α β} {ia : c α} {ib : c β}, hom ia ib → α → β)
(to_fun_inj : ∀ {α β} {ia : c α} {ib : c β}, function.injective (@to_fun α β ia ib))
(id' : Π {α} (ia : c α), hom ia ia)
(to_fun_id' : Π {α} (ia : c α), to_fun (id' ia) = id)
(comp' : Π {α β γ} {ia : c α} {ib : c β} {ic : c γ}, hom ib ic → hom ia ib → hom ia ic)
(to_fun_comp' : ∀ {α β γ} {ia : c α} {ib : c β} {ic : c γ} (f : hom ia ib) (g : hom ib ic),
                 to_fun (comp' g f) = (to_fun g) ∘ (to_fun f))

namespace bundled_category

def of_hom_class {c : Type u₂ → Type u₁} (hom : Π {α β}, c α → c β → (α → β) → Prop)
  (h_id : ∀ {α} (ia : c α), hom ia ia id)
  (h_comp : ∀ {α β γ} {ia : c α} {ib : c β} {ic : c γ} {g : β → γ} {f : α → β} (hg : hom ib ic g)
    (hf : hom ia ib f), hom ia ic (g ∘ f)) :
  bundled_category (λ α β (ia : c α) ib, subtype (hom ia ib)) :=
{ to_fun := λ _ _ _ _, subtype.val,
  id' := λ α ia, ⟨id, h_id ia⟩,
  to_fun_id' := by intros; refl,
  comp' := λ _ _ _ _ _ _ g f, ⟨g.1 ∘ f.1, h_comp g.2 f.2⟩,
  to_fun_comp' := by intros; refl,
  to_fun_inj := by intros; apply subtype.eq }

variables {c : Type u₂ → Type u₁} (hom : Π {α β}, c α → c β → Sort v) [h : bundled_category @hom]
include h

instance : has_hom.{v} (bundled c) := ⟨λ α β, @hom α β α.str β.str⟩

protected def has_coe_to_fun (α β : bundled c) : has_coe_to_fun (α ⟶ β) :=
{ F := λ _, α → β, coe := @to_fun c @hom h α.1 β.1 α.2 β.2}

local attribute [instance] bundled_category.has_coe_to_fun

lemma coe_def (α β : bundled c) (f : α ⟶ β) :
  (f : α → β) = @to_fun c @hom h α.1 β.1 α.2 β.2 f := rfl

instance : category_struct (bundled c) :=
{ id   := λ α, bundled_category.id' @hom α.str,
  comp := by intros; apply h.comp'; assumption }

@[simp] lemma coe_comp {α β γ : bundled c} {f : α ⟶ β} {g : β ⟶ γ} :
  (f ≫ g : α → γ) = g ∘ f :=
to_fun_comp' c f g

@[simp] lemma coe_id {α : bundled c} : (𝟙 α : α → α) = id := to_fun_id' @hom α.str

-- `function.injective` doesn't work here
lemma coe_inj {α β : bundled c} {f g : α ⟶ β} (p : (f : α → β) = g) : f = g :=
to_fun_inj @hom p

instance : category (bundled c) :=
{ id_comp' := by intros; apply coe_inj; simp only [coe_comp, coe_id, function.comp.right_id],
  comp_id' := by intros; apply coe_inj; simp only [coe_comp, coe_id, function.comp.left_id],
  assoc'   := by intros; apply coe_inj; simp only [coe_comp] }

/-- Custom constructor for creating concrete categories on `bundled c` (e.g., `bundled monoid`) -/
instance to_concrete_category : concrete_category.{v} (bundled c) :=
{ forget := { obj := λ α, α,
              map := λ α β f, f,
              map_id' := by apply coe_id,
              map_comp' := by apply coe_comp },
  forget_faithful := { injectivity' := by apply coe_inj } }

variables {hom} (h) {d : Type u₂ → Type u₁} (h₂ : ∀ {α}, d α → c α)
include h₂

protected def restrict_str : bundled_category (λ α β ia ib, hom (@h₂ α ia) (h₂ ib)) :=
{ to_fun := by intros; apply h.to_fun; assumption,
  to_fun_inj := by intros; apply h.to_fun_inj,
  id' := by intros; apply h.id',
  to_fun_id' := by intros; apply h.to_fun_id',
  comp' := by intros; apply h.comp'; assumption,
  to_fun_comp' := by intros; apply h.to_fun_comp' }

def restrict_str_has_forget :
  @has_forget (bundled d) (bundled c) (by haveI := h.restrict_str @h₂; apply_instance) _ :=
{ forget₂ := { obj := bundled.map @h₂, map := by intros; assumption },
  forget_comp := rfl }

end bundled_category

section functor
local attribute [instance] bundled_category.has_coe_to_fun

variables {c : Type u₂ → Type u₁} {hom_c : Π {α β}, c α → c β → Sort v} [𝒞 : bundled_category @hom_c]
          {d : Type u₂ → Type u₁} {hom_d : Π {α β}, d α → d β → Sort v} [𝒟 : bundled_category @hom_d]
          (obj : ∀ {α}, c α → d α)
          (map : ∀ {α β : bundled c}, (α ⟶ β) → ((bundled.map @obj α) ⟶ (bundled.map @obj β)))
          (h_map : ∀ {α β : bundled c} (f : α ⟶ β), ⇑(map f) = (f : α → β))

include 𝒞 𝒟 h_map

def bundled_has_forget : has_forget (bundled c) (bundled d) :=
has_forget.mk'
  (bundled.map @obj)
  (λ _, rfl)
  @map
  (by intros; apply heq_of_eq; apply h_map)

end functor
end category_theory

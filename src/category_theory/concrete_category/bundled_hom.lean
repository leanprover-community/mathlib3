/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.concrete_category.basic
import category_theory.concrete_category.bundled

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types, along with
an a `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

While the helper functions in `category_theory/concrete_category.lean` are useful for categories
with unbundled homs, this file provides similar infrastructure for categories with bundled homs.
-/

universes w v u

namespace category_theory

variables (c : Type u → Type v)

/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `monoid_hom`.
This way we can use `⟨@monoid_hom, @monoid_hom.to_fun, ...⟩` in an instance. -/
structure bundled_hom :=
(hom : Π {α β : Type u} (Iα : c α) (Iβ : c β), Type w)
(to_fun : Π {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β)
(id : Π {α : Type u} (I : c α), hom I I)
(comp : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ),
  hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ)
(hom_ext : Π {α β : Type u} (Iα : c α) (Iβ : c β), function.injective (to_fun Iα Iβ) . obviously)
(id_to_fun : Π {α : Type u} (I : c α), to_fun I I (id I) = _root_.id . obviously)
(comp_to_fun : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ)
  (f : hom Iα Iβ) (g : hom Iβ Iγ),
  to_fun Iα Iγ (comp Iα Iβ Iγ g f) = (to_fun Iβ Iγ g) ∘ (to_fun Iα Iβ f) . obviously)

attribute [class] bundled_hom

attribute [extensionality] bundled_hom.hom_ext
attribute [simp] bundled_hom.id_to_fun bundled_hom.comp_to_fun

namespace bundled_hom

variable [S : bundled_hom.{w} c]
include S

instance : category (bundled c) :=
{ hom := λ X Y, @bundled_hom.hom c S X.α Y.α X.str Y.str,
  id := λ X, @bundled_hom.id c S X.α X.str,
  comp := λ X Y Z f g, @bundled_hom.comp c S X.α Y.α Z.α X.str Y.str Z.str g f }

def has_coe_to_fun {X Y : bundled c} : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X → Y,
  coe := λ f, S.to_fun X.str Y.str f }

local attribute [instance] has_coe_to_fun

@[simp] lemma coe_id {X : bundled c} : ((𝟙 X) : X → X) = _root_.id :=
S.id_to_fun X.str
@[simp] lemma coe_comp {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun (by apply S.comp_to_fun) x

instance concrete_category : concrete_category (bundled c) :=
{ forget := { obj := λ X, X,
              map := λ X Y f, f,
              map_id' := by apply coe_id,
              map_comp' := by intros; funext; apply coe_comp },
  forget_faithful := { injectivity' := by intros; ext1 } }

variable {c}

section full_subcategory

variables {d : Type u → Type v} (obj : ∀ {α}, d α → c α)
include obj

/-- Construct a `bundled_hom` representing a full subcategory of a given `bundled_hom` category. -/
protected def full_subcategory : bundled_hom d :=
{ hom := λ α β Iα Iβ, S.hom (obj Iα) (obj Iβ),
  to_fun := by intros; apply S.to_fun; assumption,
  id := by intros; apply S.id,
  id_to_fun := by intros; apply S.id_to_fun,
  comp := by intros; apply S.comp; assumption,
  comp_to_fun := by intros; apply S.comp_to_fun }

def full_subcategory_has_forget :
  @has_forget (bundled d) (bundled c)
    (by haveI := bundled_hom.full_subcategory @obj; apply_instance) _ :=
{ forget₂ := { obj := bundled.map @obj, map := by intros; assumption },
  forget_comp := rfl }

end full_subcategory

def mk_has_forget {d : Type u → Type v} [bundled_hom.{w} d] (obj : ∀ {α}, c α → d α)
  (map : ∀ {X Y : bundled c}, (X ⟶ Y) → ((bundled.map @obj X) ⟶ (bundled.map @obj Y)))
  (h_map : ∀ {X Y : bundled c} (f : X ⟶ Y), ⇑(map f) = (f : X → Y))
  : has_forget (bundled c) (bundled d) :=
has_forget.mk'
  (bundled.map @obj)
  (λ _, rfl)
  @map
  (by intros; apply heq_of_eq; apply h_map)

end bundled_hom

end category_theory

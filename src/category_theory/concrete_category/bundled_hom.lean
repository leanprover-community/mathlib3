/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Yury Kudryashov
-/
import category_theory.concrete_category.basic
import category_theory.concrete_category.bundled

/-!
# Category instances for algebraic structures that use bundled homs.

Many algebraic structures in Lean initially used unbundled homs (e.g. a bare function between types,
along with an `is_monoid_hom` typeclass), but the general trend is towards using bundled homs.

This file provides a basic infrastructure to define concrete categories using bundled homs, and
define forgetful functors between them.
-/

universes u

namespace category_theory

variables {c : Type u → Type u} (hom : Π ⦃α β : Type u⦄ (Iα : c α) (Iβ : c β), Type u)

/-- Class for bundled homs. Note that the arguments order follows that of lemmas for `monoid_hom`.
This way we can use `⟨@monoid_hom.to_fun, @monoid_hom.id ...⟩` in an instance. -/
structure bundled_hom :=
(to_fun : Π {α β : Type u} (Iα : c α) (Iβ : c β), hom Iα Iβ → α → β)
(id : Π {α : Type u} (I : c α), hom I I)
(comp : Π {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ),
  hom Iβ Iγ → hom Iα Iβ → hom Iα Iγ)
(hom_ext : ∀ {α β : Type u} (Iα : c α) (Iβ : c β), function.injective (to_fun Iα Iβ) . obviously)
(id_to_fun : ∀ {α : Type u} (I : c α), to_fun I I (id I) = _root_.id . obviously)
(comp_to_fun : ∀ {α β γ : Type u} (Iα : c α) (Iβ : c β) (Iγ : c γ)
  (f : hom Iα Iβ) (g : hom Iβ Iγ),
  to_fun Iα Iγ (comp Iα Iβ Iγ g f) = (to_fun Iβ Iγ g) ∘ (to_fun Iα Iβ f) . obviously)

attribute [class] bundled_hom

attribute [simp] bundled_hom.id_to_fun bundled_hom.comp_to_fun

namespace bundled_hom

variable [𝒞 : bundled_hom hom]
include 𝒞

/-- Every `@bundled_hom c _` defines a category with objects in `bundled c`. -/
instance : category (bundled c) :=
by refine
{ hom := λ X Y, @hom X.1 Y.1 X.str Y.str,
  id := λ X, @bundled_hom.id c hom 𝒞 X X.str,
  comp := λ X Y Z f g, @bundled_hom.comp c hom 𝒞 X Y Z X.str Y.str Z.str g f,
  comp_id' := _,
  id_comp' := _,
  assoc' := _};
intros; apply 𝒞.hom_ext;
  simp only [𝒞.id_to_fun, 𝒞.comp_to_fun, function.left_id, function.right_id]

/-- A category given by `bundled_hom` is a concrete category. -/
instance concrete_category : concrete_category (bundled c) :=
{ forget := { obj := λ X, X,
              map := λ X Y f, 𝒞.to_fun X.str Y.str f,
              map_id' := λ X, 𝒞.id_to_fun X.str,
              map_comp' := by intros; erw 𝒞.comp_to_fun; refl },
  forget_faithful := { injectivity' := by intros; apply 𝒞.hom_ext } }

/-- Usually a bundled hom structure already has a coercion to function
that works with different universes. So we don't use this as an instance. -/
def has_coe_to_fun {X Y : bundled c} : has_coe_to_fun (X ⟶ Y) :=
{ F   := λ f, X → Y,
  coe := λ f, (forget _).map f }

local attribute [instance] has_coe_to_fun

@[simp] lemma coe_id {X : bundled c} : ((𝟙 X) : X → X) = _root_.id :=
(forget _).map_id X
@[simp] lemma coe_comp {X Y Z : bundled c} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
  (f ≫ g) x = g (f x) :=
congr_fun ((forget _).map_comp _ _) x

section full_subcategory

variables {hom} (𝒞) {d : Type u → Type u} (obj : Π ⦃α⦄, d α → c α)
include obj

/--
Construct a `bundled_hom` representing a full subcategory of a given `bundled_hom` category. The
corresponding `category` and `concrete_category` instances agree with
`induced_category (bundled.map @obj)`.
-/
protected def full_subcategory : bundled_hom (λ α β (Iα : d α) (Iβ : d β), hom (obj Iα) (obj Iβ)) :=
{ to_fun := by intros; apply 𝒞.to_fun; assumption,
  id := by intros; apply 𝒞.id,
  comp := by intros; apply 𝒞.comp; assumption,
  hom_ext := by intros; apply 𝒞.hom_ext,
  id_to_fun := by intros; apply 𝒞.id_to_fun,
  comp_to_fun := by intros; apply 𝒞.comp_to_fun }

/-- A full subcategory of a concrete category with bundled homs has a forgetful functor to the
entire category. This is used to construct instances of `has_forget` in many concrete examples. -/
def full_subcategory_has_forget :
  @has_forget (bundled d) (bundled c)
    (by haveI := 𝒞.full_subcategory obj; apply_instance) (by apply_instance) :=
induced_category.has_forget (bundled.map @obj)

end full_subcategory

variables {hom}

/-- A version of `has_forget.mk'` for categories defined using `@bundled_hom`. -/
def mk_has_forget {d : Type u → Type u} {hom_d : Π ⦃α β : Type u⦄ (Iα : d α) (Iβ : d β), Type u}
  [bundled_hom hom_d] (obj : Π ⦃α⦄, c α → d α)
  (map : Π {X Y : bundled c}, (X ⟶ Y) → ((bundled.map obj X) ⟶ (bundled.map obj Y)))
  (h_map : ∀ {X Y : bundled c} (f : X ⟶ Y), (map f : X → Y) = f)
  : has_forget (bundled c) (bundled d) :=
has_forget.mk'
  (bundled.map @obj)
  (λ _, rfl)
  @map
  (by intros; apply heq_of_eq; apply h_map)

end bundled_hom

end category_theory

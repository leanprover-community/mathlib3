/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.eq_to_hom
import data.ulift

/-!
# Discrete categories

We define `discrete α := α` for any type `α`, and use this type alias
to provide a `small_category` instance whose only morphisms are the identities.

There is an annoying technical difficulty that it has turned out to be inconvenient
to allow categories with morphisms living in `Prop`,
so instead of defining `X ⟶ Y` in `discrete α` as `X = Y`,
one might define it as `plift (X = Y)`.
In fact, to allow `discrete α` to be a `small_category`
(i.e. with morphisms in the same universe as the objects),
we actually define the hom type `X ⟶ Y` as `ulift (plift (X = Y))`.

`discrete.functor` promotes a function `f : I → C` (for any category `C`) to a functor
`discrete.functor f : discrete I ⥤ C`.

Similarly, `discrete.nat_trans` and `discrete.nat_iso` promote `I`-indexed families of morphisms,
or `I`-indexed families of isomorphisms to natural transformations or natural isomorphism.

We show equivalences of types are the same as (categorical) equivalences of the corresponding
discrete categories.
-/

namespace category_theory

universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].

/--
A type synonym for promoting any type to a category,
with the only morphisms being equalities.
-/
def discrete (α : Type u₁) := α

/--
The "discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ulift (plift (X = Y))`.

See https://stacks.math.columbia.edu/tag/001A
-/
instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X = Y)),
  id   := λ X, ulift.up (plift.up rfl),
  comp := λ X Y Z g f, by { rcases f with ⟨⟨rfl⟩⟩, exact g } }

namespace discrete

variables {α : Type u₁}

instance [inhabited α] : inhabited (discrete α) :=
by { dsimp [discrete], apply_instance }

instance [subsingleton α] : subsingleton (discrete α) :=
by { dsimp [discrete], apply_instance }

/-- Extract the equation from a morphism in a discrete category. -/
lemma eq_of_hom {X Y : discrete α} (i : X ⟶ Y) : X = Y := i.down.down

@[simp] lemma id_def (X : discrete α) : ulift.up (plift.up (eq.refl X)) = 𝟙 X := rfl

variables {C : Type u₂} [category.{v₂} C]

instance {I : Type u₁} {i j : discrete I} (f : i ⟶ j) : is_iso f :=
⟨⟨eq_to_hom (eq_of_hom f).symm, by tidy⟩⟩

/--
Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def functor {I : Type u₁} (F : I → C) : discrete I ⥤ C :=
{ obj := F,
  map := λ X Y f, begin cases f, cases f, cases f, exact 𝟙 (F X) end }

@[simp] lemma functor_obj  {I : Type u₁} (F : I → C) (i : I) :
  (discrete.functor F).obj i = F i := rfl

lemma functor_map  {I : Type u₁} (F : I → C) {i : discrete I} (f : i ⟶ i) :
  (discrete.functor F).map f = 𝟙 (F i) :=
by { cases f, cases f, cases f, refl }

/--
For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
def nat_trans {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := f }

@[simp] lemma nat_trans_app  {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) (i) : (discrete.nat_trans f).app i = f i :=
rfl

/--
For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
def nat_iso {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
nat_iso.of_components f (by tidy)

@[simp]
lemma nat_iso_hom_app {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) (i : I) :
  (discrete.nat_iso f).hom.app i = (f i).hom :=
rfl

@[simp]
lemma nat_iso_inv_app {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) (i : I) :
  (discrete.nat_iso f).inv.app i = (f i).inv :=
rfl

@[simp]
lemma nat_iso_app {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) (i : I) :
  (discrete.nat_iso f).app i = f i :=
by tidy

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
def nat_iso_functor {I : Type u₁} {F : discrete I ⥤ C} : F ≅ discrete.functor (F.obj) :=
nat_iso $ λ i, iso.refl _

/--
We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I J : Type u₁} (e : I ≃ J) : discrete I ≌ discrete J :=
{ functor := discrete.functor (e : I → J),
  inverse := discrete.functor (e.symm : J → I),
  unit_iso := discrete.nat_iso (λ i, eq_to_iso (by simp)),
  counit_iso := discrete.nat_iso (λ j, eq_to_iso (by simp)), }

/-- We can convert an equivalence of `discrete` categories to a type-level `equiv`. -/
@[simps]
def equiv_of_equivalence {α β : Type u₁} (h : discrete α ≌ discrete β) : α ≃ β :=
{ to_fun := h.functor.obj,
  inv_fun := h.inverse.obj,
  left_inv := λ a, eq_of_hom (h.unit_iso.app a).2,
  right_inv := λ a, eq_of_hom (h.counit_iso.app a).1 }

end discrete

namespace discrete
variables {J : Type v₁}

open opposite

/-- A discrete category is equivalent to its opposite category. -/
protected def opposite (α : Type u₁) : (discrete α)ᵒᵖ ≌ discrete α :=
let F : discrete α ⥤ (discrete α)ᵒᵖ := discrete.functor (λ x, op x) in
begin
  refine equivalence.mk (functor.left_op F) F _ (discrete.nat_iso $ λ X, by simp [F]),
  refine nat_iso.of_components (λ X, by simp [F]) _,
  tidy
end

variables {C : Type u₂} [category.{v₂} C]

@[simp] lemma functor_map_id
  (F : discrete J ⥤ C) {j : discrete J} (f : j ⟶ j) : F.map f = 𝟙 (F.obj j) :=
begin
  have h : f = 𝟙 j, { cases f, cases f, ext, },
  rw h,
  simp,
end

end discrete

end category_theory

/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephen Morgan, Scott Morrison, Floris van Doorn
-/
import category_theory.eq_to_hom
import data.ulift

/-!
# Discrete categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `discrete α` as a structure containing a term `a : α` for any type `α`,
and use this type alias to provide a `small_category` instance
whose only morphisms are the identities.

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

-- morphism levels before object levels. See note [category_theory universes].
universes v₁ v₂ v₃ u₁ u₁' u₂ u₃

/--
A wrapper for promoting any type to a category,
with the only morphisms being equalities.
-/
-- This is intentionally a structure rather than a type synonym
-- to enforce using `discrete_equiv` (or `discrete.mk` and `discrete.as`) to move between
-- `discrete α` and `α`. Otherwise there is too much API leakage.
@[ext] structure discrete (α : Type u₁) :=
(as : α)

@[simp] lemma discrete.mk_as {α : Type u₁} (X : discrete α) : discrete.mk X.as = X :=
by { ext, refl, }

/-- `discrete α` is equivalent to the original type `α`.-/
@[simps] def discrete_equiv {α : Type u₁} : discrete α ≃ α :=
{ to_fun := discrete.as,
  inv_fun := discrete.mk,
  left_inv := by tidy,
  right_inv := by tidy, }

instance {α : Type u₁} [decidable_eq α] : decidable_eq (discrete α) :=
discrete_equiv.decidable_eq

/--
The "discrete" category on a type, whose morphisms are equalities.

Because we do not allow morphisms in `Prop` (only in `Type`),
somewhat annoyingly we have to define `X ⟶ Y` as `ulift (plift (X = Y))`.

See <https://stacks.math.columbia.edu/tag/001A>
-/
instance discrete_category (α : Type u₁) : small_category (discrete α) :=
{ hom  := λ X Y, ulift (plift (X.as = Y.as)),
  id   := λ X, ulift.up (plift.up rfl),
  comp := λ X Y Z g f, by { cases X, cases Y, cases Z, rcases f with ⟨⟨⟨⟩⟩⟩, exact g } }

namespace discrete

variables {α : Type u₁}

instance [inhabited α] : inhabited (discrete α) :=
⟨⟨default⟩⟩

instance [subsingleton α] : subsingleton (discrete α) :=
⟨by { intros, ext, apply subsingleton.elim, }⟩

/-- A simple tactic to run `cases` on any `discrete α` hypotheses. -/
meta def _root_.tactic.discrete_cases : tactic unit :=
`[cases_matching* [discrete _, (_ : discrete _) ⟶ (_ : discrete _), plift _]]

run_cmd add_interactive [``tactic.discrete_cases]

local attribute [tidy] tactic.discrete_cases

instance [unique α] : unique (discrete α) :=
unique.mk' (discrete α)

/-- Extract the equation from a morphism in a discrete category. -/
lemma eq_of_hom {X Y : discrete α} (i : X ⟶ Y) : X.as = Y.as := i.down.down

/-- Promote an equation between the wrapped terms in `X Y : discrete α` to a morphism `X ⟶ Y`
in the discrete category. -/
abbreviation eq_to_hom {X Y : discrete α} (h : X.as = Y.as) : X ⟶ Y :=
eq_to_hom (by { ext, exact h, })

/-- Promote an equation between the wrapped terms in `X Y : discrete α` to an isomorphism `X ≅ Y`
in the discrete category. -/
abbreviation eq_to_iso {X Y : discrete α} (h : X.as = Y.as) : X ≅ Y :=
eq_to_iso (by { ext, exact h, })

/-- A variant of `eq_to_hom` that lifts terms to the discrete category. -/
abbreviation eq_to_hom' {a b : α} (h : a = b) : discrete.mk a ⟶ discrete.mk b :=
eq_to_hom h

/-- A variant of `eq_to_iso` that lifts terms to the discrete category. -/
abbreviation eq_to_iso' {a b : α} (h : a = b) : discrete.mk a ≅ discrete.mk b :=
eq_to_iso h

@[simp] lemma id_def (X : discrete α) : ulift.up (plift.up (eq.refl X.as)) = 𝟙 X := rfl

variables {C : Type u₂} [category.{v₂} C]

instance {I : Type u₁} {i j : discrete I} (f : i ⟶ j) : is_iso f :=
⟨⟨eq_to_hom (eq_of_hom f).symm, by tidy⟩⟩

/--
Any function `I → C` gives a functor `discrete I ⥤ C`.
-/
def functor {I : Type u₁} (F : I → C) : discrete I ⥤ C :=
{ obj := F ∘ discrete.as,
  map := λ X Y f, by { discrete_cases, cases f, exact 𝟙 (F X), } }

@[simp] lemma functor_obj  {I : Type u₁} (F : I → C) (i : I) :
  (discrete.functor F).obj (discrete.mk i) = F i := rfl

lemma functor_map  {I : Type u₁} (F : I → C) {i : discrete I} (f : i ⟶ i) :
  (discrete.functor F).map f = 𝟙 (F i.as) :=
by tidy

/--
The discrete functor induced by a composition of maps can be written as a
composition of two discrete functors.
-/
@[simps]
def functor_comp {I : Type u₁} {J : Type u₁'} (f : J → C) (g : I → J) :
  discrete.functor (f ∘ g) ≅ discrete.functor (discrete.mk ∘ g) ⋙ discrete.functor f :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

/--
For functors out of a discrete category,
a natural transformation is just a collection of maps,
as the naturality squares are trivial.
-/
@[simps]
def nat_trans {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ⟶ G.obj i) : F ⟶ G :=
{ app := f,
  naturality' := λ X Y g, by { discrete_cases, cases g, simp, } }

/--
For functors out of a discrete category,
a natural isomorphism is just a collection of isomorphisms,
as the naturality squares are trivial.
-/
@[simps]
def nat_iso {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) : F ≅ G :=
nat_iso.of_components f (λ X Y g, by { discrete_cases, cases g, simp, })

@[simp]
lemma nat_iso_app {I : Type u₁} {F G : discrete I ⥤ C}
  (f : Π i : discrete I, F.obj i ≅ G.obj i) (i : discrete I) :
  (discrete.nat_iso f).app i = f i :=
by tidy

/-- Every functor `F` from a discrete category is naturally isomorphic (actually, equal) to
  `discrete.functor (F.obj)`. -/
@[simp]
def nat_iso_functor {I : Type u₁} {F : discrete I ⥤ C} :
  F ≅ discrete.functor (F.obj ∘ discrete.mk) :=
nat_iso $ λ i, by { discrete_cases, refl, }

/-- Composing `discrete.functor F` with another functor `G` amounts to composing `F` with `G.obj` -/
@[simp]
def comp_nat_iso_discrete {I : Type u₁} {D : Type u₃} [category.{v₃} D]
 (F : I → C) (G : C ⥤ D) : discrete.functor F ⋙ G ≅ discrete.functor (G.obj ∘ F) :=
nat_iso $ λ i, iso.refl _

/--
We can promote a type-level `equiv` to
an equivalence between the corresponding `discrete` categories.
-/
@[simps]
def equivalence {I : Type u₁} {J : Type u₂} (e : I ≃ J) : discrete I ≌ discrete J :=
{ functor := discrete.functor (discrete.mk ∘ (e : I → J)),
  inverse := discrete.functor (discrete.mk ∘ (e.symm : J → I)),
  unit_iso := discrete.nat_iso (λ i, eq_to_iso (by { discrete_cases, simp })),
  counit_iso := discrete.nat_iso (λ j, eq_to_iso (by { discrete_cases, simp })), }

/-- We can convert an equivalence of `discrete` categories to a type-level `equiv`. -/
@[simps]
def equiv_of_equivalence {α : Type u₁} {β : Type u₂} (h : discrete α ≌ discrete β) : α ≃ β :=
{ to_fun := discrete.as ∘ h.functor.obj ∘ discrete.mk,
  inv_fun := discrete.as ∘ h.inverse.obj ∘ discrete.mk,
  left_inv := λ a, by simpa using eq_of_hom (h.unit_iso.app (discrete.mk a)).2,
  right_inv := λ a, by simpa using eq_of_hom (h.counit_iso.app (discrete.mk a)).1, }

end discrete

namespace discrete
variables {J : Type v₁}

open opposite

/-- A discrete category is equivalent to its opposite category. -/
@[simps functor_obj_as inverse_obj]
protected def opposite (α : Type u₁) : (discrete α)ᵒᵖ ≌ discrete α :=
let F : discrete α ⥤ (discrete α)ᵒᵖ := discrete.functor (λ x, op (discrete.mk x)) in
begin
  refine equivalence.mk (functor.left_op F) F _
    (discrete.nat_iso $ λ X, by { discrete_cases, simp [F] }),
  refine nat_iso.of_components (λ X, by { tactic.op_induction', discrete_cases, simp [F], }) _,
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

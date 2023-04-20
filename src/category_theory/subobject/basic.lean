/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Scott Morrison
-/
import category_theory.subobject.mono_over
import category_theory.skeletal
import category_theory.concrete_category.basic
import tactic.apply_fun
import tactic.elementwise

/-!
# Subobjects

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `subobject X` as the quotient (by isomorphisms) of
`mono_over X := {f : over X // mono f.hom}`.

Here `mono_over X` is a thin category (a pair of objects has at most one morphism between them),
so we can think of it as a preorder. However as it is not skeletal, it is not a partial order.

There is a coercion from `subobject X` back to the ambient category `C`
(using choice to pick a representative), and for `P : subobject X`,
`P.arrow : (P : C) ⟶ X` is the inclusion morphism.

We provide
* `def pullback [has_pullbacks C] (f : X ⟶ Y) : subobject Y ⥤ subobject X`
* `def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y`
* `def «exists» [has_images C] (f : X ⟶ Y) : subobject X ⥤ subobject Y`
and prove their basic properties and relationships.
These are all easy consequences of the earlier development
of the corresponding functors for `mono_over`.

The subobjects of `X` form a preorder making them into a category. We have `X ≤ Y` if and only if
`X.arrow` factors through `Y.arrow`: see `of_le`/`of_le_mk`/`of_mk_le`/`of_mk_le_mk` and
`le_of_comm`. Similarly, to show that two subobjects are equal, we can supply an isomorphism between
the underlying objects that commutes with the arrows (`eq_of_comm`).

See also

* `category_theory.subobject.factor_thru` :
  an API describing factorization of morphisms through subobjects.
* `category_theory.subobject.lattice` :
  the lattice structures on subobjects.

## Notes

This development originally appeared in Bhavik Mehta's "Topos theory for Lean" repository,
and was ported to mathlib by Scott Morrison.

### Implementation note

Currently we describe `pullback`, `map`, etc., as functors.
It may be better to just say that they are monotone functions,
and even avoid using categorical language entirely when describing `subobject X`.
(It's worth keeping this in mind in future use; it should be a relatively easy change here
if it looks preferable.)

### Relation to pseudoelements

There is a separate development of pseudoelements in `category_theory.abelian.pseudoelements`,
as a quotient (but not by isomorphism) of `over X`.

When a morphism `f` has an image, the image represents the same pseudoelement.
In a category with images `pseudoelements X` could be constructed as a quotient of `mono_over X`.
In fact, in an abelian category (I'm not sure in what generality beyond that),
`pseudoelements X` agrees with `subobject X`, but we haven't developed this in mathlib yet.

-/

universes v₁ v₂ u₁ u₂

noncomputable theory
namespace category_theory

open category_theory category_theory.category category_theory.limits

variables {C : Type u₁} [category.{v₁} C] {X Y Z : C}
variables {D : Type u₂} [category.{v₂} D]

/-!
We now construct the subobject lattice for `X : C`,
as the quotient by isomorphisms of `mono_over X`.

Since `mono_over X` is a thin category, we use `thin_skeleton` to take the quotient.

Essentially all the structure defined above on `mono_over X` descends to `subobject X`,
with morphisms becoming inequalities, and isomorphisms becoming equations.
-/

/--
The category of subobjects of `X : C`, defined as isomorphism classes of monomorphisms into `X`.
-/
@[derive [partial_order, category]]
def subobject (X : C) := thin_skeleton (mono_over X)

namespace subobject

/-- Convenience constructor for a subobject. -/
abbreviation mk {X A : C} (f : A ⟶ X) [mono f] : subobject X :=
(to_thin_skeleton _).obj (mono_over.mk' f)

section
local attribute [ext] category_theory.comma

protected lemma ind {X : C} (p : subobject X → Prop)
  (h : ∀ ⦃A : C⦄ (f : A ⟶ X) [mono f], by exactI p (subobject.mk f)) (P : subobject X) : p P :=
begin
  apply quotient.induction_on',
  intro a,
  convert h a.arrow,
  ext; refl
end

protected lemma ind₂ {X : C} (p : subobject X → subobject X → Prop)
  (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [mono f] [mono g],
    by exactI p (subobject.mk f) (subobject.mk g)) (P Q : subobject X) : p P Q :=
begin
  apply quotient.induction_on₂',
  intros a b,
  convert h a.arrow b.arrow;
  ext; refl
end

end

/-- Declare a function on subobjects of `X` by specifying a function on monomorphisms with
    codomain `X`. -/
protected def lift {α : Sort*} {X : C} (F : Π ⦃A : C⦄ (f : A ⟶ X) [mono f], α)
  (h : ∀ ⦃A B : C⦄ (f : A ⟶ X) (g : B ⟶ X) [mono f] [mono g] (i : A ≅ B),
    i.hom ≫ g = f → by exactI F f = F g) : subobject X → α :=
λ P, quotient.lift_on' P (λ m, by exactI F m.arrow) $ λ m n ⟨i⟩,
  h m.arrow n.arrow ((mono_over.forget X ⋙ over.forget X).map_iso i) (over.w i.hom)

@[simp]
protected lemma lift_mk {α : Sort*} {X : C} (F : Π ⦃A : C⦄ (f : A ⟶ X) [mono f], α) {h A}
  (f : A ⟶ X) [mono f] : subobject.lift F h (subobject.mk f) = F f :=
rfl

/-- The category of subobjects is equivalent to the `mono_over` category. It is more convenient to
use the former due to the partial order instance, but oftentimes it is easier to define structures
on the latter. -/
noncomputable def equiv_mono_over (X : C) : subobject X ≌ mono_over X :=
thin_skeleton.equivalence _

/--
Use choice to pick a representative `mono_over X` for each `subobject X`.
-/
noncomputable
def representative {X : C} : subobject X ⥤ mono_over X :=
(equiv_mono_over X).functor

/--
Starting with `A : mono_over X`, we can take its equivalence class in `subobject X`
then pick an arbitrary representative using `representative.obj`.
This is isomorphic (in `mono_over X`) to the original `A`.
-/
noncomputable
def representative_iso {X : C} (A : mono_over X) :
  representative.obj ((to_thin_skeleton _).obj A) ≅ A :=
(equiv_mono_over X).counit_iso.app A

/--
Use choice to pick a representative underlying object in `C` for any `subobject X`.

Prefer to use the coercion `P : C` rather than explicitly writing `underlying.obj P`.
-/
noncomputable
def underlying {X : C} : subobject X ⥤ C :=
representative ⋙ mono_over.forget _ ⋙ over.forget _

instance : has_coe (subobject X) C :=
{ coe := λ Y, underlying.obj Y, }

@[simp] lemma underlying_as_coe {X : C} (P : subobject X) : underlying.obj P = P := rfl

/--
If we construct a `subobject Y` from an explicit `f : X ⟶ Y` with `[mono f]`,
then pick an arbitrary choice of underlying object `(subobject.mk f : C)` back in `C`,
it is isomorphic (in `C`) to the original `X`.
-/
noncomputable
def underlying_iso {X Y : C} (f : X ⟶ Y) [mono f] : (subobject.mk f : C) ≅ X :=
(mono_over.forget _ ⋙ over.forget _).map_iso (representative_iso (mono_over.mk' f))

/--
The morphism in `C` from the arbitrarily chosen underlying object to the ambient object.
-/
noncomputable
def arrow {X : C} (Y : subobject X) : (Y : C) ⟶ X :=
(representative.obj Y).obj.hom

instance arrow_mono {X : C} (Y : subobject X) : mono (Y.arrow) :=
(representative.obj Y).property

@[simp]
lemma arrow_congr {A : C} (X Y : subobject A) (h : X = Y) :
  eq_to_hom (congr_arg (λ X : subobject A, (X : C)) h) ≫ Y.arrow = X.arrow :=
by { induction h, simp, }

@[simp]
lemma representative_coe (Y : subobject X) :
  (representative.obj Y : C) = (Y : C) :=
rfl

@[simp]
lemma representative_arrow (Y : subobject X) :
  (representative.obj Y).arrow = Y.arrow :=
rfl

@[simp, reassoc]
lemma underlying_arrow {X : C} {Y Z : subobject X} (f : Y ⟶ Z) :
  underlying.map f ≫ arrow Z = arrow Y :=
over.w (representative.map f)

@[simp, reassoc, elementwise]
lemma underlying_iso_arrow {X Y : C} (f : X ⟶ Y) [mono f] :
  (underlying_iso f).inv ≫ (subobject.mk f).arrow = f :=
over.w _

@[simp, reassoc]
lemma underlying_iso_hom_comp_eq_mk {X Y : C} (f : X ⟶ Y) [mono f] :
  (underlying_iso f).hom ≫ f = (mk f).arrow :=
(iso.eq_inv_comp _).1 (underlying_iso_arrow f).symm

/-- Two morphisms into a subobject are equal exactly if
the morphisms into the ambient object are equal -/
@[ext]
lemma eq_of_comp_arrow_eq {X Y : C} {P : subobject Y}
  {f g : X ⟶ P} (h : f ≫ P.arrow = g ≫ P.arrow) : f = g :=
(cancel_mono P.arrow).mp h

lemma mk_le_mk_of_comm {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [mono f₁] [mono f₂] (g : A₁ ⟶ A₂)
  (w : g ≫ f₂ = f₁) : mk f₁ ≤ mk f₂ :=
⟨mono_over.hom_mk _ w⟩

@[simp] lemma mk_arrow (P : subobject X) : mk P.arrow = P :=
quotient.induction_on' P $ λ Q,
begin
  obtain ⟨e⟩ := @quotient.mk_out' _ (is_isomorphic_setoid _) Q,
  refine quotient.sound' ⟨mono_over.iso_mk _ _ ≪≫ e⟩;
  tidy
end

lemma le_of_comm {B : C} {X Y : subobject B} (f : (X : C) ⟶ (Y : C)) (w : f ≫ Y.arrow = X.arrow) :
  X ≤ Y :=
by convert mk_le_mk_of_comm _ w; simp

lemma le_mk_of_comm {B A : C} {X : subobject B} {f : A ⟶ B} [mono f] (g : (X : C) ⟶ A)
  (w : g ≫ f = X.arrow) : X ≤ mk f :=
le_of_comm (g ≫ (underlying_iso f).inv) $ by simp [w]

lemma mk_le_of_comm {B A : C} {X : subobject B} {f : A ⟶ B} [mono f] (g : A ⟶ (X : C))
  (w : g ≫ X.arrow = f) : mk f ≤ X :=
le_of_comm ((underlying_iso f).hom ≫ g) $ by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext] lemma eq_of_comm {B : C} {X Y : subobject B} (f : (X : C) ≅ (Y : C))
  (w : f.hom ≫ Y.arrow = X.arrow) : X = Y :=
le_antisymm (le_of_comm f.hom w) $ le_of_comm f.inv $ f.inv_comp_eq.2 w.symm

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext] lemma eq_mk_of_comm {B A : C} {X : subobject B} (f : A ⟶ B) [mono f] (i : (X : C) ≅ A)
  (w : i.hom ≫ f = X.arrow) : X = mk f :=
eq_of_comm (i.trans (underlying_iso f).symm) $ by simp [w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext] lemma mk_eq_of_comm {B A : C} {X : subobject B} (f : A ⟶ B) [mono f] (i : A ≅ (X : C))
  (w : i.hom ≫ X.arrow = f) : mk f = X :=
eq.symm $ eq_mk_of_comm _ i.symm $ by rw [iso.symm_hom, iso.inv_comp_eq, w]

/-- To show that two subobjects are equal, it suffices to exhibit an isomorphism commuting with
    the arrows. -/
@[ext] lemma mk_eq_mk_of_comm {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [mono f] [mono g]
  (i : A₁ ≅ A₂) (w : i.hom ≫ g = f) : mk f = mk g :=
eq_mk_of_comm _ ((underlying_iso f).trans i) $ by simp [w]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
-- We make `X` and `Y` explicit arguments here so that when `of_le` appears in goal statements
-- it is possible to see its source and target
-- (`h` will just display as `_`, because it is in `Prop`).
def of_le {B : C} (X Y : subobject B) (h : X ≤ Y) : (X : C) ⟶ (Y : C) :=
underlying.map $ h.hom

@[simp, reassoc] lemma of_le_arrow {B : C} {X Y : subobject B} (h : X ≤ Y) :
  of_le X Y h ≫ Y.arrow = X.arrow :=
underlying_arrow _

instance {B : C} (X Y : subobject B) (h : X ≤ Y) : mono (of_le X Y h) :=
begin
  fsplit,
  intros Z f g w,
  replace w := w =≫ Y.arrow,
  ext,
  simpa using w,
end

lemma of_le_mk_le_mk_of_comm
  {B A₁ A₂ : C} {f₁ : A₁ ⟶ B} {f₂ : A₂ ⟶ B} [mono f₁] [mono f₂] (g : A₁ ⟶ A₂) (w : g ≫ f₂ = f₁) :
  of_le _ _ (mk_le_mk_of_comm g w) = (underlying_iso _).hom ≫ g ≫ (underlying_iso _).inv :=
by { ext, simp [w], }

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
@[derive mono]
def of_le_mk {B A : C} (X : subobject B) (f : A ⟶ B) [mono f] (h : X ≤ mk f) : (X : C) ⟶ A :=
of_le X (mk f) h ≫ (underlying_iso f).hom

@[simp] lemma of_le_mk_comp {B A : C} {X : subobject B} {f : A ⟶ B} [mono f] (h : X ≤ mk f) :
  of_le_mk X f h ≫ f = X.arrow :=
by simp [of_le_mk]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
@[derive mono]
def of_mk_le {B A : C} (f : A ⟶ B) [mono f] (X : subobject B) (h : mk f ≤ X) : A ⟶ (X : C) :=
(underlying_iso f).inv ≫ of_le (mk f) X h

@[simp] lemma of_mk_le_arrow {B A : C} {f : A ⟶ B} [mono f] {X : subobject B} (h : mk f ≤ X) :
  of_mk_le f X h ≫ X.arrow = f :=
by simp [of_mk_le]

/-- An inequality of subobjects is witnessed by some morphism between the corresponding objects. -/
@[derive mono]
def of_mk_le_mk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [mono f] [mono g] (h : mk f ≤ mk g) :
  A₁ ⟶ A₂ :=
(underlying_iso f).inv ≫ of_le (mk f) (mk g) h ≫ (underlying_iso g).hom

@[simp] lemma of_mk_le_mk_comp {B A₁ A₂ : C} {f : A₁ ⟶ B} {g : A₂ ⟶ B} [mono f] [mono g]
  (h : mk f ≤ mk g) : of_mk_le_mk f g h ≫ g = f :=
by simp [of_mk_le_mk]

@[simp, reassoc] lemma of_le_comp_of_le {B : C} (X Y Z : subobject B) (h₁ : X ≤ Y) (h₂ : Y ≤ Z) :
  of_le X Y h₁ ≫ of_le Y Z h₂ = of_le X Z (h₁.trans h₂) :=
by simp [of_le, ←functor.map_comp underlying]

@[simp, reassoc] lemma of_le_comp_of_le_mk {B A : C} (X Y : subobject B) (f : A ⟶ B) [mono f]
  (h₁ : X ≤ Y) (h₂ : Y ≤ mk f) : of_le X Y h₁ ≫ of_le_mk Y f h₂ = of_le_mk X f (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, ←functor.map_comp_assoc underlying]

@[simp, reassoc] lemma of_le_mk_comp_of_mk_le {B A : C} (X : subobject B) (f : A ⟶ B) [mono f]
  (Y : subobject B) (h₁ : X ≤ mk f) (h₂ : mk f ≤ Y) :
  of_le_mk X f h₁ ≫ of_mk_le f Y h₂ = of_le X Y (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, ←functor.map_comp underlying]

@[simp, reassoc] lemma of_le_mk_comp_of_mk_le_mk {B A₁ A₂ : C} (X : subobject B) (f : A₁ ⟶ B)
  [mono f] (g : A₂ ⟶ B) [mono g] (h₁ : X ≤ mk f) (h₂ : mk f ≤ mk g) :
  of_le_mk X f h₁ ≫ of_mk_le_mk f g h₂ = of_le_mk X g (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, of_mk_le_mk, ←functor.map_comp_assoc underlying]

@[simp, reassoc] lemma of_mk_le_comp_of_le {B A₁ : C} (f : A₁ ⟶ B) [mono f] (X Y : subobject B)
  (h₁ : mk f ≤ X) (h₂ : X ≤ Y) :
  of_mk_le f X h₁ ≫ of_le X Y h₂ = of_mk_le f Y (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, of_mk_le_mk, ←functor.map_comp underlying]

@[simp, reassoc] lemma of_mk_le_comp_of_le_mk {B A₁ A₂ : C} (f : A₁ ⟶ B) [mono f] (X : subobject B)
  (g : A₂ ⟶ B) [mono g] (h₁ : mk f ≤ X) (h₂ : X ≤ mk g) :
  of_mk_le f X h₁ ≫ of_le_mk X g h₂ = of_mk_le_mk f g (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, of_mk_le_mk, ←functor.map_comp_assoc underlying]

@[simp, reassoc] lemma of_mk_le_mk_comp_of_mk_le {B A₁ A₂ : C} (f : A₁ ⟶ B) [mono f] (g : A₂ ⟶ B)
  [mono g] (X : subobject B) (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ X) :
  of_mk_le_mk f g h₁ ≫ of_mk_le g X h₂ = of_mk_le f X (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, of_mk_le_mk, ←functor.map_comp underlying]

@[simp, reassoc] lemma of_mk_le_mk_comp_of_mk_le_mk {B A₁ A₂ A₃ : C} (f : A₁ ⟶ B) [mono f]
  (g : A₂ ⟶ B) [mono g] (h : A₃ ⟶ B) [mono h] (h₁ : mk f ≤ mk g) (h₂ : mk g ≤ mk h) :
  of_mk_le_mk f g h₁ ≫ of_mk_le_mk g h h₂ = of_mk_le_mk f h (h₁.trans h₂) :=
by simp [of_mk_le, of_le_mk, of_le, of_mk_le_mk, ←functor.map_comp_assoc underlying]

@[simp] lemma of_le_refl {B : C} (X : subobject B) :
  of_le X X le_rfl = 𝟙 _ :=
by { apply (cancel_mono X.arrow).mp, simp }

@[simp] lemma of_mk_le_mk_refl {B A₁ : C} (f : A₁ ⟶ B) [mono f] :
  of_mk_le_mk f f le_rfl = 𝟙 _ :=
by { apply (cancel_mono f).mp, simp }

/-- An equality of subobjects gives an isomorphism of the corresponding objects.
(One could use `underlying.map_iso (eq_to_iso h))` here, but this is more readable.) -/
-- As with `of_le`, we have `X` and `Y` as explicit arguments for readability.
@[simps]
def iso_of_eq {B : C} (X Y : subobject B) (h : X = Y) : (X : C) ≅ (Y : C) :=
{ hom := of_le _ _ h.le,
  inv := of_le _ _ h.ge, }

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def iso_of_eq_mk {B A : C} (X : subobject B) (f : A ⟶ B) [mono f] (h : X = mk f) : (X : C) ≅ A :=
{ hom := of_le_mk X f h.le,
  inv := of_mk_le f X h.ge }

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def iso_of_mk_eq {B A : C} (f : A ⟶ B) [mono f] (X : subobject B) (h : mk f = X) : A ≅ (X : C) :=
{ hom := of_mk_le f X h.le,
  inv := of_le_mk X f h.ge, }

/-- An equality of subobjects gives an isomorphism of the corresponding objects. -/
@[simps]
def iso_of_mk_eq_mk {B A₁ A₂ : C} (f : A₁ ⟶ B) (g : A₂ ⟶ B) [mono f] [mono g] (h : mk f = mk g) :
  A₁ ≅ A₂ :=
{ hom := of_mk_le_mk f g h.le,
  inv := of_mk_le_mk g f h.ge, }

end subobject


open category_theory.limits

namespace subobject

/-- Any functor `mono_over X ⥤ mono_over Y` descends to a functor
`subobject X ⥤ subobject Y`, because `mono_over Y` is thin. -/
def lower {Y : D} (F : mono_over X ⥤ mono_over Y) : subobject X ⥤ subobject Y :=
thin_skeleton.map F

/-- Isomorphic functors become equal when lowered to `subobject`.
(It's not as evil as usual to talk about equality between functors
because the categories are thin and skeletal.) -/
lemma lower_iso (F₁ F₂ : mono_over X ⥤ mono_over Y) (h : F₁ ≅ F₂) :
  lower F₁ = lower F₂ :=
thin_skeleton.map_iso_eq h

/-- A ternary version of `subobject.lower`. -/
def lower₂ (F : mono_over X ⥤ mono_over Y ⥤ mono_over Z) :
  subobject X ⥤ subobject Y ⥤ subobject Z :=
thin_skeleton.map₂ F

@[simp]
lemma lower_comm (F : mono_over Y ⥤ mono_over X) :
  to_thin_skeleton _ ⋙ lower F = F ⋙ to_thin_skeleton _ :=
rfl

/-- An adjunction between `mono_over A` and `mono_over B` gives an adjunction
between `subobject A` and `subobject B`. -/
def lower_adjunction {A : C} {B : D}
  {L : mono_over A ⥤ mono_over B} {R : mono_over B ⥤ mono_over A} (h : L ⊣ R) :
  lower L ⊣ lower R :=
thin_skeleton.lower_adjunction _ _ h

/-- An equivalence between `mono_over A` and `mono_over B` gives an equivalence
between `subobject A` and `subobject B`. -/
@[simps]
def lower_equivalence {A : C} {B : D} (e : mono_over A ≌ mono_over B) : subobject A ≌ subobject B :=
{ functor := lower e.functor,
  inverse := lower e.inverse,
  unit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.unit_iso,
    { exact thin_skeleton.map_id_eq.symm },
    { exact (thin_skeleton.map_comp_eq _ _).symm },
  end,
  counit_iso :=
  begin
    apply eq_to_iso,
    convert thin_skeleton.map_iso_eq e.counit_iso,
    { exact (thin_skeleton.map_comp_eq _ _).symm },
    { exact thin_skeleton.map_id_eq.symm },
  end }

section pullback
variables [has_pullbacks C]

/-- When `C` has pullbacks, a morphism `f : X ⟶ Y` induces a functor `subobject Y ⥤ subobject X`,
by pulling back a monomorphism along `f`. -/
def pullback (f : X ⟶ Y) : subobject Y ⥤ subobject X :=
lower (mono_over.pullback f)

lemma pullback_id (x : subobject X) : (pullback (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.pullback_id.app f⟩,
end

lemma pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : subobject Z) :
  (pullback (f ≫ g)).obj x = (pullback f).obj ((pullback g).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.pullback_comp _ _).app t⟩,
end

instance (f : X ⟶ Y) : faithful (pullback f) := {}

end pullback

section map

/--
We can map subobjects of `X` to subobjects of `Y`
by post-composition with a monomorphism `f : X ⟶ Y`.
-/
def map (f : X ⟶ Y) [mono f] : subobject X ⥤ subobject Y :=
lower (mono_over.map f)

lemma map_id (x : subobject X) : (map (𝟙 X)).obj x = x :=
begin
  apply quotient.induction_on' x,
  intro f,
  apply quotient.sound,
  exact ⟨mono_over.map_id.app f⟩,
end

lemma map_comp (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [mono g] (x : subobject X) :
  (map (f ≫ g)).obj x = (map g).obj ((map f).obj x) :=
begin
  apply quotient.induction_on' x,
  intro t,
  apply quotient.sound,
  refine ⟨(mono_over.map_comp _ _).app t⟩,
end

/-- Isomorphic objects have equivalent subobject lattices. -/
def map_iso {A B : C} (e : A ≅ B) : subobject A ≌ subobject B :=
lower_equivalence (mono_over.map_iso e)

/-- In fact, there's a type level bijection between the subobjects of isomorphic objects,
which preserves the order. -/
-- @[simps] here generates a lemma `map_iso_to_order_iso_to_equiv_symm_apply`
-- whose left hand side is not in simp normal form.
def map_iso_to_order_iso (e : X ≅ Y) : subobject X ≃o subobject Y :=
{ to_fun := (map e.hom).obj,
  inv_fun := (map e.inv).obj,
  left_inv := λ g, by simp_rw [← map_comp, e.hom_inv_id, map_id],
  right_inv := λ g, by simp_rw [← map_comp, e.inv_hom_id, map_id],
  map_rel_iff' := λ A B, begin
    dsimp, fsplit,
    { intro h,
      apply_fun (map e.inv).obj at h,
      simp_rw [← map_comp, e.hom_inv_id, map_id] at h,
      exact h, },
    { intro h,
      apply_fun (map e.hom).obj at h,
      exact h, },
  end }

@[simp] lemma map_iso_to_order_iso_apply (e : X ≅ Y) (P : subobject X) :
  map_iso_to_order_iso e P = (map e.hom).obj P :=
rfl

@[simp] lemma map_iso_to_order_iso_symm_apply (e : X ≅ Y) (Q : subobject Y) :
  (map_iso_to_order_iso e).symm Q = (map e.inv).obj Q :=
rfl

/-- `map f : subobject X ⥤ subobject Y` is
the left adjoint of `pullback f : subobject Y ⥤ subobject X`. -/
def map_pullback_adj [has_pullbacks C] (f : X ⟶ Y) [mono f] : map f ⊣ pullback f :=
lower_adjunction (mono_over.map_pullback_adj f)

@[simp]
lemma pullback_map_self [has_pullbacks C] (f : X ⟶ Y) [mono f] (g : subobject X) :
  (pullback f).obj ((map f).obj g) = g :=
begin
  revert g,
  apply quotient.ind,
  intro g',
  apply quotient.sound,
  exact ⟨(mono_over.pullback_map_self f).app _⟩,
end

lemma map_pullback [has_pullbacks C]
  {X Y Z W : C} {f : X ⟶ Y} {g : X ⟶ Z} {h : Y ⟶ W} {k : Z ⟶ W} [mono h] [mono g]
  (comm : f ≫ h = g ≫ k) (t : is_limit (pullback_cone.mk f g comm)) (p : subobject Y) :
  (map g).obj ((pullback f).obj p) = (pullback k).obj ((map h).obj p) :=
begin
  revert p,
  apply quotient.ind',
  intro a,
  apply quotient.sound,
  apply thin_skeleton.equiv_of_both_ways,
  { refine mono_over.hom_mk (pullback.lift pullback.fst _ _) (pullback.lift_snd _ _ _),
    change _ ≫ a.arrow ≫ h = (pullback.snd ≫ g) ≫ _,
    rw [assoc, ← comm, pullback.condition_assoc] },
  { refine mono_over.hom_mk (pullback.lift pullback.fst
                        (pullback_cone.is_limit.lift' t (pullback.fst ≫ a.arrow) pullback.snd _).1
                        (pullback_cone.is_limit.lift' _ _ _ _).2.1.symm) _,
    { rw [← pullback.condition, assoc], refl },
    { dsimp, rw [pullback.lift_snd_assoc],
      apply (pullback_cone.is_limit.lift' _ _ _ _).2.2 } }
end

end map

section «exists»
variables [has_images C]

/--
The functor from subobjects of `X` to subobjects of `Y` given by
sending the subobject `S` to its "image" under `f`, usually denoted $\exists_f$.
For instance, when `C` is the category of types,
viewing `subobject X` as `set X` this is just `set.image f`.

This functor is left adjoint to the `pullback f` functor (shown in `exists_pullback_adj`)
provided both are defined, and generalises the `map f` functor, again provided it is defined.
-/
def «exists» (f : X ⟶ Y) : subobject X ⥤ subobject Y :=
lower (mono_over.exists f)

/--
When `f : X ⟶ Y` is a monomorphism, `exists f` agrees with `map f`.
-/
lemma exists_iso_map (f : X ⟶ Y) [mono f] : «exists» f = map f :=
lower_iso _ _ (mono_over.exists_iso_map f)

/--
`exists f : subobject X ⥤ subobject Y` is
left adjoint to `pullback f : subobject Y ⥤ subobject X`.
-/
def exists_pullback_adj (f : X ⟶ Y) [has_pullbacks C] : «exists» f ⊣ pullback f :=
lower_adjunction (mono_over.exists_pullback_adj f)

end  «exists»

end subobject

end category_theory

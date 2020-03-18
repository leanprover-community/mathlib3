/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.terminal
import category_theory.limits.shapes.binary_products
import category_theory.epi_mono

/-!
# Zero morphisms and zero objects

A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. (Notice this is extra
structure, not merely a property.)

A category "has a zero object" if it has an object which is both initial and terminal. Having a
zero object provides zero morphisms, as the unique morphisms factoring through the zero object.

## References

* https://en.wikipedia.org/wiki/Zero_morphism
* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/

universes v u

open category_theory

namespace category_theory.limits

variables (C : Type u) [𝒞 : category.{v} C]
include 𝒞

/-- A category "has zero morphisms" if there is a designated "zero morphism" in each morphism space,
and compositions of zero morphisms with anything give the zero morphism. -/
class has_zero_morphisms :=
[has_zero : Π X Y : C, has_zero (X ⟶ Y)]
(comp_zero' : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z) . obviously)
(zero_comp' : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z) . obviously)

attribute [instance] has_zero_morphisms.has_zero
restate_axiom has_zero_morphisms.comp_zero'
attribute [simp] has_zero_morphisms.comp_zero
restate_axiom has_zero_morphisms.zero_comp'
attribute [simp, reassoc] has_zero_morphisms.zero_comp

section
variables {C} [has_zero_morphisms.{v} C]

lemma zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←has_zero_morphisms.zero_comp.{v} C X g, cancel_mono] at h, exact h }

lemma zero_of_comp_epi {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [epi f] (h : f ≫ g = 0) : g = 0 :=
by { rw [←has_zero_morphisms.comp_zero.{v} C f Z, cancel_epi] at h, exact h }

end

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object :=
(zero : C)
(unique_to : Π X : C, unique (zero ⟶ X))
(unique_from : Π X : C, unique (X ⟶ zero))

variables {C}

namespace has_zero_object

variables [has_zero_object.{v} C]

/--
Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def has_zero : has_zero C :=
{ zero := has_zero_object.zero.{v} C }

local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.unique_to has_zero_object.unique_from

/-- A category with a zero object has zero morphisms.

    It is rarely a good idea to use this. Many categories that have a zero object have zero
    morphisms for some other reason, for example from additivity. Library code that uses
    `zero_morphisms_of_zero_object` will then be incompatible with these categories because
    the `has_zero_morphisms` instances will not be definitionally equal. For this reason library
    code should generally ask for an instance of `has_zero_morphisms` separately, even if it already
    asks for an instance of `has_zero_objects`. -/
def zero_morphisms_of_zero_object : has_zero_morphisms.{v} C :=
{ has_zero := λ X Y,
  { zero := inhabited.default (X ⟶ 0) ≫ inhabited.default (0 ⟶ Y) },
  zero_comp' := λ X Y Z f, by { dunfold has_zero.zero, rw category.assoc, congr, },
  comp_zero' := λ X Y Z f, by { dunfold has_zero.zero, rw ←category.assoc, congr, }}

section
variable [has_zero_morphisms.{v} C]

/--  An arrow ending in the zero object is zero -/
lemma zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 :=
begin
  rw (has_zero_object.unique_from.{v} X).uniq f,
  rw (has_zero_object.unique_from.{v} X).uniq (0 : X ⟶ 0)
end

/-- An arrow starting at the zero object is zero -/
lemma zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 :=
begin
  rw (has_zero_object.unique_to.{v} X).uniq f,
  rw (has_zero_object.unique_to.{v} X).uniq (0 : 0 ⟶ X)
end

end

/-- A zero object is in particular initial. -/
def has_initial_of_has_zero_object : has_initial.{v} C :=
has_initial_of_unique 0
/-- A zero object is in particular terminal. -/
def has_terminal_of_has_zero_object : has_terminal.{v} C :=
has_terminal_of_unique 0

end has_zero_object

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_sigma_ι
  {β : Type v} [decidable_eq β]
  [has_zero_morphisms.{v} C]
  (f : β → C) [has_colimit (functor.of_function f)] (b : β) : split_mono (sigma.ι f b) :=
{ retraction := sigma.desc (λ b', if h : b' = b then eq_to_hom (congr_arg f h) else 0), }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_pi_π
  {β : Type v} [decidable_eq β]
  [has_zero_morphisms.{v} C]
  (f : β → C) [has_limit (functor.of_function f)] (b : β) : split_epi (pi.π f b) :=
{ section_ := pi.lift (λ b', if h : b = b' then eq_to_hom (congr_arg f h) else 0), }

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_coprod_inl
  [has_zero_morphisms.{v} C] {X Y : C} [has_colimit (pair X Y)] :
  split_mono (coprod.inl : X ⟶ X ⨿ Y) :=
{ retraction := coprod.desc (𝟙 X) 0, }
/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_coprod_inr
  [has_zero_morphisms.{v} C] {X Y : C} [has_colimit (pair X Y)] :
  split_mono (coprod.inr : Y ⟶ X ⨿ Y) :=
{ retraction := coprod.desc 0 (𝟙 Y), }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_prod_fst
  [has_zero_morphisms.{v} C] {X Y : C} [has_limit (pair X Y)] :
  split_epi (prod.fst : X ⨯ Y ⟶ X) :=
{ section_ := prod.lift (𝟙 X) 0, }
/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_prod_snd
  [has_zero_morphisms.{v} C] {X Y : C} [has_limit (pair X Y)] :
  split_epi (prod.snd : X ⨯ Y ⟶ Y) :=
{ section_ := prod.lift 0 (𝟙 Y), }

end category_theory.limits

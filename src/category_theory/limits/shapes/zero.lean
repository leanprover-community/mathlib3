/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.limits.shapes.binary_products
import category_theory.limits.shapes.images
import category_theory.epi_mono
import category_theory.punit
import category_theory.discrete_category

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

variables (C : Type u) [category.{v} C]

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

instance has_zero_morphisms_pempty : has_zero_morphisms.{v} (discrete pempty.{v+1}) :=
{ has_zero := by tidy }

instance has_zero_morphisms_punit : has_zero_morphisms.{v} (discrete punit.{v+1}) :=
{ has_zero := by tidy }

namespace has_zero_morphisms
variables {C}

/-- This lemma will be immediately superseded by `ext`, below. -/
private lemma ext_aux (I J : has_zero_morphisms.{v} C)
  (w : ∀ X Y : C, (@has_zero_morphisms.has_zero.{v} _ _ I X Y).zero = (@has_zero_morphisms.has_zero.{v} _ _ J X Y).zero) : I = J :=
begin
  casesI I, casesI J,
  congr,
  { ext X Y,
    exact w X Y },
  { apply proof_irrel_heq, },
  { apply proof_irrel_heq, }
end

/--
If you're tempted to use this lemma "in the wild", you should probably
carefully consider whether you've made a mistake in allowing two
instances of `has_zero_morphisms` to exist at all.

See, particularly, the note on `zero_morphisms_of_zero_object` below.
-/
lemma ext (I J : has_zero_morphisms.{v} C) : I = J :=
begin
  apply ext_aux,
  intros X Y,
  rw ←@has_zero_morphisms.comp_zero _ _ I X X (@has_zero_morphisms.has_zero _ _ J X X).zero,
  rw @has_zero_morphisms.zero_comp _ _ J,
end

instance : subsingleton (has_zero_morphisms.{v} C) :=
⟨ext⟩

end has_zero_morphisms

open has_zero_morphisms

section
variables {C} [has_zero_morphisms.{v} C]

lemma zero_of_comp_mono {X Y Z : C} {f : X ⟶ Y} (g : Y ⟶ Z) [mono g] (h : f ≫ g = 0) : f = 0 :=
by { rw [←zero_comp.{v} X g, cancel_mono] at h, exact h }

lemma zero_of_epi_comp {X Y Z : C} (f : X ⟶ Y) {g : Y ⟶ Z} [epi f] (h : f ≫ g = 0) : g = 0 :=
by { rw [←comp_zero.{v} f Z, cancel_epi] at h, exact h }

lemma eq_zero_of_image_eq_zero {X Y : C} {f : X ⟶ Y} [has_image f] (w : image.ι f = 0) : f = 0 :=
by rw [←image.fac f, w, has_zero_morphisms.comp_zero]

lemma nonzero_image_of_nonzero {X Y : C} {f : X ⟶ Y} [has_image f] (w : f ≠ 0) : image.ι f ≠ 0 :=
λ h, w (eq_zero_of_image_eq_zero h)
end

section
universes v' u'
variables (D : Type u') [category.{v'} D]

variables [has_zero_morphisms.{v} C] [has_zero_morphisms.{v'} D]

@[simp] lemma equivalence_preserves_zero_morphisms (F : C ≌ D) (X Y : C) :
  F.functor.map (0 : X ⟶ Y) = (0 : F.functor.obj X ⟶ F.functor.obj Y) :=
begin
  have t : F.functor.map (0 : X ⟶ Y) = F.functor.map (0 : X ⟶ Y) ≫ (0 : F.functor.obj Y ⟶ F.functor.obj Y),
  { apply faithful.map_injective (F.inverse),
    rw [functor.map_comp, equivalence.inv_fun_map],
    dsimp,
    rw [zero_comp, comp_zero, zero_comp], },
  exact t.trans (by simp)
end

end

/-- A category "has a zero object" if it has an object which is both initial and terminal. -/
class has_zero_object :=
(zero : C)
(unique_to : Π X : C, unique (zero ⟶ X))
(unique_from : Π X : C, unique (X ⟶ zero))

instance has_zero_object_punit : has_zero_object.{v} (discrete punit.{v+1}) :=
{ zero := punit.star,
  unique_to := by tidy,
  unique_from := by tidy, }

variables {C}

namespace has_zero_object

variables [has_zero_object.{v} C]

/--
Construct a `has_zero C` for a category with a zero object.
This can not be a global instance as it will trigger for every `has_zero C` typeclass search.
-/
protected def has_zero : has_zero C :=
{ zero := has_zero_object.zero.{v} }

local attribute [instance] has_zero_object.has_zero
local attribute [instance] has_zero_object.unique_to has_zero_object.unique_from

@[ext]
lemma to_zero_ext {X : C} (f g : X ⟶ 0) : f = g :=
by rw [(has_zero_object.unique_from.{v} X).uniq f, (has_zero_object.unique_from.{v} X).uniq g]

@[ext]
lemma from_zero_ext {X : C} (f g : 0 ⟶ X) : f = g :=
by rw [(has_zero_object.unique_to.{v} X).uniq f, (has_zero_object.unique_to.{v} X).uniq g]

instance {X : C} (f : 0 ⟶ X) : mono f :=
{ right_cancellation := λ Z g h w, by ext, }

instance {X : C} (f : X ⟶ 0) : epi f :=
{ left_cancellation := λ Z g h w, by ext, }

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
-- This can't be a `simp` lemma because the left hand side would be a metavariable.
lemma zero_of_to_zero {X : C} (f : X ⟶ 0) : f = 0 :=
by ext

/-- An arrow starting at the zero object is zero -/
lemma zero_of_from_zero {X : C} (f : 0 ⟶ X) : f = 0 :=
by ext

end

/-- A zero object is in particular initial. -/
def has_initial : has_initial.{v} C :=
has_initial_of_unique 0
/-- A zero object is in particular terminal. -/
def has_terminal : has_terminal.{v} C :=
has_terminal_of_unique 0

end has_zero_object

/-- If there are zero morphisms, any initial object is a zero object. -/
@[priority 50]
instance has_zero_object_of_has_initial_object
  [has_zero_morphisms.{v} C] [has_initial.{v} C] : has_zero_object.{v} C :=
{ zero := ⊥_ C,
  unique_to := λ X, ⟨⟨0⟩, by tidy⟩,
  unique_from := λ X, ⟨⟨0⟩, λ f,
  calc
    f = f ≫ 𝟙 _ : (category.comp_id _).symm
    ... = f ≫ 0 : by congr
    ... = 0     : has_zero_morphisms.comp_zero _ _
  ⟩ }

/-- If there are zero morphisms, any terminal object is a zero object. -/
@[priority 50]
instance has_zero_object_of_has_terminal_object
  [has_zero_morphisms.{v} C] [has_terminal.{v} C] : has_zero_object.{v} C :=
{ zero := ⊤_ C,
  unique_from := λ X, ⟨⟨0⟩, by tidy⟩,
  unique_to := λ X, ⟨⟨0⟩, λ f,
  calc
    f = 𝟙 _ ≫ f : (category.id_comp _).symm
    ... = 0 ≫ f : by congr
    ... = 0     : has_zero_morphisms.zero_comp _ _
  ⟩ }

/-- In the presence of zero morphisms, coprojections into a coproduct are (split) monomorphisms. -/
instance split_mono_sigma_ι
  {β : Type v} [decidable_eq β]
  [has_zero_morphisms.{v} C]
  (f : β → C) [has_colimit (discrete.functor f)] (b : β) : split_mono (sigma.ι f b) :=
{ retraction := sigma.desc (λ b', if h : b' = b then eq_to_hom (congr_arg f h) else 0), }

/-- In the presence of zero morphisms, projections into a product are (split) epimorphisms. -/
instance split_epi_pi_π
  {β : Type v} [decidable_eq β]
  [has_zero_morphisms.{v} C]
  (f : β → C) [has_limit (discrete.functor f)] (b : β) : split_epi (pi.π f b) :=
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

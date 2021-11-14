/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.braided
import category_theory.monoidal.Mon_

/-!
# The category of commutative monoids in a braided monoidal category.
-/

universes v₁ v₂ u₁ u₂ u

open category_theory
open category_theory.monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C] [braided_category.{v₁} C]

/--
A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ extends Mon_ C :=
(mul_comm' : (β_ _ _).hom ≫ mul = mul . obviously)

restate_axiom CommMon_.mul_comm'
attribute [simp, reassoc] CommMon_.mul_comm

namespace CommMon_

/--
The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
@[simps]
def trivial : CommMon_ C :=
{ mul_comm' := begin dsimp, rw [braiding_left_unitor, unitors_equal], end
  ..Mon_.trivial C }

instance : inhabited (CommMon_ C) := ⟨trivial C⟩

variables {C} {M : CommMon_ C}

instance : category (CommMon_ C) :=
induced_category.category CommMon_.to_Mon_

@[simp] lemma id_hom (A : CommMon_ C) : Mon_.hom.hom (𝟙 A) = 𝟙 A.X := rfl
@[simp] lemma comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
  Mon_.hom.hom (f ≫ g) = f.hom ≫ g.hom := rfl

section
variables (C)

/-- The forgetful functor from commutative monoid objects to monoid objects. -/
@[derive [full, faithful]]
def forget₂_Mon_ : CommMon_ C ⥤ Mon_ C :=
induced_functor CommMon_.to_Mon_

@[simp] lemma forget₂_Mon_obj_one (A : CommMon_ C) : ((forget₂_Mon_ C).obj A).one = A.one := rfl
@[simp] lemma forget₂_Mon_obj_mul (A : CommMon_ C) : ((forget₂_Mon_ C).obj A).mul = A.mul := rfl
@[simp] lemma forget₂_Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) :
  ((forget₂_Mon_ C).map f).hom = f.hom := rfl

end

instance unique_hom_from_trivial (A : CommMon_ C) : unique (trivial C ⟶ A) :=
Mon_.unique_hom_from_trivial A.to_Mon_

open category_theory.limits

instance : has_initial (CommMon_ C) :=
has_initial_of_unique (trivial C)

end CommMon_

namespace category_theory.lax_braided_functor

variables {C} {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D] [braided_category.{v₂} D]

/--
A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps]
def map_CommMon (F : lax_braided_functor C D) : CommMon_ C ⥤ CommMon_ D :=
{ obj := λ A,
  { mul_comm' :=
    begin
      dsimp,
      have := F.braided,
      slice_lhs 1 2 { rw ←this, },
      slice_lhs 2 3 { rw [←category_theory.functor.map_comp, A.mul_comm], },
    end,
    ..F.to_lax_monoidal_functor.map_Mon.obj A.to_Mon_ },
  map := λ A B f, F.to_lax_monoidal_functor.map_Mon.map f, }

variables (C) (D)

/-- `map_CommMon` is functorial in the lax braided functor. -/
def map_CommMon_functor : (lax_braided_functor C D) ⥤ (CommMon_ C ⥤ CommMon_ D) :=
{ obj := map_CommMon,
  map := λ F G α,
  { app := λ A,
    { hom := α.app A.X, } } }

end category_theory.lax_braided_functor

namespace CommMon_

open category_theory.lax_braided_functor

namespace equiv_lax_braided_functor_punit

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def lax_braided_to_CommMon : lax_braided_functor (discrete punit.{u+1}) C ⥤ CommMon_ C :=
{ obj := λ F, (F.map_CommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (discrete punit)),
  map := λ F G α, ((map_CommMon_functor (discrete punit) C).map α).app _ }

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def CommMon_to_lax_braided : CommMon_ C ⥤ lax_braided_functor (discrete punit.{u+1}) C :=
{ obj := λ A,
  { obj := λ _, A.X,
    map := λ _ _ _, 𝟙 _,
    ε := A.one,
    μ := λ _ _, A.mul,
    map_id' := λ _, rfl,
    map_comp' := λ _ _ _ _ _, (category.id_comp (𝟙 A.X)).symm, },
  map := λ A B f,
  { app := λ _, f.hom,
    naturality' := λ _ _ _, by { dsimp, rw [category.id_comp, category.comp_id], },
    unit' := f.one_hom,
    tensor' := λ _ _, f.mul_hom, }, }

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def unit_iso :
  𝟭 (lax_braided_functor (discrete punit.{u+1}) C) ≅
    lax_braided_to_CommMon C ⋙ CommMon_to_lax_braided C :=
nat_iso.of_components (λ F, lax_braided_functor.mk_iso
  (monoidal_nat_iso.of_components
    (λ _, F.to_lax_monoidal_functor.to_functor.map_iso (eq_to_iso (by ext)))
    (by tidy) (by tidy) (by tidy)))
  (by tidy)

/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def counit_iso : CommMon_to_lax_braided C ⋙ lax_braided_to_CommMon C ≅ 𝟭 (CommMon_ C) :=
nat_iso.of_components (λ F, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, } })
  (by tidy)

end equiv_lax_braided_functor_punit

open equiv_lax_braided_functor_punit

/--
Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equiv_lax_braided_functor_punit : lax_braided_functor (discrete punit.{u+1}) C ≌ CommMon_ C :=
{ functor := lax_braided_to_CommMon C,
  inverse := CommMon_to_lax_braided C,
  unit_iso := unit_iso C,
  counit_iso := counit_iso C, }

end CommMon_

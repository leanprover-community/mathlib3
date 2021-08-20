/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.discrete
import category_theory.limits.shapes.terminal
import algebra.punit_instances

/-!
# The category of monoids in a monoidal category.
-/

universes v₁ v₂ u₁ u₂ u

open category_theory
open category_theory.monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

/--
A monoid object internal to a monoidal category.

When the monoidal category is preadditive, this is also sometimes called an "algebra object".
-/
structure Mon_ :=
(X : C)
(one : 𝟙_ C ⟶ X)
(mul : X ⊗ X ⟶ X)
(one_mul' : (one ⊗ 𝟙 X) ≫ mul = (λ_ X).hom . obviously)
(mul_one' : (𝟙 X ⊗ one) ≫ mul = (ρ_ X).hom . obviously)
-- Obviously there is some flexibility stating this axiom.
-- This one has left- and right-hand sides matching the statement of `monoid.mul_assoc`,
-- and chooses to place the associator on the right-hand side.
-- The heuristic is that unitors and associators "don't have much weight".
(mul_assoc' : (mul ⊗ 𝟙 X) ≫ mul = (α_ X X X).hom ≫ (𝟙 X ⊗ mul) ≫ mul . obviously)

restate_axiom Mon_.one_mul'
restate_axiom Mon_.mul_one'
restate_axiom Mon_.mul_assoc'
attribute [reassoc] Mon_.one_mul Mon_.mul_one -- We prove a more general `@[simp]` lemma below.
attribute [simp, reassoc] Mon_.mul_assoc

namespace Mon_

/--
The trivial monoid object. We later show this is initial in `Mon_ C`.
-/
@[simps]
def trivial : Mon_ C :=
{ X := 𝟙_ C,
  one := 𝟙 _,
  mul := (λ_ _).hom,
  mul_assoc' :=
    by simp_rw [triangle_assoc, iso.cancel_iso_hom_right, tensor_right_iff, unitors_equal],
  mul_one' := by simp [unitors_equal] }

instance : inhabited (Mon_ C) := ⟨trivial C⟩

variables {C} {M : Mon_ C}

@[simp] lemma one_mul_hom {Z : C} (f : Z ⟶ M.X) : (M.one ⊗ f) ≫ M.mul = (λ_ Z).hom ≫ f :=
by rw [←id_tensor_comp_tensor_id, category.assoc, M.one_mul, left_unitor_naturality]

@[simp] lemma mul_one_hom {Z : C} (f : Z ⟶ M.X) : (f ⊗ M.one) ≫ M.mul = (ρ_ Z).hom ≫ f :=
by rw [←tensor_id_comp_id_tensor, category.assoc, M.mul_one, right_unitor_naturality]

lemma assoc_flip : (𝟙 M.X ⊗ M.mul) ≫ M.mul = (α_ M.X M.X M.X).inv ≫ (M.mul ⊗ 𝟙 M.X) ≫ M.mul :=
by simp

/-- A morphism of monoid objects. -/
@[ext]
structure hom (M N : Mon_ C) :=
(hom : M.X ⟶ N.X)
(one_hom' : M.one ≫ hom = N.one . obviously)
(mul_hom' : M.mul ≫ hom = (hom ⊗ hom) ≫ N.mul . obviously)

restate_axiom hom.one_hom'
restate_axiom hom.mul_hom'
attribute [simp, reassoc] hom.one_hom hom.mul_hom

/-- The identity morphism on a monoid object. -/
@[simps]
def id (M : Mon_ C) : hom M M :=
{ hom := 𝟙 M.X, }

instance hom_inhabited (M : Mon_ C) : inhabited (hom M M) := ⟨id M⟩

/-- Composition of morphisms of monoid objects. -/
@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mon_ C) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

@[simp] lemma id_hom' (M : Mon_ C) : (𝟙 M : hom M M).hom = 𝟙 M.X := rfl
@[simp] lemma comp_hom' {M N K : Mon_ C} (f : M ⟶ N) (g : N ⟶ K) :
  (f ≫ g : hom M K).hom = f.hom ≫ g.hom := rfl

section
variables (C)

/-- The forgetful functor from monoid objects to the ambient category. -/
@[simps]
def forget : Mon_ C ⥤ C :=
{ obj := λ A, A.X,
  map := λ A B f, f.hom, }

end

instance forget_faithful : faithful (@forget C _ _) := { }

instance {A B : Mon_ C} (f : A ⟶ B) [e : is_iso ((forget C).map f)] : is_iso f.hom := e

/-- The forgetful functor from monoid objects to the ambient category reflects isomorphisms. -/
instance : reflects_isomorphisms (forget C) :=
{ reflects := λ X Y f e, by exactI ⟨⟨{
  hom := inv f.hom,
  mul_hom' :=
  begin
    simp only [is_iso.comp_inv_eq, hom.mul_hom, category.assoc, ←tensor_comp_assoc,
      is_iso.inv_hom_id, tensor_id, category.id_comp],
  end }, by tidy⟩⟩ }

instance unique_hom_from_trivial (A : Mon_ C) : unique (trivial C ⟶ A) :=
{ default :=
  { hom := A.one,
    one_hom' := by { dsimp, simp, },
    mul_hom' := by { dsimp, simp [A.one_mul, unitors_equal], } },
  uniq := λ f,
  begin
    ext, simp,
    rw [←category.id_comp f.hom],
    erw f.one_hom,
  end }

open category_theory.limits

instance : has_initial (Mon_ C) :=
has_initial_of_unique (trivial C)

end Mon_

namespace category_theory.lax_monoidal_functor

variables {C} {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

/--
A lax monoidal functor takes monoid objects to monoid objects.

That is, a lax monoidal functor `F : C ⥤ D` induces a functor `Mon_ C ⥤ Mon_ D`.
-/
-- TODO: map_Mod F A : Mod A ⥤ Mod (F.map_Mon A)
@[simps]
def map_Mon (F : lax_monoidal_functor C D) : Mon_ C ⥤ Mon_ D :=
{ obj := λ A,
  { X := F.obj A.X,
    one := F.ε ≫ F.map A.one,
    mul := F.μ _ _ ≫ F.map A.mul,
    one_mul' :=
    begin
      conv_lhs { rw [comp_tensor_id, ←F.to_functor.map_id], },
      slice_lhs 2 3 { rw [F.μ_natural], },
      slice_lhs 3 4 { rw [←F.to_functor.map_comp, A.one_mul], },
      rw [F.to_functor.map_id],
      rw [F.left_unitality],
    end,
    mul_one' :=
    begin
      conv_lhs { rw [id_tensor_comp, ←F.to_functor.map_id], },
      slice_lhs 2 3 { rw [F.μ_natural], },
      slice_lhs 3 4 { rw [←F.to_functor.map_comp, A.mul_one], },
      rw [F.to_functor.map_id],
      rw [F.right_unitality],
    end,
    mul_assoc' :=
    begin
      conv_lhs { rw [comp_tensor_id, ←F.to_functor.map_id], },
      slice_lhs 2 3 { rw [F.μ_natural], },
      slice_lhs 3 4 { rw [←F.to_functor.map_comp, A.mul_assoc], },
      conv_lhs { rw [F.to_functor.map_id] },
      conv_lhs { rw [F.to_functor.map_comp, F.to_functor.map_comp] },
      conv_rhs { rw [id_tensor_comp, ←F.to_functor.map_id], },
      slice_rhs 3 4 { rw [F.μ_natural], },
      conv_rhs { rw [F.to_functor.map_id] },
      slice_rhs 1 3 { rw [←F.associativity], },
      simp only [category.assoc],
    end, },
  map := λ A B f,
  { hom := F.map f.hom,
    one_hom' := by { dsimp, rw [category.assoc, ←F.to_functor.map_comp, f.one_hom], },
    mul_hom' :=
    begin
      dsimp,
      rw [category.assoc, F.μ_natural_assoc, ←F.to_functor.map_comp, ←F.to_functor.map_comp,
        f.mul_hom],
    end },
  map_id' := λ A, by { ext, simp, },
  map_comp' := λ A B C f g, by { ext, simp, }, }

variables (C D)

/-- `map_Mon` is functorial in the lax monoidal functor. -/
def map_Mon_functor : (lax_monoidal_functor C D) ⥤ (Mon_ C ⥤ Mon_ D) :=
{ obj := map_Mon,
  map := λ F G α,
  { app := λ A,
    { hom := α.app A.X, } } }

end category_theory.lax_monoidal_functor

namespace Mon_

open category_theory.lax_monoidal_functor

namespace equiv_lax_monoidal_functor_punit

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def lax_monoidal_to_Mon : lax_monoidal_functor (discrete punit.{u+1}) C ⥤ Mon_ C :=
{ obj := λ F, (F.map_Mon : Mon_ _ ⥤ Mon_ C).obj (trivial (discrete punit)),
  map := λ F G α, ((map_Mon_functor (discrete punit) C).map α).app _ }

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def Mon_to_lax_monoidal : Mon_ C ⥤ lax_monoidal_functor (discrete punit.{u+1}) C :=
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

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def unit_iso :
  𝟭 (lax_monoidal_functor (discrete punit.{u+1}) C) ≅
    lax_monoidal_to_Mon C ⋙ Mon_to_lax_monoidal C :=
nat_iso.of_components (λ F,
  monoidal_nat_iso.of_components
    (λ _, F.to_functor.map_iso (eq_to_iso (by ext)))
    (by tidy) (by tidy) (by tidy))
  (by tidy)

/-- Implementation of `Mon_.equiv_lax_monoidal_functor_punit`. -/
@[simps]
def counit_iso : Mon_to_lax_monoidal C ⋙ lax_monoidal_to_Mon C ≅ 𝟭 (Mon_ C) :=
nat_iso.of_components (λ F, { hom := { hom := 𝟙 _, }, inv := { hom := 𝟙 _, } })
  (by tidy)

end equiv_lax_monoidal_functor_punit

open equiv_lax_monoidal_functor_punit

/--
Monoid objects in `C` are "just" lax monoidal functors from the trivial monoidal category to `C`.
-/
@[simps]
def equiv_lax_monoidal_functor_punit : lax_monoidal_functor (discrete punit.{u+1}) C ≌ Mon_ C :=
{ functor := lax_monoidal_to_Mon C,
  inverse := Mon_to_lax_monoidal C,
  unit_iso := unit_iso C,
  counit_iso := counit_iso C, }

end Mon_

/-!
Projects:
* Check that `Mon_ Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first, available in #3463)
* Check that `Mon_ Top ≌ [bundled topological monoids]`.
* Check that `Mon_ AddCommGroup ≌ Ring`.
  (We've already got `Mon_ (Module R) ≌ Algebra R`, in `category_theory.monoidal.internal.Module`.)
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
* Show that if `C` is braided then `Mon_ C` is naturally monoidal.
-/

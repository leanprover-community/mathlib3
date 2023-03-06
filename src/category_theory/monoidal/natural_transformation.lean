/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monoidal.functor
import category_theory.full_subcategory

/-!
# Monoidal natural transformations

Natural transformations between (lax) monoidal functors must satisfy
an additional compatibility relation with the tensorators:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`.

(Lax) monoidal functors between a fixed pair of monoidal categories
themselves form a category.
-/

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

open monoidal_category

variables {C : Type u₁} [category.{v₁} C] [monoidal_category.{v₁} C]
          {D : Type u₂} [category.{v₂} D] [monoidal_category.{v₂} D]

/--
A monoidal natural transformation is a natural transformation between (lax) monoidal functors
additionally satisfying:
`F.μ X Y ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ X Y`
-/
@[ext]
structure monoidal_nat_trans (F G : lax_monoidal_functor C D)
  extends nat_trans F.to_functor G.to_functor :=
(unit' : F.ε ≫ app (𝟙_ C) = G.ε . obviously)
(tensor' : ∀ X Y, F.μ _ _ ≫ app (X ⊗ Y) = (app X ⊗ app Y) ≫ G.μ _ _ . obviously)

restate_axiom monoidal_nat_trans.tensor'
attribute [simp, reassoc] monoidal_nat_trans.tensor
restate_axiom monoidal_nat_trans.unit'
attribute [simp, reassoc] monoidal_nat_trans.unit

namespace monoidal_nat_trans

/--
The identity monoidal natural transformation.
-/
@[simps]
def id (F : lax_monoidal_functor C D) : monoidal_nat_trans F F :=
{ ..(𝟙 F.to_functor) }

instance (F : lax_monoidal_functor C D) : inhabited (monoidal_nat_trans F F) := ⟨id F⟩

/--
Vertical composition of monoidal natural transformations.
-/
@[simps]
def vcomp {F G H : lax_monoidal_functor C D}
  (α : monoidal_nat_trans F G) (β : monoidal_nat_trans G H) : monoidal_nat_trans F H :=
{ ..(nat_trans.vcomp α.to_nat_trans β.to_nat_trans) }

instance category_lax_monoidal_functor : category (lax_monoidal_functor C D) :=
{ hom := monoidal_nat_trans,
  id := id,
  comp := λ F G H α β, vcomp α β, }

@[simp] lemma comp_to_nat_trans_lax {F G H : lax_monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

instance category_monoidal_functor : category (monoidal_functor C D) :=
induced_category.category monoidal_functor.to_lax_monoidal_functor

@[simp] lemma comp_to_nat_trans {F G H : monoidal_functor C D} {α : F ⟶ G} {β : G ⟶ H} :
  (α ≫ β).to_nat_trans =
    @category_struct.comp (C ⥤ D) _ _ _ _ (α.to_nat_trans) (β.to_nat_trans) := rfl

variables {E : Type u₃} [category.{v₃} E] [monoidal_category.{v₃} E]

/--
Horizontal composition of monoidal natural transformations.
-/
@[simps]
def hcomp {F G : lax_monoidal_functor C D} {H K : lax_monoidal_functor D E}
  (α : monoidal_nat_trans F G) (β : monoidal_nat_trans H K) :
  monoidal_nat_trans (F ⊗⋙ H) (G ⊗⋙ K) :=
{ unit' :=
  begin
    dsimp, simp,
    conv_lhs { rw [←K.to_functor.map_comp, α.unit], },
  end,
  tensor' := λ X Y,
  begin
    dsimp, simp,
    conv_lhs { rw [←K.to_functor.map_comp, α.tensor, K.to_functor.map_comp], },
  end,
  ..(nat_trans.hcomp α.to_nat_trans β.to_nat_trans) }

section

local attribute [simp] nat_trans.naturality monoidal_nat_trans.unit monoidal_nat_trans.tensor

/-- The cartesian product of two monoidal natural transformations is monoidal. -/
@[simps]
def prod {F G : lax_monoidal_functor C D} {H K : lax_monoidal_functor C E}
  (α : monoidal_nat_trans F G) (β : monoidal_nat_trans H K) :
  monoidal_nat_trans (F.prod' H) (G.prod' K) :=
{ app := λ X, (α.app X, β.app X) }

end

end monoidal_nat_trans

namespace monoidal_nat_iso

variables {F G : lax_monoidal_functor C D}

/--
Construct a monoidal natural isomorphism from object level isomorphisms,
and the monoidal naturality in the forward direction.
-/
def of_components
  (app : ∀ X : C, F.obj X ≅ G.obj X)
  (naturality : ∀ {X Y : C} (f : X ⟶ Y), F.map f ≫ (app Y).hom = (app X).hom ≫ G.map f)
  (unit : F.ε ≫ (app (𝟙_ C)).hom = G.ε)
  (tensor : ∀ X Y, F.μ X Y ≫ (app (X ⊗ Y)).hom = ((app X).hom ⊗ (app Y).hom) ≫ G.μ X Y) :
  F ≅ G :=
{ hom := { app := λ X, (app X).hom, },
  inv :=
  { app := λ X, (app X).inv,
    unit' := by { dsimp, rw [←unit, assoc, iso.hom_inv_id, comp_id], },
    tensor' := λ X Y,
    begin
      dsimp,
      rw [iso.comp_inv_eq, assoc, tensor, ←tensor_comp_assoc,
        iso.inv_hom_id, iso.inv_hom_id, tensor_id, id_comp],
    end,
    ..(nat_iso.of_components app @naturality).inv, }, }

@[simp] lemma of_components.hom_app
  (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
  (of_components app naturality unit tensor).hom.app X = (app X).hom := rfl
@[simp] lemma of_components.inv_app
  (app : ∀ X : C, F.obj X ≅ G.obj X) (naturality) (unit) (tensor) (X) :
  (of_components app naturality unit tensor).inv.app X = (app X).inv :=
by simp [of_components]

instance is_iso_of_is_iso_app (α : F ⟶ G) [∀ X : C, is_iso (α.app X)] : is_iso α :=
⟨(is_iso.of_iso (of_components (λ X, as_iso (α.app X))
  (λ X Y f, α.to_nat_trans.naturality f) α.unit α.tensor)).1⟩

end monoidal_nat_iso

noncomputable theory

/-- The unit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps]
def monoidal_unit (F : monoidal_functor C D) [is_equivalence F.to_functor] :
  lax_monoidal_functor.id C ⟶
    F.to_lax_monoidal_functor ⊗⋙ (monoidal_inverse F).to_lax_monoidal_functor :=
let e := F.to_functor.as_equivalence in
{ to_nat_trans := e.unit,
  tensor' := λ X Y, begin
    -- This proof is not pretty; golfing welcome!
    dsimp,
    simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_naturality_right,
      category.id_comp, category.assoc],
    simp only [←functor.map_comp],
    erw [e.counit_app_functor, e.counit_app_functor, F.to_lax_monoidal_functor.μ_natural,
      is_iso.inv_hom_id_assoc],
    simp only [category_theory.is_equivalence.inv_fun_map],
    slice_rhs 2 3 { erw iso.hom_inv_id_app, },
    dsimp,
    simp only [category_theory.category.id_comp],
    slice_rhs 1 2 { rw [←tensor_comp, iso.hom_inv_id_app, iso.hom_inv_id_app],
      dsimp, rw [tensor_id], },
    simp,
  end }.

instance (F : monoidal_functor C D) [is_equivalence F.to_functor] : is_iso (monoidal_unit F) :=
begin
  haveI : ∀ (X : C), is_iso ((monoidal_unit F).to_nat_trans.app X),
  { intros, dsimp, apply_instance, },
  exact monoidal_nat_iso.is_iso_of_is_iso_app _
end

/-- The counit of a monoidal equivalence can be upgraded to a monoidal natural transformation. -/
@[simps]
def monoidal_counit (F : monoidal_functor C D) [is_equivalence F.to_functor] :
  (monoidal_inverse F).to_lax_monoidal_functor ⊗⋙ F.to_lax_monoidal_functor ⟶
    lax_monoidal_functor.id D :=
let e := F.to_functor.as_equivalence in
{ to_nat_trans := e.counit,
  unit' := begin
    dsimp,
    simp only [category.comp_id, category.assoc, functor.map_inv, functor.map_comp,
      nat_iso.inv_inv_app, is_iso.inv_comp, is_equivalence.fun_inv_map, adjunction.hom_equiv_unit],
    erw [e.counit_app_functor, ←e.functor.map_comp_assoc, iso.hom_inv_id_app],
    dsimp, simp,
  end,
  tensor' := λ X Y, begin
    dsimp,
    simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_naturality_right, category.assoc,
      category.comp_id, functor.map_comp],
    simp only [is_equivalence.fun_inv_map],
    erw [e.counit_app_functor],
    simp only [category.assoc],
    erw [←e.functor.map_comp_assoc],
    simp only [category_theory.iso.inv_hom_id_app,
      category_theory.iso.inv_hom_id_app_assoc],
    erw [iso.hom_inv_id_app],
    erw [category_theory.functor.map_id],
    simp only [category.id_comp],
    simp only [category_theory.iso.inv_hom_id_app,
      category_theory.is_iso.hom_inv_id_assoc],
    erw [iso.inv_hom_id_app],
    dsimp, simp, refl,
  end }

instance (F : monoidal_functor C D) [is_equivalence F.to_functor] : is_iso (monoidal_counit F) :=
begin
  haveI : ∀ (X : D), is_iso ((monoidal_counit F).to_nat_trans.app X),
  { intros, dsimp, apply_instance, },
  exact monoidal_nat_iso.is_iso_of_is_iso_app _
end

end category_theory

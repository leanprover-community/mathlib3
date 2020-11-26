/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.equalizers
import category_theory.adjunction
import category_theory.monad.adjunction

namespace category_theory

open category limits

universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {A : Type u₁} {B : Type u₂} {C : Type u₃}
variables [category.{v₁} A] [category.{v₂} B] [category.{v₃} C]

/-- `A` has reflexive coequalizers if every reflexive pair has a coequalizer. -/
def has_reflexive_coequalizers (A : Type u₁) [category.{v₁} A] : Prop :=
∀ ⦃X Y : A⦄ (f g : X ⟶ Y) (r : Y ⟶ X), r ≫ f = 𝟙 _ → r ≫ g = 𝟙 _ → has_coequalizer f g

lemma reflexive_coequalizers_of_has_coequalizers [has_coequalizers A] :
  has_reflexive_coequalizers A :=
λ X Y f g r rf rg, by apply_instance

namespace lift_adjoint

variables {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (F' : C ⥤ A)
variables (adj₁ : F ⊣ U) (adj₂ : F' ⊣ R ⋙ U)

variables (hU : Π (X : B), is_colimit (cofork.of_π (adj₁.counit.app X) (adj₁.counit_naturality _)))

include adj₁ adj₂

/-- To construct the left adjoint, we use the coequalizer of `F'Uε_Y` with this morphism. -/
def second_map_app (X) : F'.obj (U.obj (F.obj (U.obj X))) ⟶ F'.obj (U.obj X) :=
F'.map (U.map (F.map (adj₂.unit.app _) ≫ adj₁.counit.app _)) ≫ adj₂.counit.app _

variables (hA : has_reflexive_coequalizers A)
include hA

/-- The coequalizer that we wish to construct is for a reflexive pair, so it exists. -/
lemma L_exists (Y : B) :
  has_coequalizer (F'.map (U.map (adj₁.counit.app Y))) (second_map_app _ _ adj₁ adj₂ Y) :=
begin
  apply hA _ _ (F'.map (adj₁.unit.app (U.obj Y))) _ _,
  { rw [← F'.map_comp, adj₁.right_triangle_components],
    apply F'.map_id },
  { dsimp [second_map_app],
    rw [← F'.map_comp_assoc, U.map_comp, adj₁.unit_naturality_assoc, adj₁.right_triangle_components,
        comp_id, adj₂.left_triangle_components] }
end

local attribute [instance] L_exists

/--
Construct the object part of the desired left adjoint as the coequalizer of `F'Uε_Y` with
`second_map_app`.
-/
noncomputable def L_obj (Y : B) : A :=
begin
  haveI := L_exists R F' adj₁ adj₂ hA,
  exact coequalizer (F'.map (U.map (adj₁.counit.app Y))) (second_map_app _ _ adj₁ adj₂ Y)
end

include hU

/-- The homset equivalence which helps show that `R` is a right adjoint. -/
noncomputable
def L_equiv (Y : A) (X : B) : (L_obj _ _ adj₁ adj₂ hA X ⟶ Y) ≃ (X ⟶ R.obj Y) :=
calc (L_obj _ _ adj₁ adj₂ hA X ⟶ Y)
        ≃ {f : F'.obj (U.obj X) ⟶ Y //
              F'.map (U.map (adj₁.counit.app X)) ≫ f = second_map_app _ _ adj₁ adj₂ _ ≫ f} :
                by apply cofork.is_colimit.hom_iso _ (colimit.is_colimit _)
  ... ≃ {g : U.obj X ⟶ U.obj (R.obj Y) //
          U.map (F.map g ≫ adj₁.counit.app _) = U.map (adj₁.counit.app _) ≫ g} :
            begin
              apply (adj₂.hom_equiv _ _).subtype_congr _,
              intro f,
              rw [← (adj₂.hom_equiv _ _).injective.eq_iff, eq_comm, adj₂.hom_equiv_naturality_left,
                  second_map_app, assoc, adj₂.hom_equiv_naturality_left, ← adj₂.counit_naturality,
                  adj₂.hom_equiv_naturality_left, adj₂.hom_equiv_unit,
                  adj₂.right_triangle_components, comp_id, functor.comp_map, ← U.map_comp, assoc,
                  ← adj₁.counit_naturality, adj₂.hom_equiv_unit, adj₂.hom_equiv_unit, F.map_comp,
                  assoc],
              refl,
            end
  ... ≃ {z : F.obj (U.obj X) ⟶ R.obj Y // _} :
            begin
              apply (adj₁.hom_equiv _ _).symm.subtype_congr,
              intro g,
              rw [← (adj₁.hom_equiv _ _).symm.injective.eq_iff, adj₁.hom_equiv_counit,
                  adj₁.hom_equiv_counit, adj₁.hom_equiv_counit, F.map_comp, assoc, U.map_comp,
                  F.map_comp, assoc, adj₁.counit_naturality, adj₁.counit_naturality_assoc,
                  eq_comm],
              refl,
            end
  ... ≃ (X ⟶ R.obj Y) : (cofork.is_colimit.hom_iso _ (hU X)).symm

/-- Construct the left adjoint to `R`, with object map `L_obj`. -/
noncomputable def construct_left_adjoint : B ⥤ A :=
begin
  refine adjunction.left_adjoint_of_equiv (λ X Y, L_equiv R F' adj₁ adj₂ hU hA Y X) _,
  intros X Y Y' g h,
  dsimp [L_equiv, -cofork.is_colimit.hom_iso_symm_apply],
  rw equiv.symm_apply_eq,
  ext,
  rw [cofork.is_colimit.hom_iso_natural, equiv.apply_symm_apply],
  dsimp,
  rw [← adj₁.hom_equiv_naturality_right_symm, ← functor.comp_map R U,
      ← adj₂.hom_equiv_naturality_right, assoc],
end

end lift_adjoint

/--
The adjoint triangle theorem: Suppose `U : B ⥤ C` has a left adjoint `F` such that `ε_X : FUX ⟶ X`
is a coequalizer for the pair `(FUε_X, ε_FUX)` for every `X` (where `ε` is the counit of the
adjunction `F ⊣ U`). Then if a category `A` has coequalizers of reflexive pairs, then a functor
`R : A ⥤ B` has a left adjoint if the composite `R ⋙ U` does.

Note the converse is true (with weaker assumptions), by `adjunction.comp`.
See https://ncatlab.org/nlab/show/adjoint+triangle+theorem
-/
noncomputable def adjoint_triangle_lift {U : B ⥤ C} {F : C ⥤ B} (R : A ⥤ B) (adj₁ : F ⊣ U)
  (hU : Π (X : B), is_colimit (cofork.of_π (adj₁.counit.app X) (adj₁.counit_naturality _)))
  (hA : has_reflexive_coequalizers A)
  [is_right_adjoint (R ⋙ U)] : is_right_adjoint R :=
{ left := lift_adjoint.construct_left_adjoint R _ adj₁ (adjunction.of_right_adjoint _) hU hA,
  adj := adjunction.adjunction_of_equiv_left _ _ }

/-!
Show that any algebra is a coequalizer of free algebras.
-/
namespace cofork_free
variables (T : B ⥤ B) [monad T] (X : monad.algebra T)

/-- The top map in the coequalizer diagram we will construct. -/
@[simps {rhs_md := semireducible}]
def top_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
(monad.free T).map X.a
/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def bottom_map : (monad.free T).obj (T.obj X.A) ⟶ (monad.free T).obj X.A :=
{ f := (μ_ T).app X.A,
  h' := monad.assoc X.A }
/-- The bottom map in the coequalizer diagram we will construct. -/
@[simps]
def coequalizer_map : (monad.free T).obj X.A ⟶ X :=
{ f := X.a,
  h' := X.assoc.symm }
lemma comm : top_map T X ≫ coequalizer_map T X = bottom_map T X ≫ coequalizer_map T X :=
begin
  ext1,
  apply X.assoc.symm,
end

/--
The cofork constructed is a colimit. This shows that any algebra is a coequalizer of free algebras.
-/
def is_colimit : is_colimit (cofork.of_π _ (comm T X)) :=
cofork.is_colimit.mk' _ $ λ s,
begin
  have h₁ : T.map X.a ≫ s.π.f = (μ_ T).app X.A ≫ s.π.f := congr_arg monad.algebra.hom.f s.condition,
  have h₂ : T.map s.π.f ≫ s.X.a = (μ_ T).app X.A ≫ s.π.f := s.π.h,
  refine ⟨⟨(η_ T).app _ ≫ s.π.f, _⟩, _, _⟩,
  { dsimp,
    rw [T.map_comp, assoc, h₂, monad.right_unit_assoc,
        (show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { ext1,
    dsimp,
    rw [(show X.a ≫ _ ≫ _ = _, from (η_ T).naturality_assoc _ _), h₁, monad.left_unit_assoc] },
  { intros m hm,
    ext1,
    dsimp,
    rw ← hm,
    dsimp,
    rw X.unit_assoc }
end
@[simp] lemma is_colimit_X : (cofork.of_π _ (comm T X)).X = X := rfl

end cofork_free

/--
If `R ⋙ monad.forget T` has a left adjoint, and the domain of `R` has reflexive coequalizers,
then `R` has a left adjoint. Note that this is a special case of `monadic_adjoint_triangle_lift`,
but is helpful for proving that.
-/
noncomputable def monad_forget_adjoint_triangle_lift (T : B ⥤ B) [monad T]
  (R : A ⥤ monad.algebra T) (hA : has_reflexive_coequalizers A)
  [is_right_adjoint (R ⋙ monad.forget T)] :
  is_right_adjoint R :=
begin
  apply adjoint_triangle_lift R (monad.adj T) _ hA,
  intro A,
  have : (monad.forget T).map ((monad.adj T).counit.app A) = A.a,
  { dsimp [monad.adj, adjunction.mk_of_hom_equiv],
    rw [T.map_id, id_comp] },
  have : (monad.adj T).counit.app A = cofork_free.coequalizer_map T A,
  { ext1,
    apply this },
  have : (monad.adj T).counit.app ((monad.free T).obj _) = cofork_free.bottom_map T A,
  { ext1,
    dsimp [monad.adj, adjunction.mk_of_hom_equiv],
    rw [T.map_id, id_comp] },
  convert cofork_free.is_colimit T A,
end

/--
If `R ⋙ U` has a left adjoint, the domain of `R` has reflexive coequalizers and `U` is a monadic
functor, then `R` has a left adjoint.
This is a special case of `adjoint_triangle_lift` which is often more useful in practice.
-/
noncomputable def monadic_adjoint_triangle_lift (U : B ⥤ C) [monadic_right_adjoint U] {R : A ⥤ B}
  (hA : has_reflexive_coequalizers A)
  [is_right_adjoint (R ⋙ U)] :
  is_right_adjoint R :=
begin
  let R' : A ⥤ _ := R ⋙ monad.comparison U,
  suffices : is_right_adjoint R',
  { let : is_right_adjoint (R' ⋙ (monad.comparison U).inv),
    { resetI,
      apply_instance },
    { let : R' ⋙ (monad.comparison U).inv ≅ R :=
        (iso_whisker_left R (monad.comparison U).fun_inv_id : _) ≪≫ R.right_unitor,
      exactI adjunction.right_adjoint_of_nat_iso this } },
  apply monad_forget_adjoint_triangle_lift _ _ hA,
  apply adjunction.right_adjoint_of_nat_iso (iso_whisker_left R (monad.comparison_forget U).symm),
end

variables {D : Type u₄}
variables [category.{v₄} D]

/--
Given a commutative square of functors

A → B
↓   ↓
C → D

where the vertical functors are monadic, and `A` has reflexive coequalizers, then if the bottom
functor has a left adjoint, then the top functor does as well.

See https://ncatlab.org/nlab/show/adjoint+lifting+theorem
-/
noncomputable def adjoint_square_lift (Q : A ⥤ B) (V : B ⥤ D) (U : A ⥤ C) (R : C ⥤ D)
  (comm : U ⋙ R ≅ Q ⋙ V)
  [monadic_right_adjoint U] [monadic_right_adjoint V]
  (hA : has_reflexive_coequalizers A)
  [is_right_adjoint R] :
  is_right_adjoint Q :=
begin
  let := adjunction.right_adjoint_of_nat_iso comm,
  exactI monadic_adjoint_triangle_lift V hA,
end

end category_theory

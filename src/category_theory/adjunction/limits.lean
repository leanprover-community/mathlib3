/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Johan Commelin
-/
import category_theory.adjunction.basic
import category_theory.limits.preserves

open opposite

namespace category_theory.adjunction
open category_theory
open category_theory.functor
open category_theory.limits

universes u₁ u₂ v

variables {C : Type u₁} [𝒞 : category.{v+1} C] {D : Type u₂} [𝒟 : category.{v+1} D]
include 𝒞 𝒟

variables {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
include adj

section preservation_colimits
variables {J : Type v} [small_category J] (K : J ⥤ C)

@[simp] def functoriality_right_adjoint : cocone (K ⋙ F) ⥤ cocone K :=
(cocones.functoriality G) ⋙ (cocones.precompose
  (K.right_unitor.inv ≫ (whisker_left K adj.unit) ≫ (associator _ _ _).inv))

@[simp] def functoriality_is_left_adjoint_unit :
  𝟭 (cocone K) ⟶ cocones.functoriality F ⋙ functoriality_right_adjoint adj K :=
{ app := λ c,
  { hom := adj.unit.app c.X,
    w' := λ j, by have := adj.unit.naturality (c.ι.app j); tidy },
  naturality' := λ _ _ f, by have := adj.unit.naturality (f.hom); tidy }.

@[simp] def functoriality_is_left_adjoint_counit :
  functoriality_right_adjoint adj K ⋙ cocones.functoriality F ⟶ 𝟭 (cocone (K ⋙ F)) :=
{ app := λ c,
  { hom := adj.counit.app c.X,
    w' :=
    begin
      intro j,
      dsimp,
      erw [category.comp_id, category.id_comp, F.map_comp, category.assoc,
        adj.counit.naturality (c.ι.app j), ← category.assoc,
        adj.left_triangle_components, category.id_comp],
      refl,
    end },
  naturality' := λ _ _ f, by have := adj.counit.naturality (f.hom); tidy }.

def functoriality_is_left_adjoint :
  is_left_adjoint (@cocones.functoriality _ _ _ _ K _ _ F) :=
{ right := functoriality_right_adjoint adj K,
  adj := mk_of_unit_counit
  { unit := functoriality_is_left_adjoint_unit adj K,
    counit := functoriality_is_left_adjoint_counit adj K, } }

/-- A left adjoint preserves colimits. -/
instance left_adjoint_preserves_colimits : preserves_colimits F :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by resetI; exact
    { preserves := λ c hc, is_colimit_iso_unique_cocone_morphism.inv
        (λ s, (((adj.functoriality_is_left_adjoint _).adj).hom_equiv _ _).unique_of_equiv $
          is_colimit_iso_unique_cocone_morphism.hom hc _ ) } } }.

end preservation_colimits

section preservation_limits
variables {J : Type v} [small_category J] (K : J ⥤ D)

@[simp] def functoriality_left_adjoint : cone (K ⋙ G) ⥤ cone K :=
(cones.functoriality F) ⋙ (cones.postcompose
  ((associator _ _ _).hom ≫ (whisker_left K adj.counit) ≫ K.right_unitor.hom))

@[simp] def functoriality_is_right_adjoint_unit :
  𝟭 (cone (K ⋙ G)) ⟶ functoriality_left_adjoint adj K ⋙ cones.functoriality G :=
{ app := λ c,
  { hom := adj.unit.app c.X,
    w' :=
    begin
      intro j,
      dsimp,
      erw [category.comp_id, category.id_comp, G.map_comp, ← category.assoc,
        ← adj.unit.naturality (c.π.app j), category.assoc,
        adj.right_triangle_components, category.comp_id],
      refl,
    end },
  naturality' := λ _ _ f, by have := adj.unit.naturality (f.hom); tidy }.

@[simp] def functoriality_is_right_adjoint_counit :
  cones.functoriality G ⋙ functoriality_left_adjoint adj K ⟶ 𝟭 (cone K) :=
{ app := λ c,
  { hom := adj.counit.app c.X,
    w' := λ j, by have := adj.counit.naturality (c.π.app j); tidy },
  naturality' := λ _ _ f, by have := adj.counit.naturality (f.hom); tidy }.

def functoriality_is_right_adjoint :
  is_right_adjoint (@cones.functoriality _ _ _ _ K _ _ G) :=
{ left := functoriality_left_adjoint adj K,
  adj := mk_of_unit_counit
  { unit := functoriality_is_right_adjoint_unit adj K,
    counit := functoriality_is_right_adjoint_counit adj K } }.

/-- A right adjoint preserves limits. -/
instance right_adjoint_preserves_limits : preserves_limits G :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ K,
    by resetI; exact
    { preserves := λ c hc, is_limit_iso_unique_cone_morphism.inv
        (λ s, (((adj.functoriality_is_right_adjoint _).adj).hom_equiv _ _).symm.unique_of_equiv $
          is_limit_iso_unique_cone_morphism.hom hc _) } } }.

omit adj

-- TODO the implicit arguments make preserves_limit* quite hard to use.
-- This should be refactored at some point. (Possibly including making `is_limit` a class.)
def is_limit_map_cone (E : D ⥤ C) [is_equivalence E]
  (c : cone K) (h : is_limit c) : is_limit (E.map_cone c) :=
begin
  have P : preserves_limits E := adjunction.right_adjoint_preserves_limits E.inv.adjunction,
  have P' := P.preserves_limits_of_shape,
  have P'' := P'.preserves_limit,
  have P''' := P''.preserves,
  exact P''' h,
end

instance has_limit_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit K] :
  has_limit (K ⋙ E) :=
{ cone := E.map_cone (limit.cone K),
  is_limit := is_limit_map_cone _ _ _ (limit.is_limit K) }

def has_limit_of_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit (K ⋙ E)] :
  has_limit K :=
@has_limit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K
(@adjunction.has_limit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
((iso_whisker_left K (fun_inv_id E)) ≪≫ (functor.right_unitor _))

end preservation_limits

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cocones_iso {J : Type v} [small_category J] {K : J ⥤ C} :
  (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ ((cocones J C).obj (op K)) :=
nat_iso.of_components (λ Y,
{ hom := λ t,
    { app := λ j, (adj.hom_equiv (K.obj j) Y) (t.app j),
      naturality' := λ j j' f, by erw [← adj.hom_equiv_naturality_left, t.naturality]; dsimp; simp },
  inv := λ t,
    { app := λ j, (adj.hom_equiv (K.obj j) Y).symm (t.app j),
      naturality' := λ j j' f, begin
        erw [← adj.hom_equiv_naturality_left_symm, ← adj.hom_equiv_naturality_right_symm, t.naturality],
        dsimp, simp
      end } } )
begin
  intros Y₁ Y₂ f,
  ext1 t,
  ext1 j,
  apply adj.hom_equiv_naturality_right
end

-- Note: this is natural in K, but we do not yet have the tools to formulate that.
def cones_iso {J : Type v} [small_category J] {K : J ⥤ D} :
  F.op ⋙ ((cones J D).obj K) ≅ (cones J C).obj (K ⋙ G) :=
nat_iso.of_components (λ X,
{ hom := λ t,
  { app := λ j, (adj.hom_equiv (unop X) (K.obj j)) (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right, ← t.naturality, category.id_comp, category.id_comp],
      refl
    end },
  inv := λ t,
  { app := λ j, (adj.hom_equiv (unop X) (K.obj j)).symm (t.app j),
    naturality' := λ j j' f, begin
      erw [← adj.hom_equiv_naturality_right_symm, ← t.naturality, category.id_comp, category.id_comp]
    end } } )
(by tidy)

end category_theory.adjunction

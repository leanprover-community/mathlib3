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

variables {C : Sort u₁} [𝒞 : category.{v+1} C] {D : Sort u₂} [𝒟 : category.{v+1} D]
include 𝒞 𝒟

variables {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
include adj

section preservation_colimits
variables {J : Type v} [small_category J] (K : J ⥤ C)

def functoriality_is_left_adjoint :
  is_left_adjoint (@cocones.functoriality _ _ _ _ K _ _ F) :=
{ right := (cocones.functoriality G) ⋙ (cocones.precompose
    (K.right_unitor.inv ≫ (whisker_left K adj.unit) ≫ (associator _ _ _).inv)),
  adj := mk_of_unit_counit
  { unit := { app := λ c, { hom := adj.unit.app c.X } },
    counit := { app := λ c, { hom := adj.counit.app c.X } } } }

/-- A left adjoint preserves colimits. -/
instance left_adjoint_preserves_colimits : preserves_colimits F :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI
    { preserves := λ c hc, is_colimit.iso_unique_cocone_morphism.inv
        (λ s, (((adj.functoriality_is_left_adjoint _).adj).hom_equiv _ _).unique_of_equiv $
          is_colimit.iso_unique_cocone_morphism.hom hc _ ) } } }.

omit adj

instance is_equivalence_preserves_colimits (E : C ⥤ D) [is_equivalence E] : preserves_colimits E :=
adjunction.left_adjoint_preserves_colimits E.adjunction

-- verify the preserve_colimits instance works as expected:
example (E : C ⥤ D) [is_equivalence E]
  (c : cocone K) (h : is_colimit c) : is_colimit (E.map_cocone c) :=
preserves_colimit.preserves E h

instance has_colimit_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit K] :
  has_colimit (K ⋙ E) :=
{ cocone := E.map_cocone (colimit.cocone K),
  is_colimit := preserves_colimit.preserves E (colimit.is_colimit K) }

def has_colimit_of_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit (K ⋙ E)] :
  has_colimit K :=
@has_colimit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K
(@adjunction.has_colimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
((functor.right_unitor _).symm ≪≫ (iso_whisker_left K (fun_inv_id E)).symm)

end preservation_colimits

section preservation_limits
variables {J : Type v} [small_category J] (K : J ⥤ D)

def functoriality_is_right_adjoint :
  is_right_adjoint (@cones.functoriality _ _ _ _ K _ _ G) :=
{ left := (cones.functoriality F) ⋙ (cones.postcompose
    ((associator _ _ _).hom ≫ (whisker_left K adj.counit) ≫ K.right_unitor.hom)),
  adj := mk_of_unit_counit
  { unit := { app := λ c, { hom := adj.unit.app c.X, } },
    counit := { app := λ c, { hom := adj.counit.app c.X, } } } }

/-- A right adjoint preserves limits. -/
instance right_adjoint_preserves_limits : preserves_limits G :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ K,
    by exactI
    { preserves := λ c hc, is_limit.iso_unique_cone_morphism.inv
        (λ s, (((adj.functoriality_is_right_adjoint _).adj).hom_equiv _ _).symm.unique_of_equiv $
          is_limit.iso_unique_cone_morphism.hom hc _) } } }.

omit adj

instance is_equivalence_preserves_limits (E : D ⥤ C) [is_equivalence E] : preserves_limits E :=
adjunction.right_adjoint_preserves_limits E.inv.adjunction

-- verify the preserve_limits instance works as expected:
example (E : D ⥤ C) [is_equivalence E]
  (c : cone K) [h : is_limit c] : is_limit (E.map_cone c) :=
preserves_limit.preserves E h

instance has_limit_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit K] :
  has_limit (K ⋙ E) :=
{ cone := E.map_cone (limit.cone K),
  is_limit := preserves_limit.preserves E (limit.is_limit K) }

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
(by tidy)

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

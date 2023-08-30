/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.limits.shapes.pullbacks
import category_theory.limits.shapes.binary_products
import category_theory.limits.preserves.shapes.pullbacks

/-!
# Relating monomorphisms and epimorphisms to limits and colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If `F` preserves (resp. reflects) pullbacks, then it preserves (resp. reflects) monomorphisms.

We also provide the dual version for epimorphisms.

-/

universes v₁ v₂ u₁ u₂

namespace category_theory
open category limits

variables {C : Type u₁} {D : Type u₂} [category.{v₁} C] [category.{v₂} D]
variables (F : C ⥤ D)

/-- If `F` preserves pullbacks, then it preserves monomorphisms. -/
lemma preserves_mono_of_preserves_limit {X Y : C} (f : X ⟶ Y) [preserves_limit (cospan f f) F]
  [mono f] : mono (F.map f) :=
begin
  have := is_limit_pullback_cone_map_of_is_limit F _ (pullback_cone.is_limit_mk_id_id f),
  simp_rw [F.map_id] at this,
  apply pullback_cone.mono_of_is_limit_mk_id_id _ this,
end

@[priority 100]
instance preserves_monomorphisms_of_preserves_limits_of_shape
  [preserves_limits_of_shape walking_cospan F] : F.preserves_monomorphisms :=
{ preserves := λ X Y f hf, by exactI preserves_mono_of_preserves_limit F f }

/-- If `F` reflects pullbacks, then it reflects monomorphisms. -/
lemma reflects_mono_of_reflects_limit {X Y : C} (f : X ⟶ Y) [reflects_limit (cospan f f) F]
  [mono (F.map f)] : mono f :=
begin
  have := pullback_cone.is_limit_mk_id_id (F.map f),
  simp_rw [←F.map_id] at this,
  apply pullback_cone.mono_of_is_limit_mk_id_id _ (is_limit_of_is_limit_pullback_cone_map F _ this),
end

@[priority 100]
instance reflects_monomorphisms_of_reflects_limits_of_shape
  [reflects_limits_of_shape walking_cospan F] : F.reflects_monomorphisms :=
{ reflects := λ X Y f hf, by exactI reflects_mono_of_reflects_limit F f }

/-- If `F` preserves pushouts, then it preserves epimorphisms. -/
lemma preserves_epi_of_preserves_colimit {X Y : C} (f : X ⟶ Y) [preserves_colimit (span f f) F]
  [epi f] : epi (F.map f) :=
begin
  have := is_colimit_pushout_cocone_map_of_is_colimit F _ (pushout_cocone.is_colimit_mk_id_id f),
  simp_rw [F.map_id] at this,
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _ this,
end

@[priority 100]
instance preserves_epimorphisms_of_preserves_colimits_of_shape
  [preserves_colimits_of_shape walking_span F] : F.preserves_epimorphisms :=
{ preserves := λ X Y f hf, by exactI preserves_epi_of_preserves_colimit F f }

/-- If `F` reflects pushouts, then it reflects epimorphisms. -/
lemma reflects_epi_of_reflects_colimit {X Y : C} (f : X ⟶ Y) [reflects_colimit (span f f) F]
  [epi (F.map f)] : epi f :=
begin
  have := pushout_cocone.is_colimit_mk_id_id (F.map f),
  simp_rw [← F.map_id] at this,
  apply pushout_cocone.epi_of_is_colimit_mk_id_id _
    (is_colimit_of_is_colimit_pushout_cocone_map F _ this)
end

@[priority 100]
instance reflects_epimorphisms_of_reflects_colimits_of_shape
  [reflects_colimits_of_shape walking_span F] : F.reflects_epimorphisms :=
{ reflects := λ X Y f hf, by exactI reflects_epi_of_reflects_colimit F f }

end category_theory

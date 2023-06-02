/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Scott Morrison, Mario Carneiro, Andrew Yang
-/
import topology.category.Top.basic
import category_theory.limits.concrete_category

/-!
# The category of topological spaces has all limits and colimits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further, these limits and colimits are preserved by the forgetful functor --- that is, the
underlying types are just the limits in the category of types.
-/

open topological_space
open category_theory
open category_theory.limits
open opposite

universes u v w

noncomputable theory

namespace Top

variables {J : Type v} [small_category J]

local notation `forget` := forget Top

/--
A choice of limit cone for a functor `F : J ⥤ Top`.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone (F : J ⥤ Top.{max v u}) : cone F :=
{ X := Top.of {u : Π j : J, F.obj j | ∀ {i j : J} (f : i ⟶ j), F.map f (u i) = u j},
  π :=
  { app := λ j,
    { to_fun := λ u, u.val j,
      continuous_to_fun := show continuous ((λ u : Π j : J, F.obj j, u j) ∘ subtype.val),
        by continuity } } }

/--
A choice of limit cone for a functor `F : J ⥤ Top` whose topology is defined as an
infimum of topologies infimum.
Generally you should just use `limit.cone F`, unless you need the actual definition
(which is in terms of `types.limit_cone`).
-/
def limit_cone_infi (F : J ⥤ Top.{max v u}) : cone F :=
{ X := ⟨(types.limit_cone (F ⋙ forget)).X, ⨅j,
        (F.obj j).str.induced ((types.limit_cone (F ⋙ forget)).π.app j)⟩,
  π :=
  { app := λ j, ⟨(types.limit_cone (F ⋙ forget)).π.app j,
                 continuous_iff_le_induced.mpr (infi_le _ _)⟩,
    naturality' := λ j j' f, continuous_map.coe_injective
      ((types.limit_cone (F ⋙ forget)).π.naturality f) } }

/--
The chosen cone `Top.limit_cone F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_is_limit (F : J ⥤ Top.{max v u}) : is_limit (limit_cone F) :=
{ lift := λ S, { to_fun := λ x, ⟨λ j, S.π.app _ x, λ i j f, by { dsimp, erw ← S.w f, refl }⟩ },
  uniq' := λ S m h, by { ext : 3, simpa [← h] } }

/--
The chosen cone `Top.limit_cone_infi F` for a functor `F : J ⥤ Top` is a limit cone.
Generally you should just use `limit.is_limit F`, unless you need the actual definition
(which is in terms of `types.limit_cone_is_limit`).
-/
def limit_cone_infi_is_limit (F : J ⥤ Top.{max v u}) : is_limit (limit_cone_infi F) :=
by { refine is_limit.of_faithful forget (types.limit_cone_is_limit _) (λ s, ⟨_, _⟩) (λ s, rfl),
     exact continuous_iff_coinduced_le.mpr (le_infi $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.π.app j).continuous :
         _) ) }

instance Top_has_limits_of_size : has_limits_of_size.{v} Top.{max v u} :=
{ has_limits_of_shape := λ J 𝒥, by exactI
  { has_limit := λ F, has_limit.mk { cone := limit_cone F, is_limit := limit_cone_is_limit F } } }

instance Top_has_limits : has_limits Top.{u} := Top.Top_has_limits_of_size.{u u}

instance forget_preserves_limits_of_size :
  preserves_limits_of_size.{v v} (forget : Top.{max v u} ⥤ Type (max v u)) :=
{ preserves_limits_of_shape := λ J 𝒥,
  { preserves_limit := λ F,
    by exactI preserves_limit_of_preserves_limit_cone
      (limit_cone_is_limit F) (types.limit_cone_is_limit (F ⋙ forget)) } }

instance forget_preserves_limits : preserves_limits (forget : Top.{u} ⥤ Type u) :=
Top.forget_preserves_limits_of_size.{u u}

/--
A choice of colimit cocone for a functor `F : J ⥤ Top`.
Generally you should just use `colimit.coone F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone`).
-/
def colimit_cocone (F : J ⥤ Top.{max v u}) : cocone F :=
{ X := ⟨(types.colimit_cocone (F ⋙ forget)).X, ⨆ j,
        (F.obj j).str.coinduced ((types.colimit_cocone (F ⋙ forget)).ι.app j)⟩,
  ι :=
  { app := λ j, ⟨(types.colimit_cocone (F ⋙ forget)).ι.app j,
                 continuous_iff_coinduced_le.mpr (le_supr _ j)⟩,
    naturality' := λ j j' f, continuous_map.coe_injective
      ((types.colimit_cocone (F ⋙ forget)).ι.naturality f) } }

/--
The chosen cocone `Top.colimit_cocone F` for a functor `F : J ⥤ Top` is a colimit cocone.
Generally you should just use `colimit.is_colimit F`, unless you need the actual definition
(which is in terms of `types.colimit_cocone_is_colimit`).
-/
def colimit_cocone_is_colimit (F : J ⥤ Top.{max v u}) : is_colimit (colimit_cocone F) :=
by { refine is_colimit.of_faithful forget (types.colimit_cocone_is_colimit _) (λ s, ⟨_, _⟩)
       (λ s, rfl),
     exact continuous_iff_le_induced.mpr (supr_le $ λ j,
       coinduced_le_iff_le_induced.mp $ (continuous_iff_coinduced_le.mp (s.ι.app j).continuous :
         _) ) }

instance Top_has_colimits_of_size : has_colimits_of_size.{v} Top.{max v u} :=
{ has_colimits_of_shape := λ J 𝒥, by exactI
  { has_colimit := λ F, has_colimit.mk { cocone := colimit_cocone F, is_colimit :=
    colimit_cocone_is_colimit F } } }

instance Top_has_colimits : has_colimits Top.{u} := Top.Top_has_colimits_of_size.{u u}

instance forget_preserves_colimits_of_size :
  preserves_colimits_of_size.{v v} (forget : Top.{max v u} ⥤ Type (max v u)) :=
{ preserves_colimits_of_shape := λ J 𝒥,
  { preserves_colimit := λ F,
    by exactI preserves_colimit_of_preserves_colimit_cocone
      (colimit_cocone_is_colimit F) (types.colimit_cocone_is_colimit (F ⋙ forget)) } }

instance forget_preserves_colimits : preserves_colimits (forget : Top.{u} ⥤ Type u) :=
Top.forget_preserves_colimits_of_size.{u u}

/-- The terminal object of `Top` is `punit`. -/
def is_terminal_punit : is_terminal (Top.of punit.{u+1}) :=
begin
  haveI : ∀ X, unique (X ⟶ Top.of punit.{u+1}) :=
    λ X, ⟨⟨⟨λ x, punit.star, by continuity⟩⟩, λ f, by ext⟩,
  exact limits.is_terminal.of_unique _,
end

/-- The terminal object of `Top` is `punit`. -/
def terminal_iso_punit : ⊤_ Top.{u} ≅ Top.of punit :=
terminal_is_terminal.unique_up_to_iso is_terminal_punit

/-- The initial object of `Top` is `pempty`. -/
def is_initial_pempty : is_initial (Top.of pempty.{u+1}) :=
begin
  haveI : ∀ X, unique (Top.of pempty.{u+1} ⟶ X) :=
    λ X, ⟨⟨⟨λ x, x.elim, by continuity⟩⟩, λ f, by ext ⟨⟩⟩,
  exact limits.is_initial.of_unique _,
end

/-- The initial object of `Top` is `pempty`. -/
def initial_iso_pempty : ⊥_ Top.{u} ≅ Top.of pempty :=
initial_is_initial.unique_up_to_iso is_initial_pempty

end Top

/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Jujian Zhang
-/
import category_theory.abelian.functor_category
import category_theory.preadditive.additive_functor
import category_theory.preadditive.functor_category
import category_theory.abelian.transfer
import category_theory.sites.left_exact

/-!
# Category of sheaves is abelian

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Let `C, D` be categories and `J` be a grothendieck topology on `C`, when `D` is abelian and
sheafification is possible in `C`, `Sheaf J D` is abelian as well (`Sheaf_is_abelian`).

Hence, `presheaf_to_Sheaf` is an additive functor (`presheaf_to_Sheaf_additive`).

-/

noncomputable theory

namespace category_theory

open category_theory.limits

section abelian

universes w v u
variables {C : Type (max v u)} [category.{v} C]
variables {D : Type w} [category.{max v u} D] [abelian D]
variables {J : grothendieck_topology C}

-- This needs to be specified manually because of universe level.
instance : abelian (Cᵒᵖ ⥤ D) := @abelian.functor_category_abelian.{v} Cᵒᵖ _ D _ _

-- This also needs to be specified manually, but I don't know why.
instance : has_finite_products (Sheaf J D) :=
{ out := λ j, { has_limit := λ F, by apply_instance } }

-- sheafification assumptions
variables [∀ (P : Cᵒᵖ ⥤ D) (X : C) (S : J.cover X), has_multiequalizer (S.index P)]
variables [∀ (X : C), has_colimits_of_shape (J.cover X)ᵒᵖ D]
variables [concrete_category.{max v u} D] [preserves_limits (forget D)]
variables [∀ (X : C), preserves_colimits_of_shape (J.cover X)ᵒᵖ (forget D)]
variables [reflects_isomorphisms (forget D)]

instance Sheaf_is_abelian [has_finite_limits D] : abelian (Sheaf J D) :=
let adj := sheafification_adjunction J D in abelian_of_adjunction _ _ (as_iso adj.counit) adj

local attribute [instance] preserves_binary_biproducts_of_preserves_binary_products

instance presheaf_to_Sheaf_additive : (presheaf_to_Sheaf J D).additive :=
(presheaf_to_Sheaf J D).additive_of_preserves_binary_biproducts

end abelian

end category_theory

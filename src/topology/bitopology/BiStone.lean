/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import topology.bitopology.hom
import topology.category.Profinite.default

/-!
# BiStone

This defines `BiStone`, the category of bi-Stone spaces.
-/

universe u

open category_theory

/-- The category of bi-Stone spaces. -/
structure BiStone : Type (u + 1) :=
(X : Type.{u})
[is_bitopological_space : bitopological_space X]
[is_bicompact_space : bicompact_space X]
[is_bi_t2_space : bi_t2_space X]
[is_bizero_dim : bizero_dim X]

namespace BiStone

instance : has_coe_to_sort BiStone Type* := ⟨X⟩

attribute [protected] BiStone.X
attribute [instance] BiStone.is_bitopological_space BiStone.is_bicompact_space
  BiStone.is_bi_t2_space BiStone.is_bizero_dim

/-- Construct a bundled `BiStone` from a bi-Hausdorff, bi-compact, bi-zero dimensional
`bitopological_space`. -/
def of (α : Type*) [bitopological_space α] [bicompact_space α] [bi_t2_space α] [bizero_dim α] :
  BiStone := ⟨α⟩

instance : inhabited BiStone := ⟨of pempty⟩

instance large_category : large_category.{u} BiStone :=
{ hom := λ X Y, X →CC Y,
  id := λ X, bicontinuous_map.id X,
  comp := λ X Y Z f g, g.comp f,
  id_comp' := λ X Y, bicontinuous_map.comp_id,
  comp_id' := λ X Y, bicontinuous_map.id_comp,
  assoc' := λ W X Y Z _ _ _, bicontinuous_map.comp_assoc _ _ _ }

instance concrete_category : concrete_category BiStone :=
{ forget := ⟨coe_sort, λ X Y, coe_fn, λ X, rfl, λ X Y Z f g, rfl⟩,
  forget_faithful := ⟨λ X Y, by convert fun_like.coe_injective⟩ }

-- /-- Constructs an equivalence between bi-Stone spaces from a bihomeomorphism between them. -/
-- @[simps] def iso.mk {α β : BiStone.{u}} (e : α ≃CC β) : α ≅ β :=
-- { hom := e,
--   inv := e.symm,
--   hom_inv_id' := by { ext, exact e.symm_apply_apply x },
--   inv_hom_id' := by { ext, exact e.apply_symm_apply x } }

end BiStone

instance Profinite.has_forget_to_BiStone : has_forget₂ Profinite BiStone :=
{ forget₂ := { obj := λ X, ⟨X⟩, map := λ X Y f, f },
  forget_comp := rfl }

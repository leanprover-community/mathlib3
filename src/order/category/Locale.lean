/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Frame
import topology.category.Top.basic
import topology.opens

/-!
# The category of locales

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

universes u

open category_theory opposite order topological_space

/-- The category of locales. -/
@[derive large_category] def Locale := Frameᵒᵖ

namespace Locale

instance : has_coe_to_sort Locale Type* := ⟨λ X, X.unop⟩
instance (X : Locale) : frame X := X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type*) [frame α] : Locale := op $ Frame.of α

instance : inhabited Locale := ⟨of punit⟩

end Locale

instance {α : Type*} [topological_space α] : frame (opens α) :=
{ inf_Sup_le_supr_inf := λ a s, begin
    sorry
  end, ..opens.complete_lattice }

/-- Strengthening of `topological_space.opens.comap`. -/
def comap' {α β : Type*} [topological_space α] [topological_space β] (f : C(α, β)) :
  frame_hom (opens β) (opens α) :=
{ to_fun := λ s, ⟨f ⁻¹' s, s.2.preimage f.continuous⟩,
  map_Sup' := λ s, opens.ext $ by simp only [opens.Sup_s, set.sUnion_image, set.preimage_Union,
    subtype.coe_mk, set.mem_image, set.Union_exists, set.bUnion_and', set.Union_Union_eq_right],
  map_inf' := λ a b, opens.ext $ by simp only [opens.coe_inf, set.inf_eq_inter, set.preimage_inter,
    opens.mk_inf_mk]}

@[simp] lemma comap'_id {α : Type*} [topological_space α] :
  comap' (continuous_map.id : C(α, α)) = frame_hom.id _ :=
by { ext, refl }

/-- The forgetful functor from `Top` to `Locale` which forgets that the space "has enough points".
-/
def Top_to_Locale : Top ⥤ Locale :=
{ obj := λ X, Locale.of (opens X),
  map := λ X Y f, quiver.hom.op (comap' f),
  map_id' := λ X, quiver.hom.unop_inj comap'_id,
  map_comp' := λ X Y Z f g, rfl }

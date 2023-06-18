/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.category.Frm

/-!
# The category of locales

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `Locale`, the category of locales. This is the opposite of the category of frames.
-/

universes u

open category_theory opposite order topological_space

/-- The category of locales. -/
@[derive large_category] def Locale := Frmᵒᵖ

namespace Locale

instance : has_coe_to_sort Locale Type* := ⟨λ X, X.unop⟩
instance (X : Locale) : frame X := X.unop.str

/-- Construct a bundled `Locale` from a `frame`. -/
def of (α : Type*) [frame α] : Locale := op $ Frm.of α

@[simp] lemma coe_of (α : Type*) [frame α] : ↥(of α) = α := rfl

instance : inhabited Locale := ⟨of punit⟩

end Locale

/-- The forgetful functor from `Top` to `Locale` which forgets that the space has "enough points".
-/
@[simps] def Top_to_Locale : Top ⥤ Locale := Top_op_to_Frame.right_op

-- Note, `CompHaus` is too strong. We only need `t0_space`.
instance CompHaus_to_Locale.faithful : faithful (CompHaus_to_Top ⋙ Top_to_Locale.{u}) :=
⟨λ X Y f g h, by { dsimp at h, exact opens.comap_injective (quiver.hom.op_inj h) }⟩

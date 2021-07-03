/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Adam Topaz
-/
import category_theory.preadditive
import category_theory.preadditive.additive_functor
import data.equiv.transfer_instance

/-!
# If `C` is preadditive, `Cᵒᵖ` has a natural preadditive structure.

-/

open opposite

namespace category_theory

variables (C : Type*) [category C] [preadditive C]

instance : preadditive Cᵒᵖ :=
{ hom_group := λ X Y, equiv.add_comm_group (op_equiv X Y),
  add_comp' := λ X Y Z f f' g,
    congr_arg quiver.hom.op (preadditive.comp_add _ _ _ g.unop f.unop f'.unop),
  comp_add' := λ X Y Z f g g',
    congr_arg quiver.hom.op (preadditive.add_comp _ _ _ g.unop g'.unop f.unop), }

@[simp] lemma unop_zero (X Y : Cᵒᵖ) : (0 : X ⟶ Y).unop = 0 := rfl
@[simp] lemma unop_add {X Y : Cᵒᵖ} (f g : X ⟶ Y) : (f + g).unop = f.unop + g.unop := rfl

variables {C} {D : Type*} [category D] [preadditive D]

instance functor.op_additive (F : C ⥤ D) [F.additive] : F.op.additive := {}

instance functor.right_op_additive (F : Cᵒᵖ ⥤ D) [F.additive] : F.right_op.additive :=
{ map_zero' := λ X Y, begin
    change (F.map 0).op = 0,
    rw functor.map_zero,
    refl,
  end,
  map_add' := λ X Y f g, begin
    change (F.map (f.op + g.op)).op = _,
    rw functor.map_add,
    refl,
  end }

instance functor.left_op_additive (F : C ⥤ Dᵒᵖ) [F.additive] : F.left_op.additive := {}

instance functor.unop_additive (F : Cᵒᵖ ⥤ Dᵒᵖ) [F.additive] : F.unop.additive :=
{ map_zero' := λ X Y, begin
    change (F.map 0).unop = 0,
    rw functor.map_zero,
    refl,
  end,
  map_add' := λ X Y f g, begin
    change (F.map (f.op + g.op)).unop = _,
    rw F.map_add,
    refl,
  end }

end category_theory

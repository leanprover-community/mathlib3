/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.preadditive
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

end category_theory

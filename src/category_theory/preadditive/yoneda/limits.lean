/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.preadditive.yoneda.basic
import algebra.category.Module.abelian

/-!
# The Yoneda embedding for preadditive categories preserves limits

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The Yoneda embedding for preadditive categories preserves limits.

## Implementation notes

This is in a separate file to avoid having to import the development of the abelian structure on
`Module` in the main file about the preadditive Yoneda embedding.

-/

universes v u

open category_theory.preadditive opposite category_theory.limits

noncomputable theory

namespace category_theory

variables {C : Type u} [category.{v} C] [preadditive C]

instance preserves_limits_preadditive_yoneda_obj (X : C) :
  preserves_limits (preadditive_yoneda_obj X) :=
have preserves_limits (preadditive_yoneda_obj X ⋙ forget _),
  from (infer_instance : preserves_limits (yoneda.obj X)),
by exactI preserves_limits_of_reflects_of_preserves _ (forget _)

instance preserves_limits_preadditive_coyoneda_obj (X : Cᵒᵖ) :
  preserves_limits (preadditive_coyoneda_obj X) :=
have preserves_limits (preadditive_coyoneda_obj X ⋙ forget _),
  from (infer_instance : preserves_limits (coyoneda.obj X)),
by exactI preserves_limits_of_reflects_of_preserves _ (forget _)

instance preserves_limits_preadditive_yoneda.obj (X : C) :
  preserves_limits (preadditive_yoneda.obj X) :=
show preserves_limits (preadditive_yoneda_obj X ⋙ forget₂ _ _), from infer_instance

instance preserves_limits_preadditive_coyoneda.obj (X : Cᵒᵖ) :
  preserves_limits (preadditive_coyoneda.obj X) :=
show preserves_limits (preadditive_coyoneda_obj X ⋙ forget₂ _ _), from infer_instance

end category_theory

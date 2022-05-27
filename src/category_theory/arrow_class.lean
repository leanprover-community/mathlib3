/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.arrow

/-!

# Classes of arrows in a category

If `C` is a category, an `arrow_class C` is a class of arrows in C. It is
implemented here as `set (arrow C)`.

If `W : arrow_class C`, and `f : X ⟶ Y` is a morphism in `C`, `W f` is the
condition that `arrow.mk f` belongs to `W`.

-/

noncomputable theory

namespace category_theory

variables (C : Type*) [category C] {D : Type*} [category D]

/-- An `arrow_class C` is a class of arrows in a category `C`. -/
abbreviation arrow_class := set (arrow C)

instance : has_coe_to_fun (arrow_class C) (λ F, (Π ⦃X Y : C⦄, (X ⟶ Y) → Prop)) :=
⟨λ F X Y f, arrow.mk f ∈ F⟩

variable {C}

namespace arrow_class

/-- If `W : arrow_class C` and `F : C ⥤ D` is a functor, then `W.is_inverted_by F`
means that all morphisms in `W` are sent to isomorphisms in `D`. -/
def is_inverted_by (W : arrow_class C) (F : C ⥤ D) : Prop :=
∀ (f : W), f.val.is_inverted_by F

end arrow_class

end category_theory

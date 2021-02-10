/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.adjunction
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.preserves.limits
import category_theory.limits.shapes.terminal
import category_theory.limits.types

namespace category_theory
open limits

def elements.initial2 (A : C) : (coyoneda.obj (op A)).elements :=
⟨A, 𝟙 _⟩

def is_initial2 (A : C) : is_initial (elements.initial2 A) :=
{ desc := λ s, ⟨s.X.2, category.id_comp _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.initial2],
    simp,
  end }

end category_theory

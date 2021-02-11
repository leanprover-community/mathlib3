/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.elements
import category_theory.limits.functor_category
import category_theory.limits.preserves.limits
import category_theory.limits.shapes.terminal

namespace category_theory
open limits opposite

universes v u
variables {C : Type u} [category.{v} C]

def elements.initial (A : C) : (coyoneda.obj (op A)).elements :=
⟨A, 𝟙 _⟩

def elements.is_initial (A : C) : is_initial (elements.initial A) :=
{ desc := λ s, ⟨s.X.2, category.id_comp _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.initial],
    simp,
  end }

/--
The initial object in the category of elements for a representable functor. In `is_initial` it is
shown that this is initial.
-/
def elements.yoneda_initial (A : C) : (yoneda.obj A).elements :=
⟨opposite.op A, 𝟙 _⟩

/--
Show that `elements.initial A` is initial in the category of elements for the `yoneda` functor.
-/
def elements.yoneda_is_initial (A : C) : is_initial (elements.yoneda_initial A) :=
{ desc := λ s, ⟨s.X.2.op, category.comp_id _⟩,
  uniq' := λ s m w,
  begin
    simp_rw ← m.2,
    dsimp [elements.yoneda_initial],
    simp,
  end }

end category_theory

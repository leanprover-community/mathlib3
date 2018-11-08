-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

import category_theory.types
import category_theory.isomorphism
import category_theory.whiskering

namespace category_theory

universes u₁ v₁ u₂ v₂ u₃ v₃
variables {A : Type u₁} [𝒜 : category.{u₁ v₁} A]
variables {B : Type u₂} [ℬ : category.{u₂ v₂} B]
variables {T : Type u₃} [𝒯 : category.{u₃ v₃} T]
include 𝒜 ℬ 𝒯

structure comma (L : A ⥤ T) (R : B ⥤ T) :=
(left : A . obviously)
(right : B . obviously)
(hom : L left ⟶ R right)

variables {L : A ⥤ T} {R : B ⥤ T}

structure comma_morphism (X Y : comma L R) :=
(left : X.left ⟶ Y.left . obviously)
(right : X.right ⟶ Y.right . obviously)
(w' : L.map left ≫ Y.hom = X.hom ≫ R.map right . obviously)

restate_axiom comma_morphism.w'

namespace comma_morphism
@[extensionality] lemma ext
  {X Y : comma L R} {f g : comma_morphism X Y}
  (l : f.left = g.left) (r : f.right = g.right) : f = g :=
begin
  cases f, cases g,
  congr; assumption
end
end comma_morphism

instance comma_category : category (comma L R) :=
{ hom := comma_morphism,
  id := λ X,
  { left := 𝟙 X.left,
    right := 𝟙 X.right },
  comp := λ X Y Z f g,
  { left := f.left ≫ g.left,
    right := f.right ≫ g.right,
    w' :=
    begin
      rw [functor.map_comp,
          category.assoc,
          g.w,
          ←category.assoc,
          f.w,
          functor.map_comp,
          category.assoc],
    end }}

end category_theory

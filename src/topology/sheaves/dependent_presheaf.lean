import category_theory.category.Cat
import category_theory.eq_to_hom

universe u

open category_theory

variables {C D : Type*} [category C] [category D]
variables (F : C ⥤ Cat)

structure grothendieck :=
(base : C)
(fiber : (F.obj base).1)

namespace grothendieck

variables {F}

structure hom (X Y : grothendieck F) :=
(base : X.base ⟶ Y.base)
(fiber : (F.map base).obj X.fiber ⟶ Y.fiber)

@[ext] lemma ext {X Y : grothendieck F} (f g : hom X Y)
  (w_base : f.base = g.base) (w_fiber : eq_to_hom (by rw w_base) ≫ f.fiber = g.fiber) : f = g :=
begin
  cases f; cases g,
  congr,
  dsimp at w_base,
  induction w_base,
  refl,
  dsimp at w_base,
  induction w_base,
  simpa using w_fiber,
end

@[simps]
def id (X : grothendieck F) : hom X X :=
{ base := 𝟙 X.base,
  fiber := eq_to_hom (by erw [category_theory.functor.map_id, functor.id_obj X.fiber]), }

@[simps]
def comp {X Y Z : grothendieck F} (f : hom X Y) (g : hom Y Z) : hom X Z :=
{ base := f.base ≫ g.base,
  fiber :=
  eq_to_hom (by erw [functor.map_comp, functor.comp_obj]) ≫
    (F.map g.base).map f.fiber ≫ g.fiber, }

end grothendieck

instance : category (grothendieck F) :=
{ hom := λ X Y, grothendieck.hom X Y,
  id := λ X, grothendieck.id X,
  comp := λ X Y Z f g, grothendieck.comp f g,
  comp_id' := λ X Y f, begin tidy?, end, -- DTT hell. Probably if we move those eq_to_hom's to the other side?
  id_comp' := sorry,
  assoc' := sorry, }

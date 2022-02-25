import category_theory.over
import category_theory.limits.shapes.pullbacks

universes u₀ v₀

noncomputable theory

namespace category_theory

open limits

variables {C : Type u₀} [category.{v₀} C] [has_pullbacks C] (W X Y Z : C)

section pullback

variables {X Y} (g : X ⟶ Y)

/-- The `pullback_functor` on objects-/
@[simp] def pullback_functor_obj (E : over Y) : over X :=
over.mk (pullback.fst : (pullback g E.hom) ⟶ X)

/-
Consider the cone over the diagram     X ----> Y <---- E₁.left

                     pullback.snd          h.left
  pullback g E₀.hom -------------> E₀.left -----> E₁.left
        |                                           |
        | pullback.fst                              |
        V                                           |
        X ----------------------------------------> Y

The universal property of `pullback g E₁.hom` gives the below definition
-/
/-- The `pullback_functor` on morphisms, as a morphism in the category-/
@[simp] def pullback_functor_map_mk_map {E₀ E₁ : over Y} (h : E₀ ⟶ E₁) :
  (pullback_functor_obj g E₀).left ⟶ (pullback_functor_obj g E₁).left :=
limits.pullback.lift (pullback.fst : pullback g E₀.hom ⟶ X) (pullback.snd ≫ h.left)
(by { simp only [pullback.condition, category.assoc], congr, exact (over.w h).symm })

/-- The `pullback_functor` on morphisms -/
@[simp] def pullback_functor_map (E₀ E₁ : over Y) (h : E₀ ⟶ E₁) :
  pullback_functor_obj g E₀ ⟶ pullback_functor_obj g E₁ :=
over.hom_mk (pullback_functor_map_mk_map g h)
(by { dsimp, simp [limits.pullback.lift_fst] })

/-- Pullback as a functor between over categories -/
def pullback_functor {X Y : C} (g : X ⟶ Y) :
  over Y ⥤ over X :=
{ obj := λ E, over.mk (pullback.fst : (pullback g E.hom) ⟶ X),
  map := pullback_functor_map g }

notation g `^*`:40 := pullback_functor g

end pullback
/--
The data of a polynomial functor expressed as morphisms in a category with adjunction conditions.

     f     g     h
  W ←- X -→ Y -→ Z

The functor in question is then between over categories

         f^*                 Πg                        Σh
      (pullback)    (right adjoint to g^*)  (left adjoint to h^*)
  C/W   =====⥤  C/X      ========⥤      C/Y    =========⥤    C/Z
-/
structure polynomial :=
(f : X ⟶ W)
(g : X ⟶ Y)
(g_left : is_left_adjoint (g^*))
(h : Y ⟶ Z)
(h_right : is_right_adjoint (h^*))

namespace polynomial

variables {W X Y Z} (P : polynomial W X Y Z)

/-- The right adjoint to g^* from the polynomial. This is Πg in the literature -/
def g_right : over X ⥤ over Y := @is_left_adjoint.right _ _ _ _ (P.g^*) P.g_left

/-- The left adjoint to h^* from the polynomial. This is Σg in the literature -/
def h_left : over Y ⥤ over Z := @is_right_adjoint.left _ _ _ _ (P.h^*) P.h_right

/-- The polynomial functor associated to the data of `category_theory.polynomial` -/
def functor : over W ⥤ over Z := P.f^* ⋙ P.g_right ⋙ P.h_left

end polynomial


end category_theory



-- #check category_theory.pullback_functor_map_mk_map

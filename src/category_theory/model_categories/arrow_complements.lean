-- This entire file should eventualy probably be put in arrow.lean!
-- Further generalities about the arrow category.
-- Eventual goals: show the arrow category has (co)limits
-- Pass adjunctions between categories to ones between arrow categories.

import category_theory.category
import category_theory.arrow
import category_theory.functor
import category_theory.adjunction.basic

universes v v' u u'

namespace category_theory

open category_theory

variables {C : Type u} [category.{v} C]
variables {D : Type u'} [category.{v'} D]

/-- -/
def adjunction_arrows (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G)
  {f : arrow C} {g : arrow D}
  (r : (F.map_arrow.obj f) ⟶ g) : (f ⟶ (G.map_arrow.obj g)) :=
begin
  let left := (adj.hom_equiv f.left g.left) r.left,
  let right := (adj.hom_equiv f.right g.right) r.right,
  have w' : left ≫ (G.map_arrow.obj g).hom = f.hom ≫ right := begin
    have s := adjunction.hom_equiv_naturality_right_symm adj left g.hom,

    tidy,
    sorry,
  end,
  apply arrow.hom_mk,
  exact w',
end


/-- An adjunction yields an adjunction between the arrow categories. -/
def adjunction_arrow_category (F : C ⥤ D) (G : D ⥤ C) (adj : F ⊣ G) :
  functor.map_arrow F ⊣ functor.map_arrow G :=
category_theory.adjunction.mk_of_hom_equiv {
  hom_equiv := λ f g,
  begin
    fconstructor,
    { intro r, -- r : F f ⟶ g
      --have :
      --let adj_r :=
      --let  h : r.left ≫ g.hom = (F.map_arrow.obj f).hom ≫ r.right := arrow.w r,
      --let  m := arrow.hom_mk _,-- h,
/-      def hom_mk {f g : arrow T} {u : f.left ⟶ g.left} {v : f.right ⟶ g.right}
  (w : u ≫ g.hom = f.hom ≫ v) : f ⟶ g :=
-/
      --exact arrow.hom_mk
      sorry,
    }
  end,
  lifting_adjunction := begin
    sorry
  end,
}

end category_theory

end category_theory

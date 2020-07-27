/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import category_theory.comma
import topology.simplicial.singular
import topology.category.Top

/-! # Geometric realization of simplicial types -/

universe variables u

open category_theory category_theory.limits

namespace sType
open Top function

structure is_realization (S : sType.{u}) (Y : Top.{u}) :=
(hom : S ⟶ singular.obj Y)
(w   : ∀ X, bijective (λ f : Y ⟶ X, hom ≫ singular.map f))

lemma singular_standard_simplex_is_realization (n : NonemptyFinLinOrd) :
  is_realization (standard_simplex.obj n) (singular_standard_simplex.obj n) :=
{ hom :=
  begin
    dsimp [singular, functor.comp_left],
    -- refine ((yoneda_lemma _).hom).app _,
  end,
  w   := _ }

open simplex_category opposite

def category_of_simplices (X : sType.{u}) : Type u :=
Σ (n : simplex_category), (skeletal_functor.{u}.op ⋙ X).obj (op n)

-- The following definition has universe issues
-- Σ (n : simplex_category), (skeletal_functor.{u}.op ⋙ X).obj (op n)

namespace category_of_simplices
variables (X : sType.{u})

-- slow, sigh
-- instance : small_category (category_of_simplices X) :=
-- { hom := λ s t, ulift { f : s.1 ⟶ t.1 // (skeletal_functor.{u}.op ⋙ X).map f.op t.2 = s.2 },
--   id := λ s, ⟨⟨𝟙 _, by tidy⟩⟩,
--   comp := λ _ _ _ f g, ⟨⟨f.down.1 ≫ g.down.1, by tidy⟩⟩ }

end category_of_simplices

set_option pp.universes true

#print category_of_simplices.category

-- def realization_obj (X : sType.{u}) : Top.{u} :=
-- begin
--   refine colimit _,
-- end

/-- The geometric realization of a simplicial type.
This functor is left adjoint to `Top.singular`. -/
@[simps]
def realization : sType.{u} ⥤ Top.{u} :=
{ obj := λ X, by extract_goal realization_obj,
  map := _,
  map_id' := _,
  map_comp' := _ }


end sType

/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_set

/-!

# The nerve of a category

This file provides the definition of the nerve of a category `C`,
which is a simplicial set `nerve C` (see [goerss-jardine-2009], Example I.1.4).

## References
* [Paul G. Goerss, John F. Jardine, *Simplical Homotopy Theory*][goerss-jardine-2009]

-/

open category_theory.category

universes v u

namespace category_theory

/-- The nerve of a category -/
@[simps]
def nerve (C : Type u) [category.{v} C] : sSet.{max u v} :=
{ obj := λ Δ, (simplex_category.to_Cat.obj Δ.unop) ⥤ C,
  map := λ Δ₁ Δ₂ f, ((whiskering_left _ _ _).obj (simplex_category.to_Cat.map f.unop)).obj,
  map_id' := λ Δ, begin
    erw functor.map_id,
    ext A,
    apply category_theory.functor.ext,
    { intros X Y f,
      erw [id_comp, comp_id],
      refl, },
    { intro X,
      refl, },
  end, }

instance {C : Type*} [category C] {Δ : simplex_categoryᵒᵖ} : category ((nerve C).obj Δ) :=
(infer_instance : category ((simplex_category.to_Cat.obj Δ.unop) ⥤ C))

/-- The nerve of a category, as a functor `Cat ⥤ sSet` -/
@[simps]
def nerve_functor : Cat ⥤ sSet :=
{ obj := λ C, nerve C,
  map := λ C C' F,
  { app := λ Δ, ((whiskering_right _ _ _).obj F).obj, },
  map_id' := λ C, begin
    ext Δ F,
    apply category_theory.functor.ext,
    { intros X Y f,
      simpa only [eq_to_hom_refl, id_comp, comp_id], },
    { intro X,
      refl, },
  end, }

end category_theory

/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.simplicial_set

/-!

# The nerve of a category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
  map := λ Δ₁ Δ₂ f x, simplex_category.to_Cat.map f.unop ⋙ x,
  map_id' := λ Δ, begin
    rw [unop_id, functor.map_id],
    ext x,
    apply functor.id_comp,
  end, }

instance {C : Type*} [category C] {Δ : simplex_categoryᵒᵖ} : category ((nerve C).obj Δ) :=
(infer_instance : category ((simplex_category.to_Cat.obj Δ.unop) ⥤ C))

/-- The nerve of a category, as a functor `Cat ⥤ sSet` -/
@[simps]
def nerve_functor : Cat ⥤ sSet :=
{ obj := λ C, nerve C,
  map := λ C C' F,
  { app := λ Δ x, x ⋙ F, },
  map_id' := λ C, begin
    ext Δ x,
    apply functor.comp_id,
  end, }

end category_theory

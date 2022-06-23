/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import algebra.category.Module.abelian

/-!
# Fully abelian categories

We say that a category `C` is fully abelian if any small full exact abelian subcategory of `C`
admits a fully faithful and exact embedding into the category of `R` modules for a suitable ring
`R`.

-/

open category_theory

universes v u

namespace category_theory.abelian
variables {C : Type u} [category.{v} C] [abelian C]

-- TODO: Exactness
/-- An embedding of a subcategory into a category of modules. -/
structure Module_embedding {D : Type v} [small_category D] (F : D ⥤ C) :=
(R : Type v)
(R_ring : ring R)
(embedding : C ⥤ Module.{v} R)
(faithful : faithful embedding)
(full : full (F ⋙ embedding))

section
variables (C)

/-- We say that a category is fully abelian if every small full exact abelian subcategory admits
    an embedding into a category of modules. -/
class fully_abelian :=
(embedding : Π {D : Type v} [small_category D] [abelian D] (F : D ⥤ C) [full F] [faithful F],
  Module_embedding F)

end

end category_theory.abelian
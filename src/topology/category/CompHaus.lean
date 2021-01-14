/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import topology.category.Top

/-!

# The category of Compact Hausdorff Spaces

We construct the category of compact Hausdorff spaces.
The type of compact Hausdorff spaces is denoted `CompHaus`, and it is endowed with a category
instance making it a full subcategory of `Top`.
The fully faithful functor `CompHaus ⥤ Top` is denoted `CompHaus_to_Top`.

**Note:** The file `topology/category/Compactum.lean` provides the equivalence between `Compactum`,
which is defined as the category of algebras for the ultrafilter monad, and `CompHaus`.
`Compactum_to_CompHaus` is the functor from `Compactum` to `CompHaus` which is proven to be an
equivalence of categories in `Compactum_to_CompHaus.is_equivalence`.
See `topology/category/Compactum.lean` for a more detailed discussion where these definitions are
introduced.

-/

open category_theory

/-- The type of Compact Hausdorff topological spaces. -/
structure CompHaus :=
(to_Top : Top)
[is_compact : compact_space to_Top]
[is_hausdorff : t2_space to_Top]

namespace CompHaus

instance : inhabited CompHaus := ⟨{to_Top := { α := pempty }}⟩

instance : has_coe_to_sort CompHaus := ⟨Type*, λ X, X.to_Top⟩
instance {X : CompHaus} : compact_space X := X.is_compact
instance {X : CompHaus} : t2_space X := X.is_hausdorff

instance category : category CompHaus := induced_category.category to_Top

@[simp]
lemma coe_to_Top {X : CompHaus} : (X.to_Top : Type*) = X :=
rfl

end  CompHaus

/-- The fully faithful embedding of `CompHaus` in `Top`. -/
@[simps, derive [full, faithful]]
def CompHaus_to_Top : CompHaus ⥤ Top := induced_functor _

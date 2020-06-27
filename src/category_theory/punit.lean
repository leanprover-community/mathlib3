/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.const
import category_theory.discrete_category

universes v u -- declare the `v`'s first; see `category_theory.category` for an explanation

namespace category_theory

namespace functor
variables (C : Type u) [category.{v} C]

/-- The constant functor sending everything to `punit.star`. -/
@[simps]
def star : C ⥤ discrete punit :=
{ obj := λ _, punit.star,
  map := λ _ _ _, 𝟙 _ }

variable {C}
/-- Any two functors to `discrete punit` are isomorphic. -/
def punit_ext (F G : C ⥤ discrete punit) : F ≅ G :=
nat_iso.of_components (λ _, eq_to_iso dec_trivial) (λ _ _ _, dec_trivial)

end functor

end category_theory

import category_theory.enriched.enriched_over
import algebra.category.Module.monoidal

universes u

open category_theory

namespace Module

instance : concrete_monoidal_category (Module ℤ) :=
{ lax_monoidal :=
  { ε := sorry,
    μ := λ G H, sorry,
    μ_natural' := λ X Y X' Y' f g, sorry,
    associativity' := λ X Y Z, sorry, }}

example : enriched_over (Module ℤ) (Module ℤ) :=
{ e_hom := λ X Y, Module.of ℤ (X ⟶ Y),
  e_id := λ X, sorry,
  e_comp := λ X Y Z p, sorry,
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end AddCommGroup

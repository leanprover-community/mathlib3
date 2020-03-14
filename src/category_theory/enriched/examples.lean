import category_theory.enriched.enriched_over
import algebra.category.Module.monoidal

universes u

open category_theory

namespace Module

set_option pp.notation false
set_option pp.implicit true
instance : concrete_monoidal_category (Module ℤ) :=
{ lax_monoidal :=
  { ε := λ x, (1 : ℤ), -- err, 0, or 1?
    μ := λ G H p,
    -- oh dear...
    ((limits.prod.fst : ((forget (Module ℤ)).obj G) ⨯ ((forget (Module ℤ)).obj H) ⟶ ((forget (Module ℤ)).obj G)) p) ⊗ₜ
    ((limits.prod.snd : ((forget (Module ℤ)).obj G) ⨯ ((forget (Module ℤ)).obj H) ⟶ ((forget (Module ℤ)).obj H)) p),
    μ_natural' := λ X Y X' Y' f g, sorry,
    associativity' := λ X Y Z, sorry,
    left_unitality' := λ X, begin ext, dsimp,  end,
    right_unitality' := sorry, }}

example : enriched_over (Module ℤ) (Module ℤ) :=
{ e_hom := λ X Y, Module.of ℤ (X ⟶ Y),
  e_id := λ X, sorry,
  e_comp := λ X Y Z p, sorry,
  e_hom_forget := λ X Y, equiv.refl _ }

-- TODO modules over a ring are enriched over themselves
-- TODO deduce from this that they are enriched over AddCommGroup

end AddCommGroup

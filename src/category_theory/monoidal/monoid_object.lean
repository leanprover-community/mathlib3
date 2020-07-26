import category_theory.monoidal.braided

/-!
# (Commutative) monoid objects in (braided) monoidal categories

The basic definitions of (commutative) monoid objects in (braided) monoidal categories,
and instances of the categories they themselves form.
-/

open category_theory

universes u v

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

structure Mon_ :=
(X          : C)
(ι          : 𝟙_ C ⟶ X)
(μ          : X ⊗ X ⟶ X)
(left_unit  : (ι ⊗ 𝟙 X) ≫ μ = (λ_ X).hom)
(right_unit : (𝟙 X ⊗ ι) ≫ μ = (ρ_ X).hom)
(μ_assoc    : (α_ X X X).hom ≫ (𝟙 X ⊗ μ) ≫ μ = (μ ⊗ 𝟙 X) ≫ μ)

namespace Mon_

variable {C}

@[ext]
structure hom (M N : Mon_ C) :=
(hom : M.X ⟶ N.X)
(ι_hom' : M.ι ≫ hom = N.ι . obviously)
(μ_hom' : M.μ ≫ hom = (hom ⊗ hom) ≫ N.μ . obviously)

restate_axiom hom.ι_hom'
restate_axiom hom.μ_hom'
attribute [simp, reassoc] hom.ι_hom hom.μ_hom

@[simps]
def id (M : Mon_ C) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mon_ C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mon_ C) :=
{
  hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g,
}

end Mon_

variables (D : Type u) [category.{v} D] [monoidal_category.{v} D] [braided_category.{v} D]

structure CommMon_ extends Mon_ D :=
(comm : (β_ X X).hom ≫ μ = μ)

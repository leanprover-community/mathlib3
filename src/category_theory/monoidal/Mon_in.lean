import category_theory.monoidal.category
import algebra.category.Mon.basic
import category_theory.monoidal.types

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

open category_theory.category
open category_theory.functor

namespace category_theory

open monoidal_category

variables (C : Type u₁) [category.{v₁} C] [monoidal_category.{v₁} C]

structure Mon_in :=
(X : C)
(ι : 𝟙_ C ⟶ X)
(μ : X ⊗ X ⟶ X)
(μ_ι : (λ_ X).inv ≫ (ι ⊗ 𝟙 X) ≫ μ = 𝟙 X)
(ι_μ : (ρ_ X).inv ≫ (𝟙 X ⊗ ι) ≫ μ = 𝟙 X)
(μ_assoc : (α_ X X X).hom ≫ (𝟙 X ⊗ μ) ≫ μ = (μ ⊗ 𝟙 X) ≫ μ)

variables {C}

namespace Mon_in

@[ext]
structure hom (M N : Mon_in C) :=
(hom : M.X ⟶ N.X)
(ι_hom' : M.ι ≫ hom = N.ι . obviously)
(μ_hom' : M.μ ≫ hom = (hom ⊗ hom) ≫ N.μ . obviously)

restate_axiom hom.ι_hom'
restate_axiom hom.μ_hom'
attribute [simp, reassoc] hom.ι_hom hom.μ_hom

@[simps]
def id (M : Mon_in C) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mon_in C} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category.{v₁} (Mon_in C) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

-- TODO
-- def equivalence_Mon : Mon_in (Type u₁) ≌ Mon.{u₁} :=
-- { functor :=
--   { obj := λ M, ⟨M.X, { one := as_element M.ι, mul := M.μ, }⟩,
--   }}

/-
TODO

* Construct the category of module objects for a fixed monoid object.
* Check that `Mon_in Type ≌ Mon`.
* Check that `Mon_in Mon ≌ CommMon`, via the Eckmann-Hilton argument.
  (You'll have to hook up the cartesian monoidal structure on `Mon` first.)
* Check that `Mon_in AddCommGroup ≌ Ring`.
  (You'll have to hook up the monoidal structure on `AddCommGroup`.
  Currently we have the monoidal structure on `Module R`; perhaps one could specialize to `R = ℤ`
  and transport the monoidal structure across an equivalence? This sounds like some work!)
* Check that `Mon_in (Module R) ≌ Algebra R`.
* Show that if `C` is braided (you'll have to define that first!)
   then `Mon_in C` is naturally monoidal.
* Can you transport this monoidal structure to `Ring` or `Algebra R`?
  How does it compare to the "native" one?
-/

end Mon_in

end category_theory

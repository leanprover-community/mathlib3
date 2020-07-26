import category_theory.monoidal.category
import algebra.category.CommRing.basic

/-!
# The category of monoids in a monoidal category, and modules over an internal monoid.
-/

universes v u

open category_theory

variables (C : Type u) [category.{v} C] [monoidal_category.{v} C]

structure Mon_ :=
(X : C)
(ι : 𝟙_ C ⟶ X)
(μ : X ⊗ X ⟶ X)
(μ_ι : (λ_ X).inv ≫ (ι ⊗ 𝟙 X) ≫ μ = 𝟙 X)
(ι_μ : (ρ_ X).inv ≫ (𝟙 X ⊗ ι) ≫ μ = 𝟙 X)
(μ_assoc : (α_ X X X).inv ≫ (μ ⊗ 𝟙 X) ≫ μ = (𝟙 X ⊗ μ) ≫ μ)

namespace Mon_

variables {C}

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
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

end Mon_

variables {C}

structure Mod_ (A : Mon_ C) :=
(X : C)
(act : A.X ⊗ X ⟶ X)
(μ_ι : (λ_ X).inv ≫ (A.ι ⊗ 𝟙 X) ≫ act = 𝟙 X)
(μ_assoc : (α_ A.X A.X X).hom ≫ (𝟙 A.X ⊗ act) ≫ act = (A.μ ⊗ 𝟙 X) ≫ act)


namespace Mod_

variables {A : Mon_ C}

@[ext]
structure hom (M N : Mod_ A) :=
(hom : M.X ⟶ N.X)
(act_hom' : M.act ≫ hom = (𝟙 A.X ⊗ hom) ≫ N.act . obviously)

restate_axiom hom.act_hom'
attribute [simp, reassoc] hom.act_hom

@[simps]
def id (M : Mod_ A) : hom M M :=
{ hom := 𝟙 M.X, }

@[simps]
def comp {M N O : Mod_ A} (f : hom M N) (g : hom N O) : hom M O :=
{ hom := f.hom ≫ g.hom, }

instance : category (Mod_ A) :=
{ hom := λ M N, hom M N,
  id := id,
  comp := λ M N O f g, comp f g, }

end Mod_

/-!
Bonus projects (all but the first will be non-trivial with today's mathlib):
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

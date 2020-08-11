/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.functor_category
import category_theory.concrete_category.bundled

namespace category_theory
open category

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C]

/--
The data of a monad on C consists of an endofunctor T together with natural transformations
η : 𝟭 C ⟶ T and μ : T ⋙ T ⟶ T satisfying three equations:
- T μ_X ≫ μ_X = μ_(TX) ≫ μ_X (associativity)
- η_(TX) ≫ μ_X = 1_X (left unit)
- Tη_X ≫ μ_X = 1_X (right unit)
-/
class monad (T : C ⥤ C) :=
(η [] : 𝟭 _ ⟶ T)
(μ [] : T ⋙ T ⟶ T)
(assoc' : ∀ X : C, T.map (nat_trans.app μ X) ≫ μ.app _ = μ.app (T.obj X) ≫ μ.app _ . obviously)
(left_unit' : ∀ X : C, η.app (T.obj X) ≫ μ.app _ = 𝟙 _  . obviously)
(right_unit' : ∀ X : C, T.map (η.app X) ≫ μ.app _ = 𝟙 _  . obviously)

variable (C)
/-- bundled monads. -/
structure Monad :=
(func : C ⥤ C)
(str : monad func . tactic.apply_instance)
variable {C}

restate_axiom monad.assoc'
restate_axiom monad.left_unit'
restate_axiom monad.right_unit'
attribute [simp] monad.left_unit monad.right_unit

notation `η_` := monad.η
notation `μ_` := monad.μ

/--
The data of a comonad on C consists of an endofunctor G together with natural transformations
ε : G ⟶ 𝟭 C and δ : G ⟶ G ⋙ G satisfying three equations:
- δ_X ≫ G δ_X = δ_X ≫ δ_(GX) (coassociativity)
- δ_X ≫ ε_(GX) = 1_X (left counit)
- δ_X ≫ G ε_X = 1_X (right counit)
-/
class comonad (G : C ⥤ C) :=
(ε [] : G ⟶ 𝟭 _)
(δ [] : G ⟶ (G ⋙ G))
(coassoc' : ∀ X : C, nat_trans.app δ _ ≫ G.map (δ.app X) = δ.app _ ≫ δ.app _ . obviously)
(left_counit' : ∀ X : C, δ.app X ≫ ε.app (G.obj X) = 𝟙 _ . obviously)
(right_counit' : ∀ X : C, δ.app X ≫ G.map (ε.app X) = 𝟙 _ . obviously)

variable (C)
/-- Bundled comonads. -/
structure CoMonad :=
(func : C ⥤ C)
(str : comonad func . tactic.apply_instance)
variable {C}

restate_axiom comonad.coassoc'
restate_axiom comonad.left_counit'
restate_axiom comonad.right_counit'
attribute [simp] comonad.left_counit comonad.right_counit

notation `ε_` := comonad.ε
notation `δ_` := comonad.δ

namespace monad
instance : monad (𝟭 C) :=
{ η := 𝟙 _,
  μ := 𝟙 _ }
/-- The initial monad. -/
def initial : Monad C := { func := 𝟭 _ }
instance unbundle_monad {M : Monad C} : monad M.func := M.str
instance : inhabited (Monad C) := ⟨initial⟩
end monad

namespace comonad
instance : comonad (𝟭 C) :=
{ ε := 𝟙 _,
  δ := 𝟙 _ }
/-- The terminal comonad. -/
def terminal : CoMonad C := { func := 𝟭 _ }
instance unbundle_comonad {M : CoMonad C} : comonad M.func := M.str
instance : inhabited (CoMonad C) := ⟨terminal⟩
end comonad

section unbundled_monads
variables {M : C ⥤ C} [monad M]
variables {N : C ⥤ C} [monad N]
variables {L : C ⥤ C} [monad L]
variables {K : C ⥤ C} [monad K]
/--
A morphism of monads is a natural transformation which is compatible with `η` and `μ`.
-/
variables (M N)
/-- A morphism of unbundled monads. -/
structure monad_hom extends nat_trans M N :=
(app_η {X} : (η_ M).app X ≫ app X = (η_ N).app X . obviously)
(app_μ {X} : (μ_ M).app X ≫ app X = (M.map (app X) ≫ app (N.obj X)) ≫ (μ_ N).app X . obviously)
attribute [nolint has_inhabited_instance] monad_hom
variables {M N}

namespace monad
variable (M)
/--
The identity morphism on a monad `M`.
-/
def ident : monad_hom M M :=
{ app := λ X, 𝟙 _,
  app_η := by simp,
  app_μ := λ X, by {simp only [auto_param_eq, functor.map_id, comp_id], tidy} }
variable {M}
end monad

namespace monad_hom
@[ext]
theorem ext (f g : monad_hom M N) : f.to_nat_trans = g.to_nat_trans → f = g :=
  by {cases f, cases g, simp}

/--
The composition of morphisms of monads.
-/
def gg (f : monad_hom M N) (g : monad_hom N L) : monad_hom M L :=
{ app := λ X, (f.app X) ≫ (g.app X),
  app_η := λ X, by {rw ←assoc, simp [app_η]},
  app_μ := λ X, by {rw ←assoc, simp [app_μ]} }

@[simp] lemma ident_gg (f : monad_hom M N) : (monad.ident M).gg f = f := by {ext X, apply id_comp}
@[simp] lemma gg_ident (f : monad_hom M N) : f.gg (monad.ident N) = f := by {ext X, apply comp_id}

lemma gg_assoc (f : monad_hom M N) (g : monad_hom N L) (h : monad_hom L K) :
  (f.gg g).gg h = f.gg (g.gg h) := by {ext X, apply assoc}

end monad_hom
end unbundled_monads

section bundled_monads
variables {M : Monad C}
variables {N : Monad C}
variables {L : Monad C}
variables {K : Monad C}

variables (M N)
/-- Morphisms of bundled monads. -/
@[nolint has_inhabited_instance]
def Monad_hom := monad_hom M.func N.func
variables {M N}

instance : category (Monad C) :=
{ hom := Monad_hom,
  id := λ M, monad.ident _,
  comp := λ _ _ _, monad_hom.gg,
  id_comp' := λ _ _, by apply monad_hom.ident_gg,
  comp_id' := λ _ _, by apply monad_hom.gg_ident,
  assoc' := λ _ _ _ _, by apply monad_hom.gg_assoc }

end bundled_monads

end category_theory

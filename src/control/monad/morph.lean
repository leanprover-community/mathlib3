/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import control.functor.morph

/-!
# Morphisms of monads

We define morphisms between monads in the sense of `control.monad.basic`.
These are morphisms of their underlying functors which are compatible with `pure` and `bind`.

We provide a bare bones interface:
1. The composition of two morphisms `η` and `γ` is denoted `η.comp γ`.
2. The identity morphism on a monad `F` is called `monad_morph.ident F`.

We prove some basic lemmas:
1. `monad_morph.ident_comp` resp. `monad_morph.comp_ident` show that the composition of a
  morphism `η` with the identity morphism (in either direction) is `η`.
2. An extensionality `monad_morph.ext` lemma stating that two morphisms are equal if their
  underlying functions are.
3. `monad_morph.comp_assoc` asserts that the composition of functor morphisms is associative.

## Note on universe restrictions

Given two monads `Mᵢ : Type uᵢ → Type vᵢ`, `i = 1, 2`,  we may only consider morphisms
`η : F >~> G` provided that `u₁ = u₂`. This restriction arises from the same restriction on the
underlying functors. See the note on universes in `control.functor.morph`.
Note that there is no restriction on `v₁` and `v₂`.
-/

universes u

/--
A morphism of monads is a morphism of their underlying functors which is
compatible with pure and bind. Use the notation `F >~> G`.
-/
@[nolint has_inhabited_instance]
structure monad_morph (F : Type u → Type*) [monad F] (G : Type u → Type*) [monad G]
  extends (F ~> G) :=
(app_pure {α} {a : α} : app (pure a) = pure a)
(app_bind {α β} {ma : F α} {f : α → F β} : app (ma >>= f) = (app ma) >>= (app ∘ f))
attribute [simp] monad_morph.app_pure monad_morph.app_bind

infixr ` >~> `:10 := monad_morph

namespace monad_morph
variables {F : Type u → Type*} [monad F]
variables {G : Type u → Type*} [monad G]
variables {H : Type u → Type*} [monad H]
variables {I : Type u → Type*} [monad I]

/--
The composition of morphisms of monads.
-/
def comp (γ : G >~> H) (η : F >~> G) : F >~> H :=
{ app_pure := λ _ _, by {change γ.app (η.app _) = _, simp},
  app_bind := λ _ _ _ _, by{ change γ.app (η.app _) = _, simp_rw [app_bind], refl},
  ..show F ~> H, by exact γ.to_functor_morph.comp η.to_functor_morph  }

@[ext]
lemma ext {η γ : F >~> G} : η.to_functor_morph = γ.to_functor_morph → η = γ :=
  by {cases η, cases γ, simp}

variable (F)
/--
The identity morphism of a monad.
-/
def ident : F >~> F :=
{ app_pure := by tauto,
  app_bind := by tauto,
  ..show F ~> F, by exact (functor_morph.ident F) }
variable {F}

@[simp] theorem ident_comp (η : F >~> G) : (ident G).comp η = η := by {ext, finish}
@[simp] theorem comp_ident (η : F >~> G) : η.comp (ident F) = η := by {ext, finish}

theorem comp_assoc (η₁ : H >~> I) (η₂ : G >~> H) (η₃ : F >~> G) :
  (η₁.comp η₂).comp η₃ = η₁.comp (η₂.comp η₃) := by {ext, finish}

def initial [is_lawful_monad F] : id >~> F :=
{ app := λ _, pure,
  naturality := λ _ _ f x, by {change pure (f x) = f <$> pure x, simp},
  app_pure := λ _ _, rfl,
  app_bind := λ α β ma f, by {simp only [pure_bind, function.comp_app], refl} }

@[simp]
theorem initial_unique [is_lawful_monad F] (f : id >~> F) : f = initial :=
  by {ext α x, apply f.app_pure}

end monad_morph

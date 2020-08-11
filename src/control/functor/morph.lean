/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/

import tactic
import control.functor

/-!
# Natural Transformations (Morphisms) of Functors

We define morphisms between functors in the sense of `control.functor`.
These are functions which are compatible with `functor.map` in the obvious sense.

We provide a bare bones interface:
1. The composition of two morphisms `η` and `γ` is denoted `η.comp γ`.
2. The identity morphism on a functor `F` is called `functor_morph.ident F`.

We prove some basic lemmas:
1. `functor_morph.ident_comp` resp. `functor_morph.comp_ident` show that the composition of a
  morphism `η` with the identity morphism (in either direction) is `η`.
2. An extensionality `functor_morph.ext` lemma stating that two morphisms are equal if their
  underlying functions are.
3. `functor_morph.comp_assoc` asserts that the composition of functor morphisms is associative.

## Note on universe restrictions

Given two functors `Fᵢ : Type uᵢ → Type vᵢ`, `i = 1, 2`,  we may only consider morphisms
`η : F ~> G` provided that `u₁ = u₂`.
This is because `η.app` is defined as `Π {α}, F α → G α`, so the universe for the input type for
`F` and `G` must be the same.
However, there is no restriction on `v₁` or `v₂` -- this is in contrast to the natural
transformations appearing in `category_theory.natural_transformation`, where such a restriction is
necessary.
-/

universes u

/--
A morphism of functors, otherwise known as a natural transformation.
Use the notation `F ~> G`.
-/
@[nolint has_inhabited_instance]
structure functor_morph (F : Type u → Type*) [functor F] (G : Type u → Type*) [functor G] :=
(app {α} : F α → G α)
(naturality {α β} {f : α → β} {x : F α} : app (f <$> x) = f <$> app x)
attribute [simp] functor_morph.naturality

infixr ` ~> `:10 := functor_morph

namespace functor_morph

variables {F : Type u → Type*} [functor F]
variables {G : Type u → Type*} [functor G]
variables {H : Type u → Type*} [functor H]
variables {I : Type u → Type*} [functor I]

/--
The composition of two morphisms of functors.
-/
def comp (γ : G ~> H) (η : F ~> G) : F ~> H :=
{ app := λ _ x, γ.app $ η.app x,
  naturality := λ _ _ _ _, by simp }

@[ext]
lemma ext {η γ : F ~> G} : η.app = γ.app → η = γ := by {cases η, cases γ, simp}

variable (F)
/--
The identity morphism of a functor.
-/
def ident : F ~> F :=
{ app := λ _, id,
  naturality := by tauto }
variable {F}

@[simp] theorem ident_comp (η : F ~> G) : (ident G).comp η = η := by {ext, finish}
@[simp] theorem comp_ident (η : F ~> G) : η.comp (ident F) = η := by {ext, finish}

theorem comp_assoc (η₁ : H ~> I) (η₂ : G ~> H) (η₃ : F ~> G) :
  (η₁.comp η₂).comp η₃ = η₁.comp (η₂.comp η₃) := by {ext, finish}

end functor_morph

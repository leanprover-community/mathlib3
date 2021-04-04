/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.set.basic

/-!
# Girard's paradox

Girard's paradox is a proof that `Type : Type` entails a contradiction. We can't say this directly
in lean because `Type : Type 1` and it's not possible to give `Type` a different type via an axiom,
so instead we axiomatize the behavior of the Pi type and application if the typing rule for Pi was
`(Type → Type) → Type` instead of `(Type → Type) → Type 1`.

Furthermore, we don't actually want false axioms in mathlib, so rather than introducing the axioms
using `axiom` or `constant` declarations, we declare a `girard` class, which bundles up the
hypotheses in Girard's paradox, such that an instance of `girard.{u]` asserts that universe `u`
satisfies the assumptions, i.e. `Type u : Type u`, give or take. Then the paradox amounts to a
proof that the `girard` class is empty.

Based on Watkins' LF implementation of Hurkens' simplification of Girard's paradox:
<http://www.cs.cmu.edu/~kw/research/hurkens95tlca.elf>.

## Main statements

* `girard.paradox : girard → false`: there are no Girard universes.
-/

universe u

/-- A "Girard universe", which is a universe `u` such that `Pi : (Type u → Type u) → Type u`.
Since we can't actually change the type of lean's `Π` operator, we define `pi`, `lam`, `app` and
the `beta` rule instead. -/
class girard :=
(pi : (Type u → Type u) → Type u)
(lam {A : Type u → Type u} : (∀ x, A x) → pi A)
(app {A} : pi A → ∀ x, A x)
(beta {A : Type u → Type u} (f : ∀ x, A x) (x) : app (lam f) x = f x)

namespace girard
variable [girard.{u}]

local attribute [simp] girard.beta

/-- Embeds a universe into `Type u`, assuming that universe `u` is a Girard universe. -/
def univ : Type u := pi (λ X, (set (set X) → X) → set (set X))

/-- A diagonal embedding `set (set univ) → univ`, part of the proof. -/
def τ (T : set (set univ)) : univ :=
lam $ λ X f, {p | {x : univ | f (app x _ f) ∈ p} ∈ T}

/-- We can map `univ` to `set (set univ)` using the definition of `univ`. -/
def σ (S : univ) : set (set univ) := app S _ τ

/-- The action of `σ (τ S)` simplifies in terms of `τ (σ x)`. -/
local attribute [simp]
theorem τ_σ_def (s S) : s ∈ σ (τ S) ↔ {x : univ | τ (σ x) ∈ s} ∈ S :=
by simp [σ, τ]

/-- Girard's paradox: there are no Girard universes. -/
theorem paradox : false :=
have ∀ p, (∀ x, p ∈ σ x → x ∈ p) → τ {p | ∀ x : univ, p ∈ σ x → x ∈ p} ∈ p, from
  λ p d, d _ (by simpa using λ x h, d (τ (σ x)) (by simpa)),
this {y | ¬ ∀ p, p ∈ σ y → τ (σ y) ∈ p}
  (λ x e f, f _ e (λ p h, f {y | τ (σ y) ∈ p} (by rwa [τ_σ_def] at h)))
  (λ p h, this {y | τ (σ y) ∈ p} (by simpa using h))

end girard

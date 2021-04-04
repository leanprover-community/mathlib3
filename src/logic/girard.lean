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
hypotheses in Girard's paradox, such that an instance of `girard.{u}` asserts that universe `u`
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

/-- Girard's paradox: there are no Girard universes. -/
theorem paradox (G : girard.{u}) : false :=
let univ := pi (λ X, (set (set X) → X) → set (set X)) in
let τ (T : set (set univ)) : univ :=
  lam $ λ X f, {p | {x : univ | f (app x _ f) ∈ p} ∈ T} in
let σ (S : univ) : set (set univ) := app S _ τ in
have τσ : ∀ s S, s ∈ σ (τ S) ↔ {x | τ (σ x) ∈ s} ∈ S := by simp [σ, τ, beta],
let ω := {p | ∀ x, p ∈ σ x → x ∈ p}, δ (S) := ∀ p, p ∈ S → τ S ∈ p in
have δ ω, from λ p d, d _ (by simpa [τσ] using λ x h, d (τ (σ x)) (by simpa)),
this {y | ¬ δ (σ y)}
  (λ x e f, f _ e (λ p h, f (τ ∘ σ ⁻¹' p) (by rwa [τσ] at h)))
  (λ p h, this (τ ∘ σ ⁻¹' p) (by simpa [τσ] using h))

end girard

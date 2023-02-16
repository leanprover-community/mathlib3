/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import combinatorics.quiver.basic
/-!

# Pushing a quiver structure along a map

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a map `σ : V → W` and a `quiver` instance on `V`, this files defines a `quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/

universes v v₁ v₂ u u₁ u₂

variables {V : Type*} [quiver V] {W : Type*} (σ : V → W)

namespace quiver

/-- The `quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unused_arguments]
def push (σ : V → W) := W

instance [h : nonempty W] : nonempty (push σ) := h

/-- The quiver structure obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint has_nonempty_instance]
inductive push_quiver {V : Type u} [quiver.{v} V] {W : Type u₂} (σ : V → W) :
  W → W → Type (max u u₂ v)
| arrow {X Y : V} (f : X ⟶ Y) : push_quiver (σ X) (σ Y)

instance : quiver (push σ) := ⟨push_quiver σ⟩

namespace push

/-- The prefunctor induced by pushing arrows via `σ` -/
def of : V ⥤q push σ :=
{ obj := σ,
  map := λ X Y f, push_quiver.arrow f }

@[simp] lemma of_obj : (of σ).obj = σ := rfl

variables {W' : Type*} [quiver W'] (φ : V ⥤q W') (τ : W → W') (h : ∀ x, φ.obj x = τ (σ x) )

include φ h
/-- Given a function `τ : W → W'` and a prefunctor `φ : V ⥤q W'`, one can extend `τ` to be
a prefunctor `W ⥤q W'` if `τ` and `σ` factorize `φ` at the level of objects, where `W` is given
the pushforward quiver structure `push σ`. -/
def lift : push σ ⥤q W' :=
{ obj := τ,
  map := @push_quiver.rec V _ W σ
    (λ X Y f, τ X ⟶ τ Y)
    (λ X Y f, by { rw [←h X, ←h Y], exact φ.map f, }) }

lemma lift_obj : (lift σ φ τ h).obj = τ := rfl

lemma lift_comp : of σ ⋙q lift σ φ τ h = φ :=
begin
  fapply prefunctor.ext,
  { rintros, simp only [prefunctor.comp_obj], symmetry, exact h X, },
  { rintros _ _ f, simp only [prefunctor.comp_map],
    apply eq_of_heq,
    iterate 2 { apply (cast_heq _ _).trans },
    symmetry,
    iterate 2 { apply (eq_rec_heq _ _).trans },
    refl, },
end

lemma lift_unique (Φ : push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : of σ ⋙q Φ = φ) :
  Φ = lift σ φ τ h :=
begin
  dsimp only [of,lift],
  fapply prefunctor.ext,
  { rintros, simp_rw [←Φ₀], },
  { rintros _ _ ⟨⟩, subst_vars, simp only [prefunctor.comp_map, cast_eq], refl, }
end

end push

end quiver

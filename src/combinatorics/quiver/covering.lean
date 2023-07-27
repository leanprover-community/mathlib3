/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
import combinatorics.quiver.cast
import combinatorics.quiver.symmetric
import data.sigma.basic
import logic.equiv.basic

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `quiver.star u` is the type of all arrows with source `u`;
* `quiver.costar u` is the type of all arrows with target `u`;
* `prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `prefunctor.is_covering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `quiver.star_path u` is the type of all paths with source `u`;
* `prefunctor.star_path u` is the obvious function `star_path u → star_path (φ.obj u)`.

## Main statements

* `prefunctor.is_covering.path_star_bijective` states that if `φ` is a covering,
  then `φ.star_path u` is a bijection for all `u`.
  In other words, every path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `prefunctor` to `quiver.prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/

open function quiver

universes u v w

variables {U : Type*} [quiver.{u+1} U]
          {V : Type*} [quiver.{v+1} V] (φ : U ⥤q V)
          {W : Type*} [quiver.{w+1} W] (ψ : V ⥤q W)

/-- The `quiver.star` at a vertex is the collection of arrows whose source is the vertex.
The type `quiver.star u` is defined to be `Σ (v : U), (u ⟶ v)`. -/
@[reducible] def quiver.star (u : U) := Σ (v : U), (u ⟶ v)

/-- Constructor for `quiver.star`. Defined to be `sigma.mk`. -/
@[reducible] protected def quiver.star.mk {u v : U} (f : u ⟶ v) : quiver.star u := ⟨_, f⟩

/-- The `quiver.costar` at a vertex is the collection of arrows whose target is the vertex.
The type `quiver.costar v` is defined to be `Σ (u : U), (u ⟶ v)`. -/
@[reducible] def quiver.costar (v : U) := Σ (u : U), (u ⟶ v)

/-- Constructor for `quiver.costar`. Defined to be `sigma.mk`. -/
@[reducible] protected def quiver.costar.mk {u v : U} (f : u ⟶ v) : quiver.costar v := ⟨_, f⟩

/-- A prefunctor induces a map of `quiver.star` at every vertex. -/
@[simps] def prefunctor.star (u : U) : quiver.star u → quiver.star (φ.obj u) :=
λ F, quiver.star.mk (φ.map F.2)

/-- A prefunctor induces a map of `quiver.costar` at every vertex. -/
@[simps] def prefunctor.costar (u : U) : quiver.costar u → quiver.costar (φ.obj u) :=
λ F, quiver.costar.mk (φ.map F.2)

@[simp] lemma prefunctor.star_apply {u v : U} (e : u ⟶ v) :
  φ.star u (quiver.star.mk e) = quiver.star.mk (φ.map e) := rfl

@[simp] lemma prefunctor.costar_apply {u v : U} (e : u ⟶ v) :
  φ.costar v (quiver.costar.mk e) = quiver.costar.mk (φ.map e) := rfl

lemma prefunctor.star_comp (u : U) :
  (φ ⋙q ψ).star u = (ψ.star (φ.obj u)) ∘ ((φ.star) u) := rfl

lemma prefunctor.costar_comp (u : U) :
  (φ ⋙q ψ).costar u = (ψ.costar (φ.obj u)) ∘ ((φ.costar) u) := rfl

/-- A prefunctor is a covering of quivers if it defines bijections on all stars and costars. -/
protected structure prefunctor.is_covering : Prop :=
(star_bijective : ∀ u, bijective (φ.star u))
(costar_bijective : ∀ u, bijective (φ.costar u))

@[simp] lemma prefunctor.is_covering.map_injective (hφ : φ.is_covering) {u v : U} :
  injective (λ (f : u ⟶ v), φ.map f) :=
begin
  rintro f g he,
  have : φ.star u (quiver.star.mk f) = φ.star u (quiver.star.mk g) := by simpa using he,
  simpa using (hφ.star_bijective u).left this,
end

lemma prefunctor.is_covering.comp (hφ : φ.is_covering) (hψ : ψ.is_covering) :
  (φ ⋙q ψ).is_covering :=
⟨λ u, (hψ.star_bijective _).comp (hφ.star_bijective _),
 λ u, (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩

lemma prefunctor.is_covering.of_comp_right (hψ : ψ.is_covering) (hφψ : (φ ⋙q ψ).is_covering) :
  φ.is_covering :=
⟨λ u, (bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
 λ u, (bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩

lemma prefunctor.is_covering.of_comp_left (hφ : φ.is_covering) (hφψ : (φ ⋙q ψ).is_covering)
  (φsur : surjective φ.obj) : ψ.is_covering :=
begin
  refine ⟨λ v, _, λ v, _⟩;
  obtain ⟨u, rfl⟩ := φsur v,
  exacts [(bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
          (bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)],
end

/-- The star of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
star and the costar at `u` in the original quiver. -/
def quiver.symmetrify_star (u : U) :
  quiver.star (symmetrify.of.obj u) ≃ quiver.star u ⊕ quiver.costar u :=
equiv.sigma_sum_distrib _ _

/-- The costar of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
costar and the star at `u` in the original quiver. -/
def quiver.symmetrify_costar (u : U) :
  quiver.costar (symmetrify.of.obj u) ≃ quiver.costar u ⊕ quiver.star u :=
equiv.sigma_sum_distrib _ _

lemma prefunctor.symmetrify_star (u : U) :
  φ.symmetrify.star u = (quiver.symmetrify_star _).symm ∘
    sum.map (φ.star u) (φ.costar u) ∘ quiver.symmetrify_star u :=
begin
  rw equiv.eq_symm_comp,
  ext ⟨v, (f|g)⟩;
  simp [quiver.symmetrify_star],
end

protected lemma prefunctor.symmetrify_costar (u : U) :
  φ.symmetrify.costar u = (quiver.symmetrify_costar _).symm ∘
    sum.map (φ.costar u) (φ.star u) ∘ quiver.symmetrify_costar u :=
begin
  rw equiv.eq_symm_comp,
  ext ⟨v, (f|g)⟩;
  simp [quiver.symmetrify_costar],
end

protected lemma prefunctor.is_covering.symmetrify (hφ : φ.is_covering) : φ.symmetrify.is_covering :=
begin
  refine ⟨λ u, _, λ u, _⟩;
  simp [φ.symmetrify_star, φ.symmetrify_costar, hφ.star_bijective u, hφ.costar_bijective u],
end

/-- The path star at a vertex `u` is the type of all paths starting at `u`.
The type `quiver.path_star u` is defined to be `Σ v : U, path u v`. -/
@[reducible] def quiver.path_star (u : U) := Σ v : U, path u v

/-- Constructor for `quiver.path_star`. Defined to be `sigma.mk`. -/
@[reducible] protected def quiver.path_star.mk {u v : U} (p : path u v) :
  quiver.path_star u := ⟨_, p⟩

/-- A prefunctor induces a map of path stars. -/
def prefunctor.path_star (u : U) : quiver.path_star u → quiver.path_star (φ.obj u) :=
λ p, quiver.path_star.mk (φ.map_path p.2)

@[simp] lemma prefunctor.path_star_apply {u v : U} (p : path u v) :
  φ.path_star u (quiver.path_star.mk p) = quiver.path_star.mk (φ.map_path p) := rfl

theorem prefunctor.path_star_injective (hφ : ∀ u, injective (φ.star u)) (u : U) :
  injective (φ.path_star u) :=
begin
  dsimp [prefunctor.path_star, quiver.path_star.mk],
  rintro ⟨v₁, p₁⟩,
  induction p₁ with x₁ y₁ p₁ e₁ ih;
    rintro ⟨y₂, p₂⟩; cases p₂ with x₂ _ p₂ e₂;
    intro h;
    simp only [prefunctor.path_star_apply, prefunctor.map_path_nil,
                prefunctor.map_path_cons] at h,
  { exfalso,
    cases h with h h',
    rw [←path.eq_cast_iff_heq rfl h.symm, path.cast_cons] at h',
    exact (path.nil_ne_cons _ _) h', },
  { exfalso,
    cases h with h h',
    rw [←path.cast_eq_iff_heq rfl h, path.cast_cons] at h',
    exact (path.cons_ne_nil _ _) h', },
  { cases h with hφy h',
    rw [←path.cast_eq_iff_heq rfl hφy, path.cast_cons, path.cast_rfl_rfl] at h',
    have hφx := path.obj_eq_of_cons_eq_cons h',
    have hφp := path.heq_of_cons_eq_cons h',
    have hφe := heq.trans (hom.cast_heq rfl hφy _).symm (path.hom_heq_of_cons_eq_cons h'),
    have h_path_star : φ.path_star u ⟨x₁, p₁⟩ = φ.path_star u ⟨x₂, p₂⟩,
    { simp only [prefunctor.path_star_apply, sigma.mk.inj_iff], exact ⟨hφx, hφp⟩, },
    cases ih h_path_star,
    have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩,
    { simp only [prefunctor.star_apply, sigma.mk.inj_iff], exact ⟨hφy, hφe⟩, },
    cases hφ x₁ h_star,
    refl, },
end

theorem prefunctor.path_star_surjective (hφ : ∀ u, surjective (φ.star u)) (u : U) :
  surjective (φ.path_star u) :=
begin
  dsimp [prefunctor.path_star, quiver.path_star.mk],
  rintro ⟨v, p⟩,
  induction p with v' v'' p' ev ih,
  { use ⟨u, path.nil⟩,
    simp only [prefunctor.map_path_nil, eq_self_iff_true, heq_iff_eq, and_self], },
  { obtain ⟨⟨u', q'⟩, h⟩ := ih,
    simp only at h,
    obtain ⟨rfl,rfl⟩ := h,
    obtain ⟨⟨u'', eu⟩, k⟩ := hφ u' ⟨_, ev⟩,
    simp at k,
    obtain ⟨rfl,rfl⟩ := k,
    use ⟨_, q'.cons eu⟩,
    simp only [prefunctor.map_path_cons, eq_self_iff_true, heq_iff_eq, and_self], }
end

theorem prefunctor.path_star_bijective (hφ : ∀ u, bijective (φ.star u)) (u : U) :
  bijective (φ.path_star u) :=
⟨φ.path_star_injective (λ u, (hφ u).1) _, φ.path_star_surjective (λ u, (hφ u).2) _⟩

namespace prefunctor.is_covering
variable {φ}

protected theorem path_star_bijective (hφ : φ.is_covering) (u : U) :
  bijective (φ.path_star u) := φ.path_star_bijective hφ.1 u

end prefunctor.is_covering

section has_involutive_reverse

variables [has_involutive_reverse U] [has_involutive_reverse V] [prefunctor.map_reverse φ]

/-- In a quiver with involutive inverses, the star and costar at any vertex are equivalent. -/
@[simps] def quiver.star_equiv_costar (u : U) :
  quiver.star u ≃ quiver.costar u :=
{ to_fun := λ e, ⟨e.1, reverse e.2⟩,
  inv_fun := λ e, ⟨e.1, reverse e.2⟩,
  left_inv := λ e, by simp [sigma.ext_iff],
  right_inv := λ e, by simp [sigma.ext_iff] }

@[simp] lemma quiver.star_equiv_costar_apply {u v : U} (e : u ⟶ v) :
  quiver.star_equiv_costar u (quiver.star.mk e) = quiver.costar.mk (reverse e) := rfl

@[simp] lemma quiver.star_equiv_costar_symm_apply {u v : U} (e : u ⟶ v) :
  (quiver.star_equiv_costar v).symm (quiver.costar.mk e) = quiver.star.mk (reverse e) := rfl

lemma prefunctor.costar_conj_star (u : U) : (φ.costar u) =
  quiver.star_equiv_costar (φ.obj u) ∘ φ.star u ∘ (quiver.star_equiv_costar u).symm :=
by { ext ⟨v, f⟩; simp, }

lemma prefunctor.bijective_costar_iff_bijective_star (u : U) :
  bijective (φ.costar u) ↔ bijective (φ.star u) :=
begin
  rw [prefunctor.costar_conj_star, bijective.of_comp_iff', bijective.of_comp_iff];
  exact equiv.bijective _,
end

lemma prefunctor.is_covering_of_bijective_star (h : ∀ u, bijective (φ.star u)) :
  φ.is_covering := ⟨h, λ u, (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

lemma prefunctor.is_covering_of_bijective_costar (h : ∀ u, bijective (φ.costar u)) :
  φ.is_covering := ⟨λ u, (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end has_involutive_reverse

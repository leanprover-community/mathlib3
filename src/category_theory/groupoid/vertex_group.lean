/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv
import combinatorics.quiver.path

/-!
# Vertex group

This file defines the vertex group (*aka* isotropy group) of a groupoid at a vertex.

## Implementation notes

* The instance is defined "manually", instead of relying on `category_theory.Aut.group` or
  using `category_theory.inv`.
* The multiplication order therefore matches the categorical one : `x * y = x ≫ y`.
* The inverse is directly defined in terms of the groupoidal inverse : `x ⁻¹ = groupoid.inv x`.

## Tags

isotropy, vertex group, groupoid
-/

namespace category_theory

namespace groupoid

universes u v

variables {C : Type u} [groupoid C]

/-- The vertex group at `c`. -/
@[simps] instance vertex_group (c : C): group (c ⟶ c) :=
{ mul := λ (x y : c ⟶ c), x ≫ y,
  mul_assoc := category.assoc,
  one := 𝟙 c,
  one_mul := category.id_comp,
  mul_one := category.comp_id,
  inv := groupoid.inv,
  mul_left_inv := inv_comp }

/-- The inverse in the group is equal to the inverse given by `category_theory.inv`. -/
lemma vertex_group.inv_eq_inv (c : C) (γ : c ⟶ c) :
  γ ⁻¹ = category_theory.inv γ := groupoid.inv_eq_inv γ

/--
An arrow in the groupoid defines, by conjugation, an isomorphism of groups between
its endpoints
-/
def vertex_group_isom_of_map {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) :=
⟨ λ γ, (groupoid.inv f) ≫ γ ≫ f, λ δ, f ≫ δ ≫ (groupoid.inv f),
  λ x, by
  { simp_rw [category.assoc, groupoid.comp_inv, category.comp_id,←category.assoc,
             groupoid.comp_inv, category.id_comp], },
  λ x, by
  { simp_rw [category.assoc, groupoid.inv_comp, ←category.assoc, groupoid.inv_comp,
             category.id_comp, category.comp_id], },
  λ x y, by
  { have : x ≫ y = x ≫ f ≫ (groupoid.inv f) ≫ y, by
    { congr, rw [←category.assoc,groupoid.comp_inv,category.id_comp], },
    simp only [this, groupoid.vertex_group_mul, category.assoc], } ⟩

/--
A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertex_group_isom_of_path {c : C} : Π {d : C} (p : quiver.path c d), (c ⟶ c) ≃* (d ⟶ d)
| _ quiver.path.nil := by refl
| _ (quiver.path.cons q f) := (vertex_group_isom_of_path q).trans (vertex_group_isom_of_map f)

/-- A functor defines a morphism of vertex group. -/
def vertex_group_hom_of_functor {D : Type v} [groupoid D] (φ : C ⥤ D) (c : C) :
  (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) :=
⟨ λ γ, φ.map γ,
  functor.map_id φ c,
  λ γ δ, functor.map_comp φ γ δ ⟩

end groupoid

end category_theory

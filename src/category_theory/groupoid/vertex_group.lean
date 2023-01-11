/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.path_category
import algebra.group.defs
import algebra.hom.group
import algebra.hom.equiv.basic
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
its endpoints.
-/
@[simps] def vertex_group_isom_of_map {c d : C} (f : c ⟶ d) : (c ⟶ c) ≃* (d ⟶ d) :=
{ to_fun  := λ γ, inv f ≫ γ ≫ f,
  inv_fun := λ δ, f ≫ δ ≫ inv f,
  left_inv := λ γ, by simp_rw [category.assoc, comp_inv, category.comp_id,
                              ←category.assoc, comp_inv, category.id_comp],
  right_inv := λ δ, by simp_rw [category.assoc, inv_comp, ←category.assoc,
                                inv_comp, category.id_comp, category.comp_id],
  map_mul' := λ γ₁ γ₂, by simp only [vertex_group_mul, inv_eq_inv,
                                     category.assoc, is_iso.hom_inv_id_assoc] }

/--
A path in the groupoid defines an isomorphism between its endpoints.
-/
def vertex_group_isom_of_path {c d : C} (p : quiver.path c d) : (c ⟶ c) ≃* (d ⟶ d) :=
vertex_group_isom_of_map (compose_path p)

/-- A functor defines a morphism of vertex group. -/
@[simps] def _root_.category_theory.functor.map_vertex_group {D : Type v} [groupoid D]
  (φ : C ⥤ D) (c : C) : (c ⟶ c) →* (φ.obj c ⟶ φ.obj c) :=
{ to_fun := φ.map,
  map_one' := φ.map_id c,
  map_mul' := φ.map_comp }

end groupoid

end category_theory

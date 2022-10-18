/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.groupoid
import category_theory.groupoid.basic
import category_theory.structured_arrow
import category_theory.groupoid.vertex_group
import category_theory.types
import category_theory.elements

/-!
# Actions of groupoids
-/

namespace category_theory

namespace groupoid

namespace action

universes u v u' v' u'' v''

variables  {V : Type*} [groupoid V] {V' : Type*} [groupoid V']

-- Possible definition of an action on a set?
structure action (X : Type u) :=
(w : X → V)
(F : V ⥤ Type u)
(Fw : F.obj = (λ v, {x | w x = v}))


variable (F : V ⥤ Type u)

def stabilizer (v : V) (x  : F.obj v) : subgroup (v ⟶ v) :=
{ carrier := {f | F.map f x = x},
  one_mem' := by simp only [vertex_group_one, set.mem_set_of_eq, functor_to_types.map_id_apply],
  mul_mem' := λ f f' hf hf', by
  { simp only [vertex_group_mul, set.mem_set_of_eq, functor_to_types.map_comp_apply],
    simp only [set.mem_set_of_eq] at hf hf',
    rw [hf, hf'], },
  inv_mem' := λ f hf, by
  { simp only [vertex_group_inv, inv_eq_inv, set.mem_set_of_eq],
    simp only [set.mem_set_of_eq] at hf,
    nth_rewrite_lhs 0 ←hf,
    rw ←functor_to_types.map_comp_apply,
    simp only [is_iso.hom_inv_id, functor_to_types.map_id_apply], } }

abbreviation semidirect_product := F.elements
instance : groupoid (semidirect_product F) := category_theory.groupoid_of_elements F

end action

end groupoid

end category_theory

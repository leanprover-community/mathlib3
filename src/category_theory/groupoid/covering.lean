/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
import category_theory.category.basic
import category_theory.functor.basic
import category_theory.groupoid
import category_theory.groupoid.basic
import combinatorics.quiver.basic
import combinatorics.quiver.symmetric
import logic.relation
import tactic.nth_rewrite
import category_theory.path_category
import category_theory.quotient
import category_theory.groupoid.vertex_group

/-!
# Covering of groupoids

-/

namespace category_theory

namespace groupoid


universes u v u' v' u'' v''

variables {V : Type*} [groupoid V] {V' : Type*} [groupoid V'] (φ : V ⥤ V')

/-- Definition following Brown -/
def is_covering := ∀ (v : V) (F' : Σ (u' : V'), φ.obj v ⟶ u'),
                     ∃! (F : Σ (u : V), v ⟶ u),
                        ∃ (h : φ.obj F.1 = F'.1), (φ.map F.2) ≫ (eq_to_hom h) = F'.2

variables {φ} (φc : is_covering φ)

namespace covering

/-- Following brown -/
def characteristic_group (v : V) := (φ.map_vertex_group v).range

include φc
lemma map_vertex_group_mono (v : V) : (φ.map_vertex_group v).ker = ⊥ :=
begin
  rw [monoid_hom.ker_eq_bot_iff],
  rintro f g he,
  simp only [functor.map_vertex_group_apply] at he,
  obtain hf := (φc v ⟨φ.obj v, φ.map f⟩),
  have := @exists_unique.unique _ _ hf ⟨v,f⟩ ⟨v,g⟩ _ _, rotate,
  { use rfl, apply category.comp_id', },
  { use rfl, simp, exact he.symm, },
  simpa only [sigma.ext_iff, eq_self_iff_true, heq_iff_eq, true_and] using this,
end

end covering

end groupoid

end category_theory

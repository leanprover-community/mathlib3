/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import category_theory.lifting_properties.basic
import category_theory.adjunction.basic

/-!

# Lifting properties and adjunction

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we obtain `adjunction.has_lifting_property_iff`, which states
that when we have an adjunction `adj : G ⊣ F` between two functors `G : C ⥤ D`
and `F : D ⥤ C`, then a morphism of the form `G.map i` has the left lifting
property in `D` with respect to a morphism `p` if and only the morphism `i`
has the left lifting property in `C` with respect to `F.map p`.

-/

namespace category_theory

open category

variables {C D : Type*} [category C] [category D] {G : C ⥤ D} {F : D ⥤ C}

namespace comm_sq

section
variables {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : G.obj A ⟶ X} {v : G.obj B ⟶ Y}
  (sq : comm_sq u (G.map i) p v) (adj : G ⊣ F)

include sq

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `G.map i` and the right map is `p` has an "adjoint" commutative
square whose left map is `i` and whose right map is `F.map p`. -/
lemma right_adjoint :
  comm_sq (adj.hom_equiv _ _ u) i (F.map p) (adj.hom_equiv _ _ v) :=
⟨begin
  simp only [adjunction.hom_equiv_unit, assoc, ← F.map_comp, sq.w],
  rw [F.map_comp, adjunction.unit_naturality_assoc],
end⟩

/-- The liftings of a commutative are in bijection with the liftings of its (right)
adjoint square. -/
def right_adjoint_lift_struct_equiv :
  sq.lift_struct ≃ (sq.right_adjoint adj).lift_struct :=
{ to_fun := λ l,
  { l := adj.hom_equiv _ _ l.l,
    fac_left' := by rw [← adj.hom_equiv_naturality_left, l.fac_left],
    fac_right' := by rw [← adjunction.hom_equiv_naturality_right, l.fac_right], },
  inv_fun := λ l,
  { l := (adj.hom_equiv _ _).symm l.l,
    fac_left' := begin
      rw [← adjunction.hom_equiv_naturality_left_symm, l.fac_left],
      apply (adj.hom_equiv _ _).left_inv,
    end,
    fac_right' := begin
      rw [← adjunction.hom_equiv_naturality_right_symm, l.fac_right],
      apply (adj.hom_equiv _ _).left_inv,
    end, },
  left_inv := by tidy,
  right_inv := by tidy, }

/-- A square has a lifting if and only if its (right) adjoint square has a lifting. -/
lemma right_adjoint_has_lift_iff :
  has_lift (sq.right_adjoint adj) ↔ has_lift sq :=
begin
  simp only [has_lift.iff],
  exact equiv.nonempty_congr (sq.right_adjoint_lift_struct_equiv adj).symm,
end

instance [has_lift sq] : has_lift (sq.right_adjoint adj) :=
by { rw right_adjoint_has_lift_iff, apply_instance, }

end

section
variables {A B : C} {X Y : D} {i : A ⟶ B} {p : X ⟶ Y} {u : A ⟶ F.obj X} {v : B ⟶ F.obj Y}
  (sq : comm_sq u i (F.map p) v) (adj : G ⊣ F)

include sq

/-- When we have an adjunction `G ⊣ F`, any commutative square where the left
map is of the form `i` and the right map is `F.map p` has an "adjoint" commutative
square whose left map is `G.map i` and whose right map is `p`. -/
lemma left_adjoint :
  comm_sq ((adj.hom_equiv _ _).symm u) (G.map i) p
    ((adj.hom_equiv _ _).symm v) :=
⟨begin
  simp only [adjunction.hom_equiv_counit, assoc,
    ← G.map_comp_assoc, ← sq.w],
  rw [G.map_comp, assoc, adjunction.counit_naturality],
end⟩

/-- The liftings of a commutative are in bijection with the liftings of its (left)
adjoint square. -/
def left_adjoint_lift_struct_equiv :
  sq.lift_struct ≃ (sq.left_adjoint adj).lift_struct :=
{ to_fun := λ l,
  { l := (adj.hom_equiv _ _).symm l.l,
    fac_left' := by rw [← adj.hom_equiv_naturality_left_symm, l.fac_left],
    fac_right' := by rw [← adj.hom_equiv_naturality_right_symm, l.fac_right], },
  inv_fun := λ l,
  { l := (adj.hom_equiv _ _) l.l,
    fac_left' := begin
      rw [← adj.hom_equiv_naturality_left, l.fac_left],
      apply (adj.hom_equiv _ _).right_inv,
    end,
    fac_right' := begin
      rw [← adj.hom_equiv_naturality_right, l.fac_right],
      apply (adj.hom_equiv _ _).right_inv,
    end, },
  left_inv := by tidy,
  right_inv := by tidy, }

/-- A (left) adjoint square has a lifting if and only if the original square has a lifting. -/
lemma left_adjoint_has_lift_iff :
  has_lift (sq.left_adjoint adj) ↔ has_lift sq :=
begin
  simp only [has_lift.iff],
  exact equiv.nonempty_congr (sq.left_adjoint_lift_struct_equiv adj).symm,
end

instance [has_lift sq] : has_lift (sq.left_adjoint adj) :=
by { rw left_adjoint_has_lift_iff, apply_instance, }

end

end comm_sq

namespace adjunction

lemma has_lifting_property_iff (adj : G ⊣ F) {A B : C} {X Y : D} (i : A ⟶ B) (p : X ⟶ Y) :
  has_lifting_property (G.map i) p ↔ has_lifting_property i (F.map p) :=
begin
  split; introI; constructor; intros f g sq,
  { rw ← sq.left_adjoint_has_lift_iff adj,
    apply_instance, },
  { rw ← sq.right_adjoint_has_lift_iff adj,
    apply_instance, },
end

end adjunction

end category_theory

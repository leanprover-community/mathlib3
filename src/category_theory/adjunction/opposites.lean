/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Read, Andrew Yang
-/

import category_theory.adjunction.basic
import category_theory.yoneda
import category_theory.opposites

/-!
# Opposite adjunctions

This file contains constructions to relate adjunctions of functors to adjunctions of their
opposites.
These constructions are used to show uniqueness of adjoints (up to natural isomorphism).

## Tags
adjunction, opposite, uniqueness
-/


open category_theory

universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

namespace category_theory.adjunction

/-- If `G.op` is adjoint to `F.op` then `F` is adjoint to `G`. -/
@[simps] def adjoint_of_op_adjoint_op (F : C ⥤ D) (G : D ⥤ C) (h : G.op ⊣ F.op) : F ⊣ G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  ((h.hom_equiv (opposite.op Y) (opposite.op X)).trans (op_equiv _ _)).symm.trans (op_equiv _ _) }

/-- If `G` is adjoint to `F.op` then `F` is adjoint to `G.unop`. -/
def adjoint_unop_of_adjoint_op (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F.op) : F ⊣ G.unop :=
adjoint_of_op_adjoint_op F G.unop (h.of_nat_iso_left G.op_unop_iso.symm)

/-- If `G.op` is adjoint to `F` then `F.unop` is adjoint to `G`. -/
def unop_adjoint_of_op_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G.op ⊣ F) : F.unop ⊣ G :=
adjoint_of_op_adjoint_op _ _ (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.unop` is adjoint to `G.unop`. -/
def unop_adjoint_unop_of_adjoint (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G ⊣ F) : F.unop ⊣ G.unop :=
adjoint_unop_of_adjoint_op F.unop G (h.of_nat_iso_right F.op_unop_iso.symm)

/-- If `G` is adjoint to `F` then `F.op` is adjoint to `G.op`. -/
@[simps] def op_adjoint_op_of_adjoint (F : C ⥤ D) (G : D ⥤ C) (h : G ⊣ F) : F.op ⊣ G.op :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  (op_equiv _ Y).trans ((h.hom_equiv _ _).symm.trans (op_equiv X (opposite.op _)).symm) }

/-- If `G` is adjoint to `F.unop` then `F` is adjoint to `G.op`. -/
def adjoint_op_of_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : D ⥤ C) (h : G ⊣ F.unop) : F ⊣ G.op :=
(op_adjoint_op_of_adjoint F.unop _ h).of_nat_iso_left F.op_unop_iso

/-- If `G.unop` is adjoint to `F` then `F.op` is adjoint to `G`. -/
def op_adjoint_of_unop_adjoint (F : C ⥤ D) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F) : F.op ⊣ G :=
(op_adjoint_op_of_adjoint _ G.unop h).of_nat_iso_right G.op_unop_iso

/-- If `G.unop` is adjoint to `F.unop` then `F` is adjoint to `G`. -/
def adjoint_of_unop_adjoint_unop (F : Cᵒᵖ ⥤ Dᵒᵖ) (G : Dᵒᵖ ⥤ Cᵒᵖ) (h : G.unop ⊣ F.unop) : F ⊣ G :=
(adjoint_op_of_adjoint_unop _ _ h).of_nat_iso_right G.op_unop_iso

/--
If `F` and `F'` are both adjoint to `G`, there is a natural isomorphism
`F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda`.
We use this in combination with `fully_faithful_cancel_right` to show left adjoints are unique.
-/
def left_adjoints_coyoneda_equiv {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G):
  F.op ⋙ coyoneda ≅ F'.op ⋙ coyoneda :=
nat_iso.of_components
  (λ X, nat_iso.of_components
    (λ Y, ((adj1.hom_equiv X.unop Y).trans (adj2.hom_equiv X.unop Y).symm).to_iso)
    (by tidy))
  (by tidy)

/-- If `F` and `F'` are both left adjoint to `G`, then they are naturally isomorphic. -/
def left_adjoint_uniq {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
nat_iso.remove_op (fully_faithful_cancel_right _ (left_adjoints_coyoneda_equiv adj2 adj1))

@[simp]
lemma hom_equiv_left_adjoint_uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
  adj1.hom_equiv _ _ ((left_adjoint_uniq adj1 adj2).hom.app x) = adj2.unit.app x :=
begin
  apply (adj1.hom_equiv _ _).symm.injective,
  apply quiver.hom.op_inj,
  apply coyoneda.map_injective,
  swap, apply_instance,
  ext f y,
  simpa [left_adjoint_uniq, left_adjoints_coyoneda_equiv]
end

@[simp, reassoc]
lemma unit_left_adjoint_uniq_hom {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
  adj1.unit ≫ whisker_right (left_adjoint_uniq adj1 adj2).hom G = adj2.unit :=
begin
  ext x,
  rw [nat_trans.comp_app, ← hom_equiv_left_adjoint_uniq_hom_app adj1 adj2],
  simp [-hom_equiv_left_adjoint_uniq_hom_app, ←G.map_comp]
end

@[simp, reassoc]
lemma unit_left_adjoint_uniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
  adj1.unit.app x ≫ G.map ((left_adjoint_uniq adj1 adj2).hom.app x) = adj2.unit.app x :=
by { rw ← unit_left_adjoint_uniq_hom adj1 adj2, refl }

@[simp, reassoc]
lemma left_adjoint_uniq_hom_counit {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) :
  whisker_left G (left_adjoint_uniq adj1 adj2).hom ≫ adj2.counit = adj1.counit :=
begin
  ext x,
  apply quiver.hom.op_inj,
  apply coyoneda.map_injective,
  swap, apply_instance,
  ext y f,
  have : F.map (adj2.unit.app (G.obj x)) ≫ adj1.counit.app (F'.obj (G.obj x)) ≫
    adj2.counit.app x ≫ f = adj1.counit.app x ≫ f,
  { erw [← adj1.counit.naturality, ← F.map_comp_assoc], simpa },
  simpa [left_adjoint_uniq, left_adjoints_coyoneda_equiv] using this
end

@[simp, reassoc]
lemma left_adjoint_uniq_hom_app_counit {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : D) :
  (left_adjoint_uniq adj1 adj2).hom.app (G.obj x) ≫ adj2.counit.app x = adj1.counit.app x :=
by { rw ← left_adjoint_uniq_hom_counit adj1 adj2, refl }

@[simp]
lemma left_adjoint_uniq_inv_app {F F' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (x : C) :
  (left_adjoint_uniq adj1 adj2).inv.app x = (left_adjoint_uniq adj2 adj1).hom.app x := rfl

@[simp, reassoc]
lemma left_adjoint_uniq_trans {F F' F'' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (adj3 : F'' ⊣ G) :
  (left_adjoint_uniq adj1 adj2).hom ≫ (left_adjoint_uniq adj2 adj3).hom =
    (left_adjoint_uniq adj1 adj3).hom :=
begin
  ext,
  apply quiver.hom.op_inj,
  apply coyoneda.map_injective,
  swap, apply_instance,
  ext,
  simp [left_adjoints_coyoneda_equiv, left_adjoint_uniq]
end

@[simp, reassoc]
lemma left_adjoint_uniq_trans_app {F F' F'' : C ⥤ D} {G : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G) (adj3 : F'' ⊣ G) (x : C) :
  (left_adjoint_uniq adj1 adj2).hom.app x ≫ (left_adjoint_uniq adj2 adj3).hom.app x =
    (left_adjoint_uniq adj1 adj3).hom.app x :=
by { rw ← left_adjoint_uniq_trans adj1 adj2 adj3, refl }

@[simp]
lemma left_adjoint_uniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
  (left_adjoint_uniq adj1 adj1).hom = 𝟙 _ :=
begin
  ext,
  apply quiver.hom.op_inj,
  apply coyoneda.map_injective,
  swap, apply_instance,
  ext,
  simp [left_adjoints_coyoneda_equiv, left_adjoint_uniq]
end

/-- If `G` and `G'` are both right adjoint to `F`, then they are naturally isomorphic. -/
def right_adjoint_uniq {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') : G ≅ G' :=
nat_iso.remove_op
  (left_adjoint_uniq (op_adjoint_op_of_adjoint _ F adj2) (op_adjoint_op_of_adjoint _ _ adj1))

@[simp]
lemma hom_equiv_symm_right_adjoint_uniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
  (adj2.hom_equiv _ _).symm ((right_adjoint_uniq adj1 adj2).hom.app x) = adj1.counit.app x :=
begin
  apply quiver.hom.op_inj,
  convert hom_equiv_left_adjoint_uniq_hom_app
    (op_adjoint_op_of_adjoint _ F adj2) (op_adjoint_op_of_adjoint _ _ adj1) (opposite.op x),
  simpa
end

@[simp, reassoc]
lemma unit_right_adjoint_uniq_hom_app {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : C) :
  adj1.unit.app x ≫ (right_adjoint_uniq adj1 adj2).hom.app (F.obj x) = adj2.unit.app x :=
begin
  apply quiver.hom.op_inj,
  convert left_adjoint_uniq_hom_app_counit
    (op_adjoint_op_of_adjoint _ _ adj2) (op_adjoint_op_of_adjoint _ _ adj1) (opposite.op x),
  all_goals { simpa }
end

@[simp, reassoc]
lemma unit_right_adjoint_uniq_hom {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
  adj1.unit ≫ whisker_left F (right_adjoint_uniq adj1 adj2).hom = adj2.unit :=
by { ext x, simp }

@[simp, reassoc]
lemma right_adjoint_uniq_hom_app_counit {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
  F.map ((right_adjoint_uniq adj1 adj2).hom.app x) ≫ adj2.counit.app x = adj1.counit.app x :=
begin
  apply quiver.hom.op_inj,
  convert unit_left_adjoint_uniq_hom_app
    (op_adjoint_op_of_adjoint _ _ adj2) (op_adjoint_op_of_adjoint _ _ adj1) (opposite.op x),
  all_goals { simpa }
end

@[simp, reassoc]
lemma right_adjoint_uniq_hom_counit {F : C ⥤ D} {G G' : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F ⊣ G') :
  whisker_right (right_adjoint_uniq adj1 adj2).hom F ≫ adj2.counit = adj1.counit :=
by { ext, simp }

@[simp]
lemma right_adjoint_uniq_inv_app {F : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (x : D) :
  (right_adjoint_uniq adj1 adj2).inv.app x = (right_adjoint_uniq adj2 adj1).hom.app x := rfl

@[simp, reassoc]
lemma right_adjoint_uniq_trans_app {F : C ⥤ D} {G G' G'' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (adj3 : F ⊣ G'') (x : D) :
  (right_adjoint_uniq adj1 adj2).hom.app x ≫ (right_adjoint_uniq adj2 adj3).hom.app x =
    (right_adjoint_uniq adj1 adj3).hom.app x :=
begin
  apply quiver.hom.op_inj,
  exact left_adjoint_uniq_trans_app (op_adjoint_op_of_adjoint _ _ adj3)
    (op_adjoint_op_of_adjoint _ _ adj2) (op_adjoint_op_of_adjoint _ _ adj1) (opposite.op x)
end

@[simp, reassoc]
lemma right_adjoint_uniq_trans {F : C ⥤ D} {G G' G'' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F ⊣ G') (adj3 : F ⊣ G'') :
  (right_adjoint_uniq adj1 adj2).hom ≫ (right_adjoint_uniq adj2 adj3).hom =
    (right_adjoint_uniq adj1 adj3).hom :=
by { ext, simp }

@[simp]
lemma right_adjoint_uniq_refl {F : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) :
  (right_adjoint_uniq adj1 adj1).hom = 𝟙 _ :=
by { delta right_adjoint_uniq, simp }

/--
Given two adjunctions, if the left adjoints are naturally isomorphic, then so are the right
adjoints.
-/
def nat_iso_of_left_adjoint_nat_iso {F F' : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (l : F ≅ F') :
  G ≅ G' :=
right_adjoint_uniq adj1 (adj2.of_nat_iso_left l.symm)

/--
Given two adjunctions, if the right adjoints are naturally isomorphic, then so are the left
adjoints.
-/
def nat_iso_of_right_adjoint_nat_iso {F F' : C ⥤ D} {G G' : D ⥤ C}
  (adj1 : F ⊣ G) (adj2 : F' ⊣ G') (r : G ≅ G') :
  F ≅ F' :=
left_adjoint_uniq adj1 (adj2.of_nat_iso_right r.symm)

end category_theory.adjunction

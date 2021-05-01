/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.concrete_category.basic
import category_theory.yoneda
import category_theory.limits.shapes.pullbacks

/-!
# Representably concrete categories

-/

namespace category_theory

universes w v u

variables (C : Type u) [category.{v} C]

@[simps]
def point_bijection {X : Type v} : (punit ⟶ X) ≃ X :=
{ to_fun := λ f, f punit.star,
  inv_fun := λ x _, x,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ f, rfl }

def representably_concrete_of_left_adjoint (F : C ⥤ Type v) [is_right_adjoint F] :
  corepresentable F :=
{ has_representation :=
  ⟨ opposite.op ((left_adjoint F).obj punit),
    { app := λ X, equiv.trans ((adjunction.of_right_adjoint F).hom_equiv _ _) point_bijection },
    begin
      apply nat_iso.is_iso_of_is_iso_app _,
      intro X,
      rw is_iso_iff_bijective,
      apply equiv.bijective,
    end⟩ }

variables [concrete_category.{v} C]

class representably_concrete : Prop :=
(out : corepresentable (forget C))

variables [representably_concrete C]

noncomputable def representing_object : C :=
representably_concrete.out.has_representation.some.unop

noncomputable def representing : coyoneda.obj (opposite.op (representing_object C)) ≅ forget C :=
@as_iso _ _ _ _ _ (representably_concrete.out.has_representation.some_spec.some_spec)

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

variables {C}

noncomputable def rep_equiv {X : C} : (representing_object C ⟶ X) ≃ X :=
iso.to_equiv ((representing C).app _)

lemma rep_equiv_apply {X Y : C} (f : representing_object C ⟶ X) (g : X ⟶ Y) :
  rep_equiv (f ≫ g) = g (rep_equiv f) :=
congr_fun ((representing C).hom.naturality g) f

@[simp] lemma rep_equiv_symm_apply {X Y : C} (x : X) (f : X ⟶ Y) :
  rep_equiv.symm x ≫ f = rep_equiv.symm (f x) :=
by rw [equiv.eq_symm_apply, rep_equiv_apply, equiv.apply_symm_apply]

open limits

section pullback

variables {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [has_pullback f g] {x : X} {y : Y}

noncomputable def mk_pullback (h : f x = g y) :
  (pullback f g : C) :=
rep_equiv (pullback.lift (rep_equiv.symm x) (rep_equiv.symm y) (by simp [h]))

@[simp]
lemma fst_mk_pullback (h : f x = g y) : (pullback.fst : pullback f g ⟶ X) (mk_pullback h) = x :=
by rw [mk_pullback, ←rep_equiv_apply, pullback.lift_fst, equiv.apply_symm_apply]

@[simp]
lemma snd_mk_pullback (h : f x = g y) : (pullback.snd : pullback f g ⟶ Y) (mk_pullback h) = y :=
by rw [mk_pullback, ←rep_equiv_apply, pullback.lift_snd, equiv.apply_symm_apply]

lemma mk_pullback_uniq (h : f x = g y) (q : pullback f g)
  (hq₁ : (pullback.fst : pullback f g ⟶ X) q = x)
  (hq₂ : (pullback.snd : pullback f g ⟶ Y) q = y) :
  q = mk_pullback h :=
by { rw [mk_pullback, ←equiv.symm_apply_eq], ext1; simpa }

end pullback

end category_theory

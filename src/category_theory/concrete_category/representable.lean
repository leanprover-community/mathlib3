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
noncomputable theory

universes w v u

variables (C : Type u) [category.{v} C]

@[simps]
def point_bijection {X : Type v} : (punit ⟶ X) ≃ X :=
{ to_fun := λ f, f ⟨⟩,
  inv_fun := λ x _, x,
  left_inv := λ x, by { ext ⟨⟩, refl },
  right_inv := λ f, rfl }

lemma corepresentable_of_right_adjoint (F : C ⥤ Type v) [is_right_adjoint F] :
  F.corepresentable :=
{ has_corepresentation :=
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
(out : (forget C).corepresentable)

instance : representably_concrete (Type u) := { out := corepresentable_of_right_adjoint _ _ }

attribute [instance] representably_concrete.out

variables [representably_concrete C]

local attribute [instance] concrete_category.has_coe_to_sort
local attribute [instance] concrete_category.has_coe_to_fun

variables {C}

/--
Elements of `X` are in natural bijection with morphisms from the corepresenting object to `X`. This
allows convenient description of limits in representably concrete categories.
-/
noncomputable def rep_equiv {X : C} : ((forget C).corepr_X ⟶ X) ≃ X :=
iso.to_equiv ((forget C).corepr_w.app _)

lemma rep_equiv_apply {X Y : C} (f : (forget C).corepr_X ⟶ X) (g : X ⟶ Y) :
  rep_equiv (f ≫ g) = g (rep_equiv f) :=
congr_fun ((forget C).corepr_f.naturality g) f

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

section binary_product

variables {X Y : C} [has_binary_product X Y] (x : X) (y : Y)

noncomputable def mk_binary_product : (X ⨯ Y : C) :=
rep_equiv (limits.prod.lift (rep_equiv.symm x) (rep_equiv.symm y))

@[simp] lemma fst_mk_binary_product : (limits.prod.fst : X ⨯ Y ⟶ X) (mk_binary_product x y) = x :=
by rw [mk_binary_product, ←rep_equiv_apply, prod.lift_fst, equiv.apply_symm_apply]
@[simp] lemma snd_mk_binary_product : (limits.prod.snd : X ⨯ Y ⟶ Y) (mk_binary_product x y) = y :=
by rw [mk_binary_product, ←rep_equiv_apply, prod.lift_snd, equiv.apply_symm_apply]
lemma mk_binary_product_uniq (z : X ⨯ Y)
  (hz₁ : (limits.prod.fst : X ⨯ Y ⟶ X) z = x) (hz₂ : (limits.prod.snd : X ⨯ Y ⟶ Y) z = y) :
  z = mk_binary_product x y :=
by { rw [mk_binary_product, ←equiv.symm_apply_eq], ext1; simpa }

@[simps] noncomputable def binary_product.equiv : (X ⨯ Y : C) ≃ X × Y :=
{ to_fun := λ z, ⟨(limits.prod.fst : X ⨯ Y ⟶ X) z, (limits.prod.snd : X ⨯ Y ⟶ Y) z⟩,
  inv_fun := λ z, mk_binary_product z.1 z.2,
  left_inv := λ z, (mk_binary_product_uniq _ _ _ rfl rfl).symm,
  right_inv := λ ⟨x, y⟩, prod.ext (fst_mk_binary_product _ _) (snd_mk_binary_product _ _) }

end binary_product

section terminal

variables [has_terminal C]

noncomputable def mk_terminal : (⊤_ C : C) :=
rep_equiv (terminal.from _)

lemma mk_terminal_uniq (z : ⊤_ C) :
  z = mk_terminal :=
by { rw [mk_terminal, ←equiv.symm_apply_eq], apply subsingleton.elim }

noncomputable instance : unique (⊤_ C : C) :=
{ default := mk_terminal,
  uniq := mk_terminal_uniq }

end terminal

end category_theory

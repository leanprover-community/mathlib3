/-
Copyright (c) 2022 Winston Yin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Winston Yin
-/
import representation_theory.Action

/-!
# `Action V G` is a closed monoidal category when `G : Group` and `V` is a closed monoidal category.
-/

universe u

open opposite
open category_theory

variables
  {V : Type (u+1)} [large_category V] [monoidal_category V] [monoidal_closed V] {G : Group.{u}}
  (X Y Z : Action V G) (g g' : G)

namespace Action

/-- For f : X.V ⟶ Y.V, compose on the right by X.ρ g⁻¹ : X.V ⟶ X.V -/
def pre_comp : (ihom X.V).obj Y.V ⟶ (ihom X.V).obj Y.V :=
  (monoidal_closed.internal_hom.map (X.ρ (g⁻¹ : G)).op).app Y.V

@[simp] lemma pre_comp_apply :
  pre_comp X Y g = (monoidal_closed.internal_hom.map (X.ρ (g⁻¹ : G)).op).app Y.V := rfl

@[simp] lemma pre_comp_mul :
  pre_comp X Y (g * g') = pre_comp X Y g' ≫ pre_comp X Y g := by simp

/-- For f : X.V ⟶ Y.V, compose on the left by Y.ρ g : Y.V ⟶ Y.V -/
def post_comp : (ihom X.V).obj Y.V ⟶ (ihom X.V).obj Y.V :=
  (monoidal_closed.internal_hom.flip.map (Y.ρ g)).app (op X.V)

@[simp] lemma post_comp_apply :
  post_comp X Y g = (monoidal_closed.internal_hom.flip.map (Y.ρ g)).app (op X.V) := rfl

@[simp] lemma post_comp_mul :
  post_comp X Y (g * g') = post_comp X Y g' ≫ post_comp X Y g := by simp

lemma pre_post_comp_comm :
  pre_comp X Y g ≫ post_comp X Y g' = post_comp X Y g' ≫ pre_comp X Y g := by simp

/-- The internal hom of `X Y : Action V G`, i.e. the natural G-action on `[X, Y]` -/
@[protected] def ihom (X Y : Action V G) : Action V G :=
⟨(ihom X.V).obj Y.V,
begin
  refine ⟨λ g, pre_comp X Y g ≫ post_comp X Y g, _, _⟩,
  { simp [pre_comp_apply, post_comp_apply],
    apply category.id_comp },
  { intros g g',
    rw [pre_comp_mul, post_comp_mul, End.mul_def, category.assoc, category.assoc],
    nth_rewrite 1 ←category.assoc,
    rw pre_post_comp_comm,
    rw category.assoc }
end⟩

@[simp] lemma ihom_V : (ihom X Y).V = (ihom X.V).obj Y.V := rfl

@[simp] lemma ihom_ρ : (ihom X Y).ρ g = pre_comp X Y g ≫ post_comp X Y g := rfl

/-- `Action.ihom` as a functor -/
def ihom_functor (X : (Action V G)ᵒᵖ) : Action V G ⥤ Action V G :=
{ obj := ihom (unop X),
  map := λ Y Z f, begin
    refine ⟨(monoidal_closed.internal_hom.flip.map f.hom).app (op (unop X).V), _⟩,
    { intro,
      simp,
      apply congr_arg,
      rw [←functor.map_comp, ←functor.map_comp],
      apply congr_arg,
      apply f.comm },
  end,
  map_id' := by { intro Y, ext, simp, congr },
  map_comp' := by { intros, apply Action.hom.ext, simp } }

@[simp] lemma ihom_functor_obj (X : (Action V G)ᵒᵖ) :
  (ihom_functor X).obj Y = ihom (unop X) Y := rfl

@[simp] lemma ihom_functor_map_hom (X' : (Action V G)ᵒᵖ) (f : X ⟶ Y) :
  ((ihom_functor X').map f).hom =
  (monoidal_closed.internal_hom.flip.map f.hom).app (op (unop X').V) := rfl

/-- Mapping of homs that is compatible with `ihom_functor` -/
def coyoneda_map {X Y : (Action V G)ᵒᵖ} (f : X ⟶ Y) :
  ihom_functor X ⟶ ihom_functor Y :=
begin
  refine ⟨_, _⟩,
  { intro Z,
    rw [ihom_functor_obj, ihom_functor_obj],
    refine ⟨(monoidal_closed.internal_hom.map f.unop.hom.op).app Z.V, _⟩,
    intro,
    simp,
    rw [←category.assoc, ←category.assoc],
    apply congr_fun,
    apply congr_arg,
    rw [←nat_trans.comp_app, ←nat_trans.comp_app],
    apply congr_fun,
    apply (nat_trans.ext_iff _ _).mp,
    rw [←functor.map_comp, ←functor.map_comp],
    apply congr_arg,
    rw [←op_comp, ←op_comp],
    apply congr_arg,
    apply (f.unop.comm (g⁻¹ : G)).symm },
  { intros X' Y' f',
    simp,
    apply Action.hom.ext,
    simp }
end

@[simp] lemma coyoneda_map_app_hom {X Y : (Action V G)ᵒᵖ} (f : X ⟶ Y) :
  ((coyoneda_map f).app Z).hom =
  (monoidal_closed.internal_hom.map f.unop.hom.op).app Z.V := rfl

/-- The Yoneda embedding for `Action V G` built from `Action.ihom`. -/
def coyoneda : (Action V G)ᵒᵖ ⥤ Action V G ⥤ Action V G :=
{ obj := ihom_functor,
  map := λ X Y f, coyoneda_map f,
  map_id' := by { intro, apply nat_trans.ext, ext, simp, congr },
  map_comp' := by { intros, apply nat_trans.ext, ext, simp } }

@[simp] lemma coyoneda_obj {X : (Action V G)ᵒᵖ} :
  coyoneda.obj X = ihom_functor X := rfl

@[simp] lemma coyoneda_obj_map_hom {X : (Action V G)ᵒᵖ} (f : Y ⟶ Z) :
  ((coyoneda.obj X).map f).hom = ((ihom_functor X).map f).hom := rfl

@[simp] lemma coyoneda_obj_obj_ρ :
  ((coyoneda.obj (op X)).obj Y).ρ g = pre_comp X Y g ≫ post_comp X Y g := rfl

@[simp] lemma internal_hom_obj (X : Vᵒᵖ) :
  monoidal_closed.internal_hom.obj X = ihom (unop X) := rfl

@[simp] lemma internal_hom_map {X Y : Vᵒᵖ} (f : X ⟶ Y) :
  monoidal_closed.internal_hom.map f = monoidal_closed.pre f.unop := rfl

@[simp] lemma internal_hom_obj_map (X : Vᵒᵖ) {Y Z : V} (f : Y ⟶ Z) :
  (monoidal_closed.internal_hom.obj X).map f = (ihom (unop X)).map f := rfl

variables {X Y Z}
@[nolint unused_arguments] lemma tensor_left_g_id_comp_injective {f' f'' : X.V ⊗ Y.V ⟶ Z.V} :
  ((X.ρ_Aut g).hom ⊗ 𝟙 Y.V) ≫ f' = ((X.ρ_Aut g).hom ⊗ 𝟙 Y.V) ≫ f'' → f' = f'' :=
begin
  intro h,
  have h' := congr_arg (category_struct.comp ((X.ρ_Aut g).inv ⊗ 𝟙 Y.V)) h,
  rw [monoidal_category.inv_hom_id_tensor_assoc, monoidal_category.inv_hom_id_tensor_assoc] at h',
  rw monoidal_category.tensor_id_comp_id_tensor_assoc at h',
  simp at h',
  exact h'
end

/-- Elevate the curry on `V` to an `Action V G` hom. -/
def monoidal_closed_curry
  (f : (monoidal_category.tensor_left X).obj Y ⟶ Z) :
  Y ⟶ (coyoneda.obj (op X)).obj Z :=
⟨monoidal_closed.curry f.hom,
begin
  intro,
  rw coyoneda_obj_obj_ρ,
  rw ←monoidal_closed.curry_natural_left,
  have : (𝟙 (unop (op X)).V ⊗ Y.ρ g) ≫ f.hom = (𝟙 X.V ⊗ Y.ρ g) ≫ f.hom := rfl,
  rw this,
  have h := congr_arg (category_struct.comp ((X.ρ_Aut g).inv ⊗ 𝟙 Y.V)) (f.comm g),
  have : ((monoidal_category.tensor_left X).obj Y).ρ = (X ⊗ Y).ρ := rfl,
  rw this at h,
  rw Action.tensor_rho at h,
  rw ←Action.ρ_Aut_apply_hom at h,
  rw monoidal_category.inv_hom_id_tensor_assoc at h,
  rw monoidal_category.tensor_id_comp_id_tensor_assoc at h,
  rw (monoidal_closed.curry_eq_iff _ _).mpr,
  rw h,
  simp,
  rw [←category.assoc, ←category.assoc],
  have : (ihom (unop (op X.V))).map = (ihom X.V).map := rfl,
  rw this,
  rw [monoidal_closed.uncurry_natural_right
    (monoidal_closed.curry f.hom ≫ (monoidal_closed.pre (X.ρ (g⁻¹ : G))).app Z.V)],
  apply congr_fun,
  apply congr_arg,
  rw monoidal_closed.uncurry_natural_left,
  rw monoidal_closed.uncurry_pre,
  rw @monoidal_category.id_tensor_comp_tensor_id_assoc _ _ _ _ ((ihom X.V).obj Z.V),
  apply tensor_left_g_id_comp_injective g,
  rw [←Action.ρ_Aut_apply_inv, monoidal_category.hom_inv_id_tensor_assoc,
    monoidal_category.hom_inv_id_tensor_assoc],
  simp,
  rw ←monoidal_closed.uncurry_eq,
  rw monoidal_closed.uncurry_curry,
  apply_instance,
end⟩

@[simp] lemma monoidal_closed_curry_hom
  (f : (monoidal_category.tensor_left X).obj Y ⟶ Z) :
  (monoidal_closed_curry f).hom = monoidal_closed.curry f.hom := rfl

/-- Elevate the uncurry on `V` to an `Action V G` hom. -/
def monoidal_closed_uncurry
  (f : Y ⟶ ihom X Z) :
  (monoidal_category.tensor_left X).obj Y ⟶ Z :=
⟨monoidal_closed.uncurry f.hom,
begin
  intro,
  have : ((monoidal_category.tensor_left X).obj Y).ρ = (X ⊗ Y).ρ := rfl,
  rw this,
  apply tensor_left_g_id_comp_injective g⁻¹,
  rw [Action.tensor_rho, Action.ρ_Aut_apply_hom, ←Action.ρ_Aut_apply_inv,
    ←Action.ρ_Aut_apply_hom, ←category.assoc,
    monoidal_category.inv_hom_id_tensor,
    monoidal_category.tensor_id, category.id_comp],
  rw ←monoidal_closed.uncurry_natural_left,
  rw f.comm,
  rw ihom_ρ,
  simp,
  rw ←category.assoc,
  have : (ihom (unop (op X.V))).map = (ihom X.V).map := rfl,
  rw this,
  rw monoidal_closed.uncurry_natural_right,
  rw ←category.assoc,
  apply congr_fun,
  apply congr_arg,
  rw monoidal_closed.uncurry_natural_left,
  rw monoidal_closed.uncurry_pre,
  have : 𝟙 ((ihom (unop (op X.V))).obj Z.V) = 𝟙 ((ihom X.V).obj Z.V) := rfl,
  rw this,
  have : (ihom.ev (unop (op X.V))).app = (ihom.ev X.V).app := rfl,
  rw this,
  have : 𝟙 ((ihom X.V).obj Z.V) = 𝟙 (ihom X Z).V := rfl,
  rw this,
  rw monoidal_category.id_tensor_comp_tensor_id_assoc,
  apply tensor_left_g_id_comp_injective g,
  rw ←Action.ρ_Aut_apply_inv,
  rw monoidal_category.hom_inv_id_tensor_assoc,
  rw monoidal_category.hom_inv_id_tensor_assoc,
  rw [monoidal_category.tensor_id, category.id_comp],
  rw [category.id_comp, ←monoidal_category.tensor_id],
  rw ←monoidal_closed.uncurry_natural_left,
  rw ←monoidal_closed.curry_eq_iff,
  rw ←monoidal_closed.uncurry_eq,
  rw monoidal_closed.curry_uncurry,
  rw category.id_comp,
  apply_instance,
  apply_instance
end⟩

@[simp] lemma monoidal_closed_uncurry_hom
  (f : Y ⟶ ihom X Z) :
  (monoidal_closed_uncurry f).hom = monoidal_closed.uncurry f.hom := rfl

/-- Intermediate step to constructing `monoidal_closed` -/
def monoidal_closed_hom_equiv :
  ((monoidal_category.tensor_left X).obj Y ⟶ Z) ≃
  (Y ⟶ (coyoneda.obj (op X)).obj Z) :=
{ to_fun := monoidal_closed_curry,
  inv_fun := monoidal_closed_uncurry,
  left_inv := by { intro f, apply Action.hom.ext, simp },
  right_inv := by { intro f, apply Action.hom.ext, simp } }

@[simp] lemma monoidal_closed_hom_equiv_apply
  (f : (monoidal_category.tensor_left X).obj Y ⟶ Z) :
  monoidal_closed_hom_equiv f = monoidal_closed_curry f := rfl

@[simp] lemma monoidal_closed_hom_equiv_symm_apply
  (f : Y ⟶ ihom X Z) :
  monoidal_closed_hom_equiv.symm f = monoidal_closed_uncurry f := rfl

/-- For a group `G`, if `V` is a closed monoidal category, then `Action V G` is a closed monoidal
category. -/
instance : monoidal_closed (Action V G) :=
-- ⟨λ X, ⟨⟨_, _⟩⟩⟩
{ closed' := λ X,
  { is_adj :=
    { right := coyoneda.obj (op X),
      adj := begin
        apply adjunction.mk_of_hom_equiv,
        refine ⟨λ Y Z, monoidal_closed_hom_equiv, _, _⟩,
        { intros Y Y' Z f f',
          apply Action.hom.ext,
          simp,
          rw ←monoidal_closed.uncurry_natural_left },
        { intros Y Z' Z f f',
          apply Action.hom.ext,
          simp,
          have : (ihom (unop (op (unop (op X)).V))).map = (ihom X.V).map := rfl,
          rw this,
          rw monoidal_closed.curry_natural_right,
          have : (ihom (unop (op X)).V).map = (ihom X.V).map := rfl,
          rw this }
      end }}}

end Action

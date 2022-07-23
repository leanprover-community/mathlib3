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

namespace Action

variables
  {V : Type (u+1)} [large_category V] [monoidal_category V] {G : Group.{u}}
  {X Y Z : Action V G} (g g' : G)

@[simp] lemma left_inv_g_tensor_comp
  {YV₁ YV₂ YV₃ : V} {fY₁ : YV₁ ⟶ YV₂} {fY₂ : YV₂ ⟶ YV₃} :
  (X.ρ (g⁻¹ : G) ⊗ fY₁) ≫ (X.ρ g ⊗ fY₂) = 𝟙 X.V ⊗ fY₁ ≫ fY₂ :=
by rw [←Action.ρ_Aut_apply_inv, ←Action.ρ_Aut_apply_hom, monoidal_category.inv_hom_id_tensor,
    monoidal_category.id_tensor_comp]

@[simp] lemma left_inv_g_tensor_comp_assoc
  {YV₁ YV₂ YV₃ ZV : V} {fY₁ : YV₁ ⟶ YV₂} {fY₂ : YV₂ ⟶ YV₃} {f : X.V ⊗ YV₃ ⟶ ZV} :
  (X.ρ (g⁻¹ : G) ⊗ fY₁) ≫ (X.ρ g ⊗ fY₂) ≫ f = (𝟙 X.V ⊗ fY₁ ≫ fY₂) ≫ f :=
by rw [←category.assoc, left_inv_g_tensor_comp]

@[simp] lemma left_g_inv_tensor_comp
  {YV₁ YV₂ YV₃ : V} {fY₁ : YV₁ ⟶ YV₂} {fY₂ : YV₂ ⟶ YV₃} :
  (X.ρ g ⊗ fY₁) ≫ (X.ρ (g⁻¹ : G) ⊗ fY₂) = 𝟙 X.V ⊗ fY₁ ≫ fY₂ :=
by rw [←Action.ρ_Aut_apply_inv, ←Action.ρ_Aut_apply_hom, monoidal_category.hom_inv_id_tensor,
    monoidal_category.id_tensor_comp]

@[simp] lemma left_g_inv_tensor_comp_assoc
  {YV₁ YV₂ YV₃ ZV : V} {fY₁ : YV₁ ⟶ YV₂} {fY₂ : YV₂ ⟶ YV₃} {f : X.V ⊗ YV₃ ⟶ ZV} :
  (X.ρ g ⊗ fY₁) ≫ (X.ρ (g⁻¹ : G) ⊗ fY₂) ≫ f = (𝟙 X.V ⊗ fY₁ ≫ fY₂) ≫ f :=
by rw [←category.assoc, left_g_inv_tensor_comp]

lemma tensor_left_g_id_comp_injective {f₁ f₂ : X.V ⊗ Y.V ⟶ Z.V} :
  (X.ρ g ⊗ 𝟙 Y.V) ≫ f₁ = (X.ρ g ⊗ 𝟙 Y.V) ≫ f₂ → f₁ = f₂ :=
begin
  intro h,
  have h' := congr_arg (category_struct.comp (X.ρ (g⁻¹ : G) ⊗ 𝟙 Y.V)) h,
  simp at h',
  exact h'
end

-- Consider adding "right" versions of the above lemmas

variables [monoidal_closed V] (X Y Z)

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
  { simp only [pre_comp_apply, inv_one, ρ_one, op_id, category_theory.functor.map_id,
      nat_trans.id_app, post_comp_apply, End.one_def],
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
      simp only [ihom_ρ, pre_comp_apply, post_comp_apply, functor.flip_map_app, category.assoc,
        nat_trans.naturality_assoc],
      apply congr_arg,
      rw [←functor.map_comp, ←functor.map_comp],
      apply congr_arg,
      apply f.comm },
  end,
  map_id' := by { intro Y, ext, simp only
    [Action.id_hom, category_theory.nat_trans.id_app, category_theory.functor.map_id], congr },
  map_comp' := by { intros, apply Action.hom.ext, simp } }

@[simp] lemma ihom_functor_obj (X : (Action V G)ᵒᵖ) :
  (ihom_functor X).obj Y = ihom (unop X) Y := rfl

@[simp] lemma ihom_functor_map_hom (X' : (Action V G)ᵒᵖ) (f : X ⟶ Y) :
  ((ihom_functor X').map f).hom =
  (monoidal_closed.internal_hom.flip.map f.hom).app (op (unop X').V) := rfl

@[simp] lemma internal_hom_obj (X : Vᵒᵖ) :
  monoidal_closed.internal_hom.obj X = ihom (unop X) := rfl

@[simp] lemma internal_hom_map {X Y : Vᵒᵖ} (f : X ⟶ Y) :
  monoidal_closed.internal_hom.map f = monoidal_closed.pre f.unop := rfl

@[simp] lemma internal_hom_obj_map (X : Vᵒᵖ) {Y Z : V} (f : Y ⟶ Z) :
  (monoidal_closed.internal_hom.obj X).map f = (ihom (unop X)).map f := rfl

variables {X Y Z}

/-- Elevate the curry on `V` to an `Action V G` hom. -/
def monoidal_closed_curry
  (f : (monoidal_category.tensor_left X).obj Y ⟶ Z) : Y ⟶ (ihom_functor (op X)).obj Z :=
⟨monoidal_closed.curry f.hom,
begin
  intro,
  dsimp,
  rw ←monoidal_closed.curry_natural_left,
  rw monoidal_closed.curry_eq_iff,
  apply tensor_left_g_id_comp_injective g,
  rw monoidal_category.tensor_id_comp_id_tensor_assoc,
  have := f.comm g,
  dsimp at this,
  rw [this, ←category.assoc, monoidal_closed.uncurry_natural_right, ←category.assoc],
  apply congr_fun,
  apply congr_arg,
  rw [monoidal_closed.uncurry_natural_left, monoidal_closed.uncurry_pre,
  monoidal_category.id_tensor_comp_tensor_id_assoc, left_g_inv_tensor_comp_assoc,
  category.id_comp, ←monoidal_closed.uncurry_eq, monoidal_closed.uncurry_curry]
end⟩

@[simp] lemma monoidal_closed_curry_hom
  (f : (monoidal_category.tensor_left X).obj Y ⟶ Z) :
  (monoidal_closed_curry f).hom = monoidal_closed.curry f.hom := rfl

/-- Elevate the uncurry on `V` to an `Action V G` hom. -/
def monoidal_closed_uncurry
  (f : Y ⟶ ihom X Z) : (monoidal_category.tensor_left X).obj Y ⟶ Z :=
⟨monoidal_closed.uncurry f.hom,
begin
  intro,
  dsimp,
  apply tensor_left_g_id_comp_injective g⁻¹,
  rw [Action.left_inv_g_tensor_comp_assoc, category.id_comp, ←monoidal_closed.uncurry_natural_left,
    f.comm],
  simp only [Action.pre_comp_apply, Action.internal_hom_obj_map, quiver.hom.unop_op, Action.ihom_ρ,
    functor.flip_map_app, Action.internal_hom_map, Action.post_comp_apply],
  dsimp,
  rw [←category.assoc, monoidal_closed.uncurry_natural_right, ←category.assoc],
  apply congr_fun,
  apply congr_arg,
  rw [monoidal_closed.uncurry_natural_left, monoidal_closed.uncurry_pre,
    monoidal_category.id_tensor_comp_tensor_id_assoc],
  apply tensor_left_g_id_comp_injective g,
  rw [Action.left_g_inv_tensor_comp_assoc, category.id_comp, Action.left_g_inv_tensor_comp_assoc,
    category.comp_id, monoidal_category.tensor_id, category.id_comp, monoidal_closed.uncurry_eq],
end⟩

@[simp] lemma monoidal_closed_uncurry_hom
  (f : Y ⟶ ihom X Z) :
  (monoidal_closed_uncurry f).hom = monoidal_closed.uncurry f.hom := rfl

/-- Intermediate step to constructing `monoidal_closed` -/
def monoidal_closed_hom_equiv :
  ((monoidal_category.tensor_left X).obj Y ⟶ Z) ≃
  (Y ⟶ (ihom_functor (op X)).obj Z) :=
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
    { right := ihom_functor (op X),
      adj := begin
        apply adjunction.mk_of_hom_equiv,
        refine ⟨λ Y Z, monoidal_closed_hom_equiv, _, _⟩,
        { intros Y Y' Z f f',
          apply Action.hom.ext,
          simp only [Action.monoidal_closed_uncurry_hom,
            category_theory.monoidal_category.tensor_left_map,
            Action.id_hom, Action.tensor_hom, Action.comp_hom,
            Action.monoidal_closed_hom_equiv_symm_apply],
          rw ←monoidal_closed.uncurry_natural_left },
        { intros Y Z' Z f f',
          apply Action.hom.ext,
          simp only [Action.monoidal_closed_hom_equiv_apply, Action.internal_hom_obj_map,
            Action.ihom_functor_map_hom, Action.comp_hom, category_theory.functor.flip_map_app,
            Action.monoidal_closed_curry_hom],
          dsimp,
          rw monoidal_closed.curry_natural_right }
      end }}}

end Action

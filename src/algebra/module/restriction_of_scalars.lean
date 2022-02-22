/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.CommRing
import algebra.category.Module.basic
import linear_algebra.tensor_product

open_locale tensor_product

namespace change_of_rings

namespace restriction_of_scalars

universe u

variables {R S : CommRing.{u}} -- [ring R] [ring S] -- (f : R →+* S)
variables (N : Module S) -- [add_comm_monoid N] [module S N]
variable (f : R ⟶ S)
include f

/--Definition of scalar multiplication in restriction of scalars-/
def has_scalar : has_scalar R N :=
{ smul := λ r n,  f r • n}

-- #check (restriction_of_scalars.has_scalar N f).smul
localized "attribute [instance] restriction_of_scalars.has_scalar" in change_of_rings

@[simp] lemma smul_def (r : R) (n : N) :
  @has_scalar.smul R N (restriction_of_scalars.has_scalar N f) r n = f r • n := rfl

def is_module : module R N :=
{ one_smul := by simp,
  mul_smul := by simp [mul_smul],
  smul_add := by simp [smul_add],
  smul_zero := by simp,
  add_smul := by simp [add_smul],
  zero_smul := by simp,
  ..(restriction_of_scalars.has_scalar N f) }.

localized "attribute [instance] restriction_of_scalars.is_module" in change_of_rings

/--
Given a ring homomorphism `f : R ⟶ S`, and an `S`-module `N`, we can turn `N` into an `R`-module.
This is called restriction_of_scalar
-/
def module :
  Module R :=
{ carrier := N,
  is_add_comm_group := infer_instance,
  is_module := is_module N f }.

localized "notation f `^*` N := restriction_of_scalars.module N f" in change_of_rings

instance has_scalar' : _root_.has_scalar S (f ^* N) :=
{ smul := λ s n, @has_scalar.smul S N _ s n }.

@[simp] lemma smul_def' (r : R) (n : f ^* N) : r • n = f r • n := rfl

/--restrictino of scalar is a functor from `S`-modules to `R`-modules.-/
def functor : Module S ⥤ Module R :=
{ obj := λ N, f ^* N,
  map := λ N₁ N₂ l,
    { to_fun := l,
      map_add' := λ x y, by rw [linear_map.map_add],
      map_smul' := λ r y, begin
        simp only [smul_def', ring_hom.id_apply],
        convert linear_map.map_smul l (f r) y,
      end } }

end restriction_of_scalars

namespace extension_of_scalars

universe u

variables {R S : CommRing.{u}} (f : R ⟶ S) (M : Module R)
include f

/--
This action gives `S` an `R`-module strucutre
-/
def is_R_mod_S : module R S := restriction_of_scalars.is_module ⟨S⟩ f

localized "attribute [instance] extension_of_scalars.is_R_mod_S" in change_of_rings

@[simp] lemma smul_def (r : R) (s : S) :
  @has_scalar.smul _ _ begin
    haveI := is_R_mod_S f,
    resetI,
    apply_instance
  end r s = f r * s := rfl


include M
localized "notation M `⊗[` R `,` f `]` S := @tensor_product R _ M S _ _ _
  (extension_of_scalars.is_R_mod_S f)" in change_of_rings

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
@[reducible] def has_scalar_S_M_tensor_S : _root_.has_scalar S (M ⊗[R, f] S) :=
{ smul := λ s', @tensor_product.lift R _ M S (M ⊗[R, f] S) _ _ _ _ (is_R_mod_S f) _
  { to_fun := λ m,
    { to_fun := λ s, @tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m (s * s'),
      map_add' := λ x y, by rw [add_mul, tensor_product.tmul_add],
      map_smul' := λ x y, begin
        rw [ring_hom.id_apply],
        rw [smul_def f x, mul_assoc, ←smul_def],
        erw tensor_product.tmul_smul,
      end },
    map_add' := λ _ _, begin
      ext s, simp only [linear_map.coe_mk, linear_map.add_apply],
      rw tensor_product.add_tmul
    end,
    map_smul' := λ _ _, begin
      ext s, simp only [linear_map.smul_apply, ring_hom.id_apply, linear_map.coe_mk],
      rw @tensor_product.smul_tmul R _ R _ M S _ _ _ (is_R_mod_S f) _ begin
        haveI := is_R_mod_S f,
        resetI,
        apply_instance,
      end _,
      rw tensor_product.tmul_smul
    end } }

local attribute [instance] has_scalar_S_M_tensor_S

lemma has_scalar_S_M_tensor_S.smul_pure_tensor (s s' : S) (m : M) :
  s • (@tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m s') =
  @tensor_product.tmul R _ M S _ _ _ (is_R_mod_S f) m (s * s') :=
begin
  unfold has_scalar.smul, simp only [tensor_product.lift.tmul, linear_map.coe_mk],
  rw mul_comm,
end

/--
See above
-/
def mul_action_S_M_tensor_S : _root_.mul_action S (M ⊗[R, f] S) :=
{ one_smul := λ x, begin
    apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x;
    unfold has_scalar.smul,
    { simp only [map_zero] },
    { intros m s, simp only [tensor_product.lift.tmul, linear_map.coe_mk, mul_one], },
    { intros x y ihx ihy, simp only [map_add, ihx, ihy] },
  end,
  mul_smul := λ s s' x, begin
    apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x;
    unfold has_scalar.smul,
    { simp only [map_zero] },
    { intros m s'', simp only [tensor_product.lift.tmul, linear_map.coe_mk],
      rw [mul_comm s s', mul_assoc], },
    { intros x y ihx ihy,
      conv_lhs { rw [map_add] },
      conv_rhs { rw [map_add, map_add, ←ihx, ←ihy], } }
  end,
  ..(has_scalar_S_M_tensor_S f M) }

local attribute [instance] mul_action_S_M_tensor_S

@[simp] lemma distrib_mul_action_S_M_tensor_S.smul_zero (s : S) : s • (0 : M ⊗[R, f] S) = 0 :=
begin
  unfold has_scalar.smul,
  simp only [map_zero],
end

def distrib_mul_action_S_M_tensor_S : _root_.distrib_mul_action S (M ⊗[R, f] S) :=
{ smul_zero := by simp,
  smul_add := λ r x y, begin
    apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
    { simp, },
    { intros m s, unfold has_scalar.smul, simp only [map_add], },
    { intros z z' ihz ihz',
      unfold has_scalar.smul, simp only [map_add], }
  end }

/--
See above
-/
@[reducible] def module : Module S :=
{ carrier := M ⊗[R, f] S,
  is_module :=
    { add_smul := λ s s' x, begin
        apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
        { rw [distrib_mul_action_S_M_tensor_S.smul_zero,
              distrib_mul_action_S_M_tensor_S.smul_zero,
              distrib_mul_action_S_M_tensor_S.smul_zero, zero_add] },
        { rintros m s'',
          rw [has_scalar_S_M_tensor_S.smul_pure_tensor,
              has_scalar_S_M_tensor_S.smul_pure_tensor,
              has_scalar_S_M_tensor_S.smul_pure_tensor, add_mul,
              tensor_product.tmul_add] },
        { rintros x y ihx ihy,
          conv_lhs { rw [smul_add, ihx, ihy] },
          have : s • x + s' • x + (s • y + s' • y) = s • x + s • y + (s' • x + s' • y),
          { rw [add_assoc, add_assoc],
            apply congr_arg2 (+), refl,
            rw [←add_assoc, ←add_assoc],
            apply congr_arg2 (+), rw add_comm, refl, },
          erw this,
          conv_rhs { rw [smul_add, smul_add] },
          refl }
      end,
      zero_smul := λ x, begin
        apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
        { rw smul_zero },
        { rintros m s,
          rw [has_scalar_S_M_tensor_S.smul_pure_tensor, zero_mul, tensor_product.tmul_zero], },
        { rintros x y ihx ihy, rw [smul_add, ihx, ihy, zero_add] }
      end,
      ..(distrib_mul_action_S_M_tensor_S f M) } }

localized "notation f `_*` M := extension_of_scalars.module f M" in change_of_rings

omit M
/--
Extension of scalars is a functor where an `R`-module `M` is sent to `M ⊗ S` and
`l : M1 ⟶ M2` is sent to `m ⊗ s ↦ l m ⊗ s`
-/
def map {M1 M2 : Module R} (l : M1 ⟶ M2) : (module f M1) ⟶ (module f M2) :=
{ to_fun := @tensor_product.lift R _ M1 S (M2 ⊗[R, f] S) _ _ _ _ (is_R_mod_S f) _
       {to_fun := λ m : M1,
        { to_fun := λ (s : ↥S), @tensor_product.tmul R _ M2 S _ _ _ (is_R_mod_S f) (l m) s,
          map_add' := λ s s', by rw tensor_product.tmul_add,
          map_smul' := λ r s, by rw [ring_hom.id_apply, tensor_product.tmul_smul] },
        map_add' := λ m m', begin
          ext s, simp only [map_add, linear_map.coe_mk, linear_map.add_apply],
          rw tensor_product.add_tmul
        end,
        map_smul' := λ s m, begin
          ext s,
          simp only [linear_map.smul_apply, ring_hom.id_apply,
            linear_map.coe_mk, linear_map.map_smulₛₗ],
          rw @tensor_product.smul_tmul R _ R _ M2 S _ _ _ (is_R_mod_S f) _
            begin
              haveI := is_R_mod_S f,
              resetI,
              apply_instance
            end,
          rw tensor_product.tmul_smul
        end},
  map_add' := λ x y, by rw map_add,
  map_smul' := λ s x, begin
    apply @tensor_product.induction_on R _ M1 S _ _ _ (is_R_mod_S f) _ x,
    { rw [smul_zero, map_zero, smul_zero], },
    { rintros m s',
      rw [has_scalar_S_M_tensor_S.smul_pure_tensor, ring_hom.id_apply,
        tensor_product.lift.tmul, tensor_product.lift.tmul, linear_map.coe_mk, linear_map.coe_mk,
        has_scalar_S_M_tensor_S.smul_pure_tensor], },
    { rintros x y ihx ihy,
      rw [ring_hom.id_apply] at ihx ihy ⊢,
      rw [smul_add, linear_map.map_add, ihx, ihy, linear_map.map_add, smul_add], }
  end }

/--
The functor extension of scalars
-/
def functor : Module.{u} R ⥤ Module.{u} S :=
{ obj := λ M, f _* M,
  map := λ M1 M2 l, map f l,
  map_id' := λ M, begin
    ext x, rw [map, Module.id_apply],
    apply @tensor_product.induction_on R _ M S _ _ _ (is_R_mod_S f) _ x,
    { rw map_zero },
    { intros m s, rw [linear_map.coe_mk, tensor_product.lift.tmul], refl, },
    { intros x y ihx ihy, rw [linear_map.coe_mk] at ihx ihy ⊢,
      rw [map_add, ihx, ihy], }
  end,
  map_comp' := λ M1 M2 M3 g h, begin
    ext x,
    rw [map, map, map, linear_map.coe_mk, category_theory.comp_apply,
      linear_map.coe_mk, linear_map.coe_mk],
    apply @tensor_product.induction_on R _ _ S _ _ _ (is_R_mod_S f) _ x,
    { rw [map_zero, map_zero, map_zero], },
    { rintros m s, rw [tensor_product.lift.tmul, tensor_product.lift.tmul], refl, },
    { rintros x y ihx ihy,
      rw [map_add, ihx, ihy, map_add, map_add], }
  end }.

end extension_of_scalars

section adjunction

universe u

open category_theory
open_locale change_of_rings

variables {R S : CommRing.{u}} (f : R ⟶ S) (X : Module.{u} R) (Y : Module.{u} S)

def backward (g : X ⟶ (restriction_of_scalars.functor f).obj Y) :
  (extension_of_scalars.functor f).obj X ⟶ Y :=
{ to_fun := λ z,
  let m1 := extension_of_scalars.is_R_mod_S f,
    m2 : module R Y := restriction_of_scalars.is_module _ f in
  begin
    resetI,
    refine tensor_product.lift
      { to_fun := λ x,
          { to_fun := λ s, _,
            map_add' := _,
            map_smul' := _, },
        map_add' := _,
        map_smul' := _ } z,
    { -- `x ⊗ s ↦ s • g x` in Y
      exact s • (g x : Y) },
    { intros, rw add_smul, },
    { intros,
      simp only [extension_of_scalars.smul_def, ring_hom.id_apply,
        restriction_of_scalars.smul_def', mul_smul],
      refl, },
    { intros x y,
      ext s,
      simp only [linear_map.coe_mk, smul_add, linear_map.add_apply, map_add], },
    { intros r x,
      ext s,
      simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply,
        linear_map.map_smul],
      erw [← mul_smul, mul_comm, mul_smul],
      refl, },
  end,
  map_add' := λ z1 z2, by simp only [map_add],
  map_smul' := λ r z, begin
    rw [ring_hom.id_apply],
    induction z using tensor_product.induction_on with x y x y ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { rw extension_of_scalars.has_scalar_S_M_tensor_S.smul_pure_tensor,
      simp [tensor_product.lift.tmul],
      rw [mul_smul], },
    { simp only [smul_add, map_add],
      dsimp only at ih1 ih2,
      rw [ih1, ih2], },
  end }.

def forward (g : (extension_of_scalars.functor f).obj X ⟶ Y) :
  X ⟶ (restriction_of_scalars.functor f).obj Y :=
{ to_fun := λ x, g begin
    refine @tensor_product.tmul R _ X S _ _ _ (restriction_of_scalars.is_module ⟨S⟩ f) x 1,
  end,
  map_add' := λ x x', by rw [tensor_product.add_tmul, map_add],
  map_smul' := λ r x, begin
    rw [ring_hom.id_apply],
    have eq0 :
      -- (r • x) ⊗ₜ[R] 1 = x ⊗ₜ[R] (r • 1)
      (@tensor_product.tmul R _ X S _ _ _ (restriction_of_scalars.is_module ⟨S⟩ f) (r • x) 1) =
      @tensor_product.tmul R _ X S _ _ _ (restriction_of_scalars.is_module ⟨S⟩ f) x (f r • 1),
    { erw @tensor_product.smul_tmul R _ R _ X S _ _ _
        (restriction_of_scalars.is_module ⟨S⟩ f) _ begin
          haveI := (restriction_of_scalars.is_module ⟨S⟩ f),
          apply_instance
        end _ r x 1,
      congr', },
    have eq1 := congr_arg g eq0,
    erw ← linear_map.map_smul,
    erw eq1,
    congr' 1,
    rw extension_of_scalars.has_scalar_S_M_tensor_S.smul_pure_tensor,
    refl,
  end }

def equiv :
  ((extension_of_scalars.functor f).obj X ⟶ Y) ≃ (X ⟶ (restriction_of_scalars.functor f).obj Y) :=
{ to_fun := forward f X Y,
  inv_fun := backward f X Y,
  left_inv := λ g, begin
    ext z,
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul,
      simp only [linear_map.coe_mk],
      change s • g _ = _,
      rw [← linear_map.map_smul, extension_of_scalars.has_scalar_S_M_tensor_S.smul_pure_tensor,
        mul_one], },
    { rw [map_add, map_add, ih1, ih2], }
  end,
  right_inv := λ g, begin
    ext,
    unfold forward backward,
    simp only [linear_map.coe_mk, tensor_product.lift.tmul, one_smul],
  end }

def unit.map : X ⟶ ((extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f).obj X) :=
{ to_fun := λ x, @tensor_product.tmul R _ X S _ _ _ (restriction_of_scalars.is_module ⟨S⟩ f) x 1,
  map_add' := λ x x', by { rw tensor_product.add_tmul, },
  map_smul' := λ r x, begin
    erw [@tensor_product.smul_tmul R _ R _ X S _ _ _
        (restriction_of_scalars.is_module ⟨S⟩ f) _ begin
          haveI := (restriction_of_scalars.is_module ⟨S⟩ f),
          apply_instance
        end _ r x 1, ring_hom.id_apply,
        extension_of_scalars.has_scalar_S_M_tensor_S.smul_pure_tensor],
    congr,
  end }.

def unit : 𝟭 (Module ↥R) ⟶ extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f :=
{ app := unit.map f,
  naturality' := λ X X' g, begin
    ext,
    simp only [unit.map, functor.id_map, Module.coe_comp, linear_map.coe_mk,
      function.comp_app, functor.comp_map],
    have eq1 : (restriction_of_scalars.functor f).map ((extension_of_scalars.functor f).map g) =
      { to_fun := (extension_of_scalars.functor f).map g, map_add' := _, map_smul' := _ } := rfl,
    rw eq1,
    simp only [linear_map.coe_mk],
    erw tensor_product.lift.tmul,
    simp only [linear_map.coe_mk],
  end }

def counit.map : (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f).obj Y ⟶ Y :=
{ to_fun :=
    let m1 : module R S := restriction_of_scalars.is_module ⟨S⟩ f,
        m2 : module R Y := restriction_of_scalars.is_module Y f in
    begin
      resetI,
      refine tensor_product.lift
        { to_fun := λ y,
            { to_fun := λ s, _,
              map_add' := _,
              map_smul' := _ },
          map_add' := _,
          map_smul' := _ },
      { exact s • (y : Y), },
      { intros s s', rw add_smul, },
      { intros r s,
        rw [ring_hom.id_apply, restriction_of_scalars.smul_def,
          @restriction_of_scalars.smul_def R S ⟨S⟩ f, smul_eq_mul, mul_smul], },
      { intros y1 y2,
        ext,
        simp only [linear_map.coe_mk, smul_add, linear_map.add_apply], },
      { intros r y,
        ext s,
        simp only [ring_hom.id_apply, restriction_of_scalars.smul_def',
          linear_map.coe_mk, linear_map.smul_apply],
        erw [← mul_smul, mul_comm, mul_smul],
        refl, },
    end,
  map_add' := λ z1 z2, by simp only [map_add],
  map_smul' := λ s z, begin
    simp only [ring_hom.id_apply],
    induction z using tensor_product.induction_on with x s' z1 z2 ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { erw extension_of_scalars.has_scalar_S_M_tensor_S.smul_pure_tensor,
      simp only [linear_map.coe_mk, tensor_product.lift.tmul],
      rw mul_smul, },
    { rw [smul_add, map_add, map_add, ih1, ih2, smul_add], },
  end }.

def counit : (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f) ⟶ (𝟭 _) :=
{ app := counit.map f,
  naturality' := λ Y Y' g, begin
    ext z,
    simp only [functor.comp_map, Module.coe_comp, function.comp_app, functor.id_map],
    induction z using tensor_product.induction_on with y s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { unfold counit.map,
      erw [tensor_product.lift.tmul, tensor_product.lift.tmul],
      simp only [linear_map.coe_mk, linear_map.map_smulₛₗ, ring_hom.id_apply],
      refl, },
    { rw [map_add, map_add, ih1, ih2, map_add, map_add], }
  end }

def adjunction : adjunction (extension_of_scalars.functor f) (restriction_of_scalars.functor f) :=
{ hom_equiv := equiv f,
  unit := unit f,
  counit := counit f,
  hom_equiv_unit' := λ X Y g, begin
    ext x,
    unfold equiv unit,
    simp only [equiv.coe_fn_mk, Module.coe_comp, function.comp_app],
    unfold unit.map forward,
    simp only [linear_map.coe_mk],
    refl,
  end,
  hom_equiv_counit' := λ X Y g, begin
    ext z,
    unfold equiv counit,
    simp only [equiv.coe_fn_symm_mk, Module.coe_comp, function.comp_app],
    unfold backward counit.map,
    simp only [linear_map.coe_mk],
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul, },
    { simp only [map_add, ih1, ih2], }
  end }.

end adjunction

end change_of_rings

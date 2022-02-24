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
variable (f : R ⟶ S)
variables (N : Module S) -- [add_comm_monoid N] [module S N]
include f

@[reducible] def module :
  Module R :=
{ carrier := N,
  is_module := module.comp_hom _ f, }.
localized "notation f `^*` N := restriction_of_scalars.module f N" in change_of_rings

def is_module : _root_.module R N := (f ^* N).is_module

localized "attribute [instance] restriction_of_scalars.is_module" in change_of_rings


instance has_scalar' : _root_.has_scalar S (f ^* N) :=
{ smul := λ s n, @has_scalar.smul S N _ s n }.

@[simp] lemma smul_def' (r : R) (n : f ^* N) : r • n = f r • n := rfl
@[simp] lemma smul_def (r : R) (n : N) :
  @has_scalar.smul R N begin
    haveI := is_module f N,
    apply_instance,
  end r n = f r • n := rfl

def compatible_smul (N₁ N₂ : Module S) :
  let m1 := is_module f N₁,
      m2 := is_module f N₂,
      m3 := is_module f ⟨S⟩ in
  begin
    resetI,
    exact linear_map.compatible_smul N₁ N₂ R S
  end :=
let m1 := is_module f N₁,
    m2 := is_module f N₂,
    m3 := is_module f ⟨S⟩ in
begin
  resetI,
  fconstructor,
  intros g r n,
  calc  g (r • n)
      = g (f r • n) : by congr' 1
    ... = f r • g n : by { erw linear_map.map_smul, },
end
/--restriction of scalar is a functor from `S`-modules to `R`-modules.-/
def functor : Module S ⥤ Module R :=
{ obj := λ N, f ^* N,
  map := λ N₁ N₂ l,
  let m1 := is_module f N₁,
      m2 := is_module f N₂,
      m3 := is_module f ⟨S⟩,
      m4 := compatible_smul f N₁ N₂ in
  begin
    dsimp only at m4,
    resetI,
    exact linear_map.restrict_scalars R l,
  end }.

localized "notation f `⥤^*` M := (restriction_of_scalars.functor f).obj M" in change_of_rings

end restriction_of_scalars

namespace extension_of_scalars

open category_theory tensor_product

universe u

variables {R S : CommRing.{u}} (f : R ⟶ S) (M : Module R)
include f

-- /--
-- This action gives `S` an `R`-module strucutre
-- -/
-- def is_R_mod_S : module R S := restriction_of_scalars.is_module ⟨S⟩ f

-- localized "attribute [instance] extension_of_scalars.is_R_mod_S" in change_of_rings

-- @[simp] lemma smul_def (r : R) (s : S) :
--   @has_scalar.smul _ _ begin
--     haveI := is_R_mod_S f,
--     resetI,
--     apply_instance
--   end r s = f r * s := rfl


include M
localized "notation M `⊗[` R `,` f `]` S := @tensor_product R _ M S _ _ _
  (restriction_of_scalars.is_module f ⟨S⟩)" in change_of_rings
localized "notation m `⊗ₜ[` R `,` f `]` s := @tensor_product.tmul R _ _ _ _ _ _
  (restriction_of_scalars.is_module f ⟨_⟩) m s" in change_of_rings

def smul_by (s : S) : (M ⊗[R, f] S) ⟶ (M ⊗[R, f] S) :=
let m : module R S := restriction_of_scalars.is_module f ⟨S⟩ in
begin
  resetI,
  refine tensor_product.lift _,
  refine ⟨_, _, _⟩,
  { -- we define `m ↦ (s' ↦ m ⊗ (s * s'))`
    refine λ m, ⟨λ s', m ⊗ₜ[R, f] (s * s'), _, _⟩,
    { -- map_add
      intros,
      erw [mul_add, tmul_add], },
    { -- map_smul
      intros,
      rw [ring_hom.id_apply, smul_tmul', smul_tmul],
      congr' 1,
      rw [restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul, ← mul_assoc, mul_comm s,
        mul_assoc, restriction_of_scalars.smul_def f ⟨S⟩, smul_eq_mul],
    }, },
  { intros,
    ext,
    simp only [linear_map.coe_mk, map_add, add_tmul],
    refl, },
  { intros,
    ext,
    simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply],
    rw [tensor_product.smul_tmul'], }
end.

lemma smul_by.pure_tensor (s s' : S) (m : M) :
  (smul_by f M s (m ⊗ₜ[R, f] s')) =
  m ⊗ₜ[R, f] (s * s') :=
begin
  simp only [smul_by, tensor_product.lift.tmul, linear_map.coe_mk],
end

lemma smul_by.one : smul_by f M 1 = 𝟙 _ :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ _ _ ih1 ih2,
  { simpa only [smul_by, map_zero], },
  { simpa only [smul_by.pure_tensor, one_mul], },
  { simp only [category_theory.types_id_apply] at ih1 ih2 ⊢,
    conv_rhs { rw [← ih1, ← ih2] },
    convert map_add _ _ _, },
end.

lemma smul_by.mul (s s' : S) : smul_by f M (s * s') = smul_by f M s' ≫ smul_by f M s :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp only [smul_by, map_zero, types_comp_apply], },
  { simp [smul_by, mul_assoc], },
  { convert congr_arg2 (+) ih1 ih2 using 1,
    { convert map_add _ _ _ },
    { simp only [types_comp_apply],
      calc  smul_by f M s (smul_by f M s' (x + y))
          = smul_by f M s (smul_by f M s' x + smul_by f M s' y)
          : by { congr' 1, convert map_add _ _ _}
      ... = smul_by f M s (smul_by f M s' x) + smul_by f M s (smul_by f M s' y)
          : by convert map_add _ _ _, }, }
end.

lemma smul_by.apply_zero (s : S) : smul_by f M s 0 = 0 :=
by simp only [smul_by, map_zero]

lemma smul_by.apply_add (s : S) (a b) : smul_by f M s (a + b) = smul_by f M s a + smul_by f M s b :=
by simp [smul_by, map_add]


lemma smul_by.add (s s') : smul_by f M (s + s') = smul_by f M s + smul_by f M s' :=
begin
  ext x,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp [smul_by], },
  { simp [smul_by, add_mul, tmul_add], },
  { simp only [pi.add_apply, smul_by.apply_add, ih1, ih2],
    rw show ∀ (a b c d : M ⊗[R, f] S), a + b + (c + d) = a + c + (b + d), from _,
    intros,
    -- `ring` doesn't work here for some reason
    rw calc a + b + (c + d) = a + (b + (c + d)) : by rw add_assoc
      ... = a + (b + c + d) : by rw add_assoc
      ... = a + (c + b + d) : by rw add_comm b c
      ... = a + (c + (b + d)) : by rw add_assoc
      ... = a + c + (b + d) : by rw add_assoc, }
end.

lemma smul_by.zero : smul_by f M 0 = 0 :=
begin
  ext,
  induction x using tensor_product.induction_on with _ _ x y ih1 ih2,
  { simp [smul_by], },
  { simp [smul_by], },
  { simp [smul_by.apply_add, ih1, ih2], }
end.

/--
Since `S` has an `R`-module structure, `M ⊗[R] S` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (m ⊗ s') := m ⊗ (s * s')`
-/
@[reducible] def has_scalar_S_M_tensor_S : _root_.has_scalar S (M ⊗[R, f] S) :=
{ smul := λ s', smul_by f M s' }

local attribute [instance] has_scalar_S_M_tensor_S

lemma smul_pure_tensor (s s' : S) (m : M) :
  (s • (m ⊗ₜ[R, f] s')) =
  m ⊗ₜ[R, f] (s * s') :=
by simp only [smul_by, tensor_product.lift.tmul, linear_map.coe_mk]

@[simp] lemma smul_zero (s : S) : s • (0 : M ⊗[R, f] S) = 0 :=
by simp [smul_by]

/--
See above
-/
def mul_action_S_M_tensor_S : _root_.mul_action S (M ⊗[R, f] S) :=
{ one_smul := λ x, begin
    change smul_by _ _ _ _ = _,
    rw smul_by.one f M,
    refl,
  end,
  mul_smul := λ s s' x, begin
    change smul_by _ _ _ _ = smul_by _ _ _ (smul_by _ _ _ _),
    rw smul_by.mul f M,
    refl,
  end,
  ..(has_scalar_S_M_tensor_S f M) }.

localized "attribute [instance] extension_of_scalars.mul_action_S_M_tensor_S" in change_of_rings

def distrib_mul_action_S_M_tensor_S : _root_.distrib_mul_action S (M ⊗[R, f] S) :=
{ smul_zero := λ s, by { change smul_by f M s 0 = 0, apply smul_by.apply_zero, },
  smul_add := λ s x y, begin
    change smul_by f M s (x + y) = smul_by f M s x + smul_by f M s y,
    apply smul_by.apply_add,
  end }

def is_module : module S (M ⊗[R, f] S) :=
{ add_smul := λ s s' x, begin
    change smul_by _ _ _ _ = smul_by _ _ _ _ + smul_by _ _ _ _,
    rw smul_by.add,
    refl,
  end,
  zero_smul := λ x, begin
    change smul_by _ _ _ _ = _,
    rw smul_by.zero,
    refl,
  end,
  ..(distrib_mul_action_S_M_tensor_S f M) }.

def is_module' : module R (M ⊗[R, f] S) :=
infer_instance

-- def compatible_smul (M1 M2 : Module R) :
--   linear_map.compatible_smul (M1 ⊗[R, f] S) (M2 ⊗[R, f] S) S R :=
-- let im1 : module R S := restriction_of_scalars.is_module f ⟨S⟩,
--     im2 : module S (M1 ⊗[R, f] S) := is_module f M1,
--     im3 : module S (M2 ⊗[R, f] S) := is_module f M2 in
-- ⟨λ g s x, begin
--   resetI,
--   induction x using tensor_product.induction_on with m1 s' z1 z2 ih1 ih2,
--   { simp [smul_by.apply_zero], },
--   { simp only [smul_by.pure_tensor],
--     revert s,
--     induction g (m1 ⊗ₜ[R, f] s') using tensor_product.induction_on,
--     rw ← lift.equiv_symm_apply R M1 S (M2 ⊗[R, f] S) g m1 (s * s'),
--     rw ← lift.equiv_symm_apply R M1 S (M2 ⊗[R, f] S) g m1 s',
--     -- dsimp only,
--     -- squeeze_dsimp,
--     -- type_check (tensor_product.lift.equiv R M1 S (M2 ⊗[R, f] S)).symm g m1 s,
--     sorry },
--   { erw [map_add, smul_add s z1 z2, map_add, ih1, ih2, smul_add s (g z1) (g z2)],
--     refl, },
-- end⟩

localized "attribute [instance] extension_of_scalars.is_module extension_of_scalars.is_module'"
  in change_of_rings
/--
See above
-/
def module : Module S :=
{ carrier := M ⊗[R, f] S,
  is_module := is_module f M }

localized "notation f `_*` M := extension_of_scalars.module f M" in change_of_rings

omit M
/--
Extension of scalars is a functor where an `R`-module `M` is sent to `M ⊗ S` and
`l : M1 ⟶ M2` is sent to `m ⊗ s ↦ l m ⊗ s`
-/
def map {M1 M2 : Module R} (l : M1 ⟶ M2) : (f _* M1) ⟶ (f _* M2) :=
let im1 : _root_.module R S := restriction_of_scalars.is_module f ⟨S⟩,
    im2 : _root_.module R (f _* M2) := is_module' f M2 in
begin
  resetI,
  refine
    { to_fun := tensor_product.lift { to_fun := λ m1, _, map_add' := _, map_smul' := _ },
      map_add' := _,
      map_smul' := _ },
  { -- `S ⟶ f _* M2` given by `s ↦ l m ⊗ s`
    refine { to_fun := λ s, (l m1) ⊗ₜ[R, f] s, map_add' := _, map_smul' := _ },
    { -- map_add
      intros,
      rw [tmul_add], },
    { -- map_smul
      intros,
      rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩ r x, smul_tmul',
        smul_tmul],
      refl, } },
  { intros m m',
    ext s,
    simp [add_tmul], },
  { intros r m,
    ext s,
    simp [smul_tmul], },
  { intros z1 z2,
    simp, },
  { intros s z,
    induction z using tensor_product.induction_on with _ _ z1 z2 ih1 ih2,
    { simp [smul_zero], },
    { simp [smul_pure_tensor], },
    { rw [smul_add, map_add, ring_hom.id_apply, ih1, ih2, map_add, smul_add,
        ring_hom.id_apply], } }
end.

/--
The functor extension of scalars
-/
def functor : Module.{u} R ⥤ Module.{u} S :=
{ obj := λ M, f _* M,
  map := λ M1 M2 l, map f l,
  map_id' := λ M, begin
    ext x,
    rw [map, Module.id_apply],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { rw map_zero },
    { rw [linear_map.coe_mk, tensor_product.lift.tmul], refl, },
    { rw [linear_map.coe_mk] at ihx ihy ⊢,
      rw [map_add, ihx, ihy], }
  end,
  map_comp' := λ M1 M2 M3 g h, begin
    ext x,
    rw [map, map, map, linear_map.coe_mk, category_theory.comp_apply,
      linear_map.coe_mk, linear_map.coe_mk],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { rw [map_zero, map_zero, map_zero], },
    { rw [tensor_product.lift.tmul, tensor_product.lift.tmul], refl, },
    { rw [map_add, ihx, ihy, map_add, map_add], }
  end }.

localized "notation f `⥤_*` M := (extension_of_scalars.functor f).obj M" in change_of_rings

end extension_of_scalars

section adjunction

universe u

open category_theory tensor_product
open_locale change_of_rings

variables {R S : CommRing.{u}} (f : R ⟶ S) (X : Module.{u} R) (Y : Module.{u} S)

def backward (g : X ⟶ (f ⥤^* Y)) :
  (f ⥤_* X) ⟶ Y :=
{ to_fun := λ z,
  let m1 := restriction_of_scalars.is_module f ⟨S⟩,
      m2 : module R Y := restriction_of_scalars.is_module f Y,
      m3 : module S (f ⥤^* Y) := Y.is_module in
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
    { intros r s,
      rw [ring_hom.id_apply],
      calc  (r • s) • g x
          = (f r * s) • g x : rfl
      ... = f r • s • g x : by rw [mul_smul], },
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
    { erw [extension_of_scalars.smul_pure_tensor],
      simp [tensor_product.lift.tmul, mul_smul], },
    { simp only [smul_add, map_add],
      dsimp only at ih1 ih2,
      rw [ih1, ih2], },
  end }.

def forward (g : (f ⥤_* X) ⟶ Y) :
  X ⟶ (f ⥤^* Y) :=
let m1 : module R S := restriction_of_scalars.is_module f ⟨S⟩,
    m2 : module R Y := restriction_of_scalars.is_module f Y in
{ to_fun := λ x, g (x ⊗ₜ[R, f] 1),
  map_add' := λ x x', by rw [tensor_product.add_tmul, map_add],
  map_smul' := λ r x, begin
    resetI,
    rw [ring_hom.id_apply],
    calc  g ((r • x) ⊗ₜ[R, f] (1 : S))
        = g (x ⊗ₜ[R, f] (r • 1)) : by rw smul_tmul
    ... = g (x ⊗ₜ[R, f] (f r • 1)) : by rw restriction_of_scalars.smul_def f ⟨S⟩
    ... = g (f r • (x ⊗ₜ[R, f] 1)) : by congr' 1
    ... = f r • g (x ⊗ₜ[R, f] 1) : by rw linear_map.map_smul
    ... = r • g (x ⊗ₜ[R, f] 1) : rfl,
  end }.

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
      rw [← linear_map.map_smul, extension_of_scalars.smul_pure_tensor, mul_one], },
    { rw [map_add, map_add, ih1, ih2], }
  end,
  right_inv := λ g, begin
    ext,
    unfold forward backward,
    simp only [linear_map.coe_mk, tensor_product.lift.tmul, one_smul],
  end }.

def unit.map : X ⟶ ((extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f).obj X) :=
let m1 : module R S := restriction_of_scalars.is_module f ⟨S⟩ in
{ to_fun := λ x, x ⊗ₜ[R, f] 1,
  map_add' := λ x x', by { rw tensor_product.add_tmul, },
  map_smul' := λ r x, begin
    resetI,
    erw [smul_tmul, extension_of_scalars.smul_pure_tensor],
    congr,
  end }.

def unit : 𝟭 (Module ↥R) ⟶ extension_of_scalars.functor f ⋙ restriction_of_scalars.functor f :=
{ app := unit.map f,
  naturality' := λ X X' g, begin
    ext,
    simp only [unit.map, functor.id_map, Module.coe_comp, linear_map.coe_mk,
      function.comp_app, functor.comp_map],
    rw show (restriction_of_scalars.functor f).map ((extension_of_scalars.functor f).map g) =
      { to_fun := (extension_of_scalars.functor f).map g, map_add' := _, map_smul' := _ }, from rfl,
    simp only [linear_map.coe_mk],
    erw tensor_product.lift.tmul,
    simp only [linear_map.coe_mk],
  end }

def counit.map : (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f).obj Y ⟶ Y :=
let m1 : module R S := restriction_of_scalars.is_module f ⟨S⟩,
    m2 : module R Y := restriction_of_scalars.is_module f Y in
{ to_fun :=
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
          restriction_of_scalars.smul_def f ⟨S⟩ r s, smul_eq_mul, mul_smul], },
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
    { erw extension_of_scalars.smul_pure_tensor,
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
  end }.

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

/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic
import ring_theory.tensor_product

/-!
# Change Of Rings

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.

* `category_theory.Module.extend_scalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extend_scalars : Module R ⥤ Module S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

## List of notations
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f] m` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`.
-/


namespace category_theory.Module

universes v u₁ u₂

namespace restrict_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : Module R :=
{ carrier := M,
  is_module := module.comp_hom M f }

/--
Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
def map' {M M' : Module.{v} S} (g : M ⟶ M') :
  obj' f M ⟶ obj' f M' :=
{ map_smul' := λ r, g.map_smul (f r), ..g }

end restrict_scalars

/--
The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
* an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
* an `S`-linear map is also `R`-linear
-/
def restrict_scalars {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  Module.{v} S ⥤ Module.{v} R :=
{ obj := restrict_scalars.obj' f,
  map := λ _ _, restrict_scalars.map' f,
  map_id' := λ _, linear_map.ext $ λ m, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ m, rfl }

@[simp] lemma restrict_scalars.map_apply {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
  {M M' : Module.{v} S} (g : M ⟶ M') (x) : (restrict_scalars f).map g x = g x := rfl

@[simp] lemma restrict_scalars.smul_def {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
  {M : Module.{v} S} (r : R) (m : (restrict_scalars f).obj M) : r • m = (f r • m : M) := rfl

@[simp] lemma restrict_scalars.smul_def' {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
  {M : Module.{v} S} (r : R) (m : M) : (r • m : (restrict_scalars f).obj M) = (f r • m : M) := rfl

@[priority 100]
instance smul_comm_class_mk {R : Type u₁} {S : Type u₂} [ring R] [comm_ring S] (f : R →+* S)
  (M : Type v) [add_comm_group M] [module S M] :
  @smul_comm_class R S M ((restrict_scalars.obj' f (Module.mk M)).is_module.to_has_smul) _ :=
{ smul_comm := λ r s m, (by simp [←mul_smul, mul_comm] : f r • s • m = s • f r • m) }

namespace extend_scalars

open tensor_product

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)

section unbundled

variables (M : Type v) [add_comm_monoid M] [module R M]
-- This notation is necessary because we need to reason about `s ⊗ₜ m` where `s : S` and `m : M`;
-- without this notation, one need to work with `s : (restrict_scalars f).obj ⟨S⟩`.
localized "notation s `⊗ₜ[` R `,` f `]` m := @tensor_product.tmul R _ _ _ _ _
  (module.comp_hom _ f) _ s m" in change_of_rings

end unbundled

open_locale change_of_rings

variables (M : Module.{v} R)

/--
Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def obj' : Module S :=
⟨tensor_product R ((restrict_scalars f).obj ⟨S⟩) M⟩

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : Module.{v} R} (l : M1 ⟶ M2) : (obj' f M1) ⟶ (obj' f M2) :=
@linear_map.base_change R S M1 M2 _ _ ((algebra_map S _).comp f).to_algebra _ _ _ _ l

lemma map'_id {M : Module.{v} R} : map' f (𝟙 M) = 𝟙 _ :=
linear_map.ext $ λ (x : obj' f M),
begin
  dsimp only [map', Module.id_apply],
  induction x using tensor_product.induction_on with _ _ m s ihx ihy,
  { simp only [map_zero], },
  { rw [linear_map.base_change_tmul, Module.id_apply], },
  { rw [map_add, ihx, ihy] },
end

lemma map'_comp {M₁ M₂ M₃ : Module.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
  map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ :=
linear_map.ext $ λ (x : obj' f M₁),
begin
  dsimp only [map'],
  induction x using tensor_product.induction_on with _ _ x y ihx ihy,
  { refl, },
  { refl, },
  { simp only [map_add, ihx, ihy], },
end

end extend_scalars

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def extend_scalars {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S) :
  Module.{v} R ⥤ Module.{max v u₂} S :=
{ obj := λ M, extend_scalars.obj' f M,
  map := λ M1 M2 l, extend_scalars.map' f l,
  map_id' := λ _, extend_scalars.map'_id f,
  map_comp' := λ _ _ _, extend_scalars.map'_comp f }

namespace extend_scalars

open_locale change_of_rings

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)

@[simp] protected lemma smul_tmul {M : Module.{v} R} (s s' : S) (m : M) :
  s • (s' ⊗ₜ[R, f] m : (extend_scalars f).obj M) = (s * s') ⊗ₜ[R, f] m := rfl

@[simp] lemma map_tmul {M M' : Module.{v} R} (g : M ⟶ M') (s : S) (m : M) :
  (extend_scalars f).map g (s ⊗ₜ[R, f] m) = s ⊗ₜ[R, f] g m := rfl

end extend_scalars

namespace extension_restriction_adj

open_locale change_of_rings
open tensor_product

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y and a map `(extension_of_scalars.functor f).obj X ⟶ Y`,
there is a map `X ⟶ (restriction_of_scalars.functor f).obj Y`
-/
@[simps] def hom_equiv.to_restrict_scalars {X Y} (g : (extend_scalars f).obj X ⟶ Y) :
  X ⟶ (restrict_scalars f).obj Y :=
{ to_fun := λ x, g $ (1 : S) ⊗ₜ[R, f] x,
  map_add' := λ _ _, by rw [tmul_add, map_add],
  map_smul' := λ r x,
  begin
    letI : module R S := module.comp_hom S f,
    letI : module R Y := module.comp_hom Y f,
    rw [ring_hom.id_apply, restrict_scalars.smul_def, ←linear_map.map_smul, tmul_smul],
    congr,
  end }

/--
Given `R`-module X and `S`-module Y and a map `X ⟶ (restriction_of_scalars.functor f).obj Y`,
there is a map `(extension_of_scalars.functor f).obj X ⟶ Y`
-/
@[simps] def hom_equiv.from_extend_scalars {X Y} (g : X ⟶ (restrict_scalars f).obj Y) :
  (extend_scalars f).obj X ⟶ Y :=
let m1 : module R S := module.comp_hom S f, m2 : module R Y := module.comp_hom Y f in
begin
  resetI,
  refine ⟨λ z, tensor_product.lift ⟨λ s, ⟨_, _, _⟩, _, _⟩ z, _, _⟩,
  { exact λ x, s • g x },
  { intros, rw [map_add, smul_add], },
  { intros, rw [ring_hom.id_apply, smul_comm, ←linear_map.map_smul], },
  { intros, ext, simp only [linear_map.coe_mk, linear_map.add_apply], rw ←add_smul, },
  { intros, ext,
    simp only [linear_map.coe_mk, ring_hom.id_apply, linear_map.smul_apply,
      restrict_scalars.smul_def, smul_eq_mul],
    convert mul_smul _ _ _, },
  { intros, rw [map_add], },
  { intros r z,
    rw [ring_hom.id_apply],
    induction z using tensor_product.induction_on with x y x y ih1 ih2,
    { simp only [smul_zero, map_zero], },
    { simp only [linear_map.coe_mk, extend_scalars.smul_tmul, lift.tmul, ←mul_smul], },
    { simp only [smul_add, map_add],
      dsimp only at ih1 ih2,
      rw [ih1, ih2], }, },
end

/--
Given `R`-module X and `S`-module Y, the linear maps `(extension_of_scalars.functor f).obj X ⟶ Y`
bijectively corresponding to `X ⟶ (restriction_of_scalars.functor f).obj Y`
-/
@[simps] def hom_equiv' {X Y} :
  ((extend_scalars f).obj X ⟶ Y) ≃ (X ⟶ (restrict_scalars f).obj Y) :=
{ to_fun := hom_equiv.to_restrict_scalars f,
  inv_fun := hom_equiv.from_extend_scalars f,
  left_inv := λ g, begin
    ext z,
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul,
      simp only [linear_map.coe_mk],
      change S at x,
      erw [←linear_map.map_smul, extend_scalars.smul_tmul, mul_one x], },
    { rw [map_add, map_add, ih1, ih2], }
  end,
  right_inv := λ g, by { ext, simp } }

/--
For any `R`-module X, there is a natural `R`-linear map from `X` to `X ⨂ S` by sending `x ↦ x ⊗ 1`
-/
@[simps] def unit.map {X} : X ⟶ (extend_scalars f ⋙ restrict_scalars f).obj X :=
let m1 : module R S := module.comp_hom S f in
{ to_fun := λ x, (1 : S) ⊗ₜ[R, f] x,
  map_add' := λ x x', by { rw tensor_product.tmul_add, },
  map_smul' := λ r x,
  begin
    resetI,
    erw [ring_hom.id_apply, extend_scalars.smul_tmul, mul_one (f r), tmul_smul,
      extend_scalars.smul_tmul, mul_one (f r)],
  end }

/--
The natural transformation from ideantity functor on `R`-module to the composition of extension and
restriction of scalars.
-/
def unit : 𝟭 (Module R) ⟶ extend_scalars f ⋙ restrict_scalars f :=
{ app := λ _, unit.map f,
  naturality' := λ X X' g, by { ext (x : X), simp } }

/--
For any `S`-module Y, there is a natural `R`-linear map from `Y ⨂ S` to `Y` by
`y ⊗ s ↦ s • y`-/
@[simps] def counit.map {Y} :
  (restrict_scalars f ⋙ extend_scalars f).obj Y ⟶ Y :=
let m1 : module R S := module.comp_hom S f,
    m2 : module R Y := module.comp_hom Y f in
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
      { haveI t : has_smul S ((restriction_of_scalars.functor f).obj Y),
        { haveI : module S ((restriction_of_scalars.functor f).obj Y) :=
          (infer_instance : module S Y),
          apply_instance, },
        exact @has_smul.smul _ _ t s y, },
      { intros s s', rw add_smul, },
      { intros r s,
        rw [ring_hom.id_apply, restriction_of_scalars.smul_def f ⟨S⟩,
          restriction_of_scalars.smul_def f, smul_eq_mul, mul_smul], },
      { intros y1 y2,
        ext,
        simp only [linear_map.coe_mk, smul_add, linear_map.add_apply], },
      { intros r y,
        ext s,
        simp only [ring_hom.id_apply, restriction_of_scalars.smul_def,
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
  end }

/--
The natural transformation from the composition of restriction and extension of scalars to the
identity functor on `S`-module.
-/
@[simps] def counit :
  (restriction_of_scalars.functor f ⋙ extension_of_scalars.functor f) ⟶ (𝟭 (Module S)) :=
{ app := λ _, counit.map f,
  naturality' := λ Y Y' g, begin
    ext z,
    simp only [functor.comp_map, Module.coe_comp, function.comp_app, functor.id_map],
    induction z using tensor_product.induction_on with y s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { unfold counit.map,
      erw [tensor_product.lift.tmul, tensor_product.lift.tmul],
      simp only [linear_map.coe_mk, linear_map.map_smulₛₗ, ring_hom.id_apply],
      refl },
    { rw [map_add, map_add, ih1, ih2, map_add, map_add], }
  end }

/--
extension of scalars ⊣ restriction of scalars
-/
def adjunction : adjunction (extension_of_scalars.functor f) (restriction_of_scalars.functor f) :=
{ hom_equiv := λ _ _, hom_equiv' f,
  unit := unit f,
  counit := counit f,
  hom_equiv_unit' := λ X Y g, by { ext, simpa },
  hom_equiv_counit' := λ X Y g,
  begin
    ext z,
    simp only [hom_equiv'_symm_apply, hom_equiv.to_extension_apply, counit_app, Module.coe_comp,
      function.comp_app, counit.map_apply],
    induction z using tensor_product.induction_on with x s z1 z2 ih1 ih2,
    { simp only [map_zero], },
    { erw tensor_product.lift.tmul, },
    { simp only [map_add, ih1, ih2], }
  end }

end extension_restriction_adj

end change_of_rings

end category_theory.Module

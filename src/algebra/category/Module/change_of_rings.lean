/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic
import linear_algebra.tensor_product

/-!
# Change Of Rings

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.

* `category_theory.Module.extend_scalars.funtor`: given **commutative** ring and a ring homomorphism
  `f : R ⟶ S`, then `extend_scalars.functor : Module R ⥤ Module S` is defined by `M ↦ S ⨂ M` where
  the module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

-/


namespace category_theory.Module

universes u₁ u₂ v

namespace restrict_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : Module R :=
{ carrier := M,
  is_add_comm_group := infer_instance,
  is_module := module.comp_hom M f }

/-- The `R`-scalar multiplication on `S`-module M defined by `r • m := f r • m` -/
protected def has_smul : has_smul R M :=
(module.comp_hom M f).to_has_smul

localized "notation r ` r•[` f `] ` :=
  @@has_smul.smul (restrict_scalars.has_smul f _) r"
  in change_of_rings

@[simp] lemma smul_def (r : R) (m : M) : r r•[f] m = f r • m := rfl

/--
Given an `S`-linear map `g : M → M'` between `S`-modules, `g` is also `R`-linear between `M` and
`M'` by means of restriction of scalars.
-/
@[simps] def map' {M M' : Module.{v} S} (g : M ⟶ M') :
  obj' f M ⟶ obj' f M' :=
{ map_smul' := λ r (x : M), by simp,
  ..g }

end restrict_scalars

@[simps] def restrict_scalars {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  Module.{v} S ⥤ Module.{v} R :=
{ obj := restrict_scalars.obj' f,
  map := λ _ _, restrict_scalars.map' f,
  map_id' := λ _, linear_map.ext $ λ m, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ m, rfl }

namespace extend_scalars

open_locale tensor_product
open tensor_product

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S) (M : Module R)
include f

include M
localized "notation S `⊗[` R `,` f `]` M := @tensor_product R _ S M _ _
  (module.comp_hom S f) _" in change_of_rings
localized "notation s `⊗ₜ[` R `,` f `]` m := @tensor_product.tmul R _ _ _ _ _
  (module.comp_hom _ f) _ s m" in change_of_rings

/--
Since `S` has an `R`-module structure, `S ⊗[R] M` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (s' ⊗ m) := (s * s') ⊗ m`
-/
def is_module : module S (S ⊗[R, f] M) :=
@tensor_product.left_module R _ S _ S M _ _ (module.comp_hom S f) _ _
begin
  fconstructor,
  intros r s₁ s₂,
  simp only [restrict_scalars.smul_def f ⟨S⟩, smul_eq_mul],
  ring,
end

notation s ` e•[` f `]` := @@has_smul.smul (is_module f _).to_has_smul s

/--
S ⨂ M is also an `R`-module
-/
def is_module' : module R (S ⊗[R, f] M) := infer_instance

lemma smul_tensor (s s' : S) (m : M) : s e•[f] (s' ⊗ₜ[R, f] m) = (s * s') ⊗ₜ[R, f] m :=
by rw [smul_tmul', smul_eq_mul]

lemma smul_tensor' (r : R) (s : S) (m : M) : r • (s ⊗ₜ[R, f] m) = s ⊗ₜ[R, f] (r • m) :=
by rw [(@smul_tmul R _ R _ S M _ _ (module.comp_hom S f) _
    (module.comp_hom S f).to_distrib_mul_action _ _ r s m).symm, smul_tmul']

/--
Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def obj' : Module S :=
{ carrier := S ⊗[R, f] M,
  is_module := is_module f M }

omit M
/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
@[simps] def map' {M1 M2 : Module R} (l : M1 ⟶ M2) : (obj' f M1) ⟶ (obj' f M2) :=
{ to_fun := @tensor_product.lift R _ S M1 _ _ _ _ (module.comp_hom S f) _ (is_module' f M2) $
  { to_fun := λ s,
    { to_fun := λ m, s ⊗ₜ[R, f] l m,
      map_add' := λ m m', by rw [map_add, tmul_add],
      map_smul' := λ r m, by rw [ring_hom.id_apply, smul_tensor', linear_map.map_smul], },
    map_add' := λ m₁ m₂, fun_like.ext _ _ $
      λ s, by simp only [linear_map.coe_mk, linear_map.add_apply, add_tmul],
    map_smul' := λ r s, fun_like.ext _ _ $
      λ m, by { simpa [linear_map.coe_mk, linear_map.smul_apply, smul_tmul'], }, },
  map_add' := λ x y, by rw [map_add],
  map_smul' := λ s x,
  begin
    apply @tensor_product.induction_on R _ S M1 _ _ (module.comp_hom S f) _ _ x,
    { rw [smul_zero, map_zero, smul_zero], },
    { intros,
      simp only [smul_tensor, ring_hom.id_apply, tensor_product.lift.tmul, linear_map.coe_mk], },
    { intros _ _ ih1 ih2,
      simp only [smul_add, map_add, ih1, ih2, ring_hom.id_apply] },
  end }

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
@[simps] def functor : Module R ⥤ Module S :=
{ obj := λ M, obj' f M,
  map := λ M1 M2 l, map' f l,
  map_id' := λ M, begin
    ext x,
    simp_rw [map', Module.id_apply, linear_map.coe_mk],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { rw map_zero },
    { simp only [linear_map.coe_mk, tensor_product.lift.tmul], },
    { rw [map_add, ihx, ihy], }
  end,
  map_comp' := λ M1 M2 M3 g h, begin
    ext x,
    simp_rw [map'_apply, category_theory.comp_apply, map'_apply],
    induction x using tensor_product.induction_on with _ _ m s ihx ihy,
    { simp only [map_zero], },
    { simp only [tensor_product.lift.tmul, linear_map.coe_mk], },
    { simp only [map_add, ihx, ihy], }
  end }

end extend_scalars

end category_theory.Module

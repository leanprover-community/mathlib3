/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic
import algebra.category.Algebra.basic
import ring_theory.tensor_product

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

## List of notations
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `S`-module, `r : R` and `m : M` then notation `r r•[f] m` means `R`-scalar action on
  `M` defined by `f r • m`.
-/


namespace category_theory.Module

universes v u₁ u₂

namespace restrict_scalars

section unbundled

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
  (M : Type v) [add_comm_monoid M] [module S M]

/-- The `R`-scalar multiplication on `S`-module M defined by `r • m := f r • m` -/
protected def has_smul : has_smul R M :=
(module.comp_hom M f).to_has_smul

localized "notation r ` r•[` f `] ` :=
  @@has_smul.smul (restrict_scalars.has_smul f _) r"
  in change_of_rings

end unbundled

open_locale change_of_rings

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
variable (M : Module.{v} S)

/-- Any `S`-module M is also an `R`-module via a ring homomorphism `f : R ⟶ S` by defining
    `r • m := f r • m` (`module.comp_hom`). This is called restriction of scalars. -/
def obj' : Module R :=
{ carrier := M,
  is_add_comm_group := infer_instance,
  is_module := module.comp_hom M f }


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

/--
 The restriction of scalars operation is functorial. For any `f : R →+* S` a ring homomorphism,
 * an `S`-module `M` can be considered as `R`-module by `r • m = f r • m`
 * an `S`-linear map is also `R`-linear
 -/
@[simps] def restrict_scalars {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  Module.{v} S ⥤ Module.{v} R :=
{ obj := restrict_scalars.obj' f,
  map := λ _ _, restrict_scalars.map' f,
  map_id' := λ _, linear_map.ext $ λ m, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ m, rfl }

end category_theory.Module

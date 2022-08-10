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

* `category_theory.Module.extend_scalars`: given **commutative** rings `R, S` and ring homomorphism
  `f : R ⟶ S`, then `extend_scalars : Module R ⥤ Module S` is defined by `M ↦ S ⨂ M` where the
  module structure is defined by `s • (s' ⊗ m) := (s * s') ⊗ m` and `R`-linear map `l : M ⟶ M'`
  is sent to `S`-linear map `s ⊗ m ↦ s ⊗ l m : S ⨂ M ⟶ S ⨂ M'`.

## List of notations
Let `R, S` be rings and `f : R →+* S`
* if `M` is an `R`-module, then notation `S ⨂[R, f] M` means the tensor product `S ⨂ M` where `S`
  is considered as an `R`-module via restriction of scalars.
* if `M` is an `R`-module, `s : S` and `m : M`, then `s ⊗ₜ[R, f]` is the pure tensor
  `s ⊗ m : S ⊗[R, f] M`
* if `M` is an `R`-module, `s : S` and  `x : S ⊗[R, f] M` then notation `s e•[f] x` denotes the
  `S`-scalar multiplication where if `x` is pure tensor `s' ⊗ m` then `s e•[f] (s' ⊗ m)` is defined
  as `(s * s') ⊗ m`
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

/--
If `R, S` are commutative rings and `f : R →+* S`, then any `S`-algebra is also an `R`-algebra
-/
def is_algebra {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)
  (A : Type v) [comm_semiring A] [algebra S A] : algebra R A :=
{ smul := (module.comp_hom A f).to_has_smul.smul,
  to_fun := algebra_map _ _ ∘ f,
  map_one' := by simp only [function.comp_app, map_one],
  map_mul' := λ _ _, by simp only [function.comp_app, map_mul],
  map_zero' := by simp only [function.comp_app, map_zero],
  map_add' := λ _ _, by simp only [function.comp_app, map_add],
  commutes' := λ _ _, by ring,
  smul_def' := λ r a, algebra.smul_def _ _ }

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

namespace restrict_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

@[simp] lemma map_apply  {M M' : Module.{v} S} (g : M ⟶ M') (x) :
  (restrict_scalars f).map g x = g x := rfl

@[simp] lemma smul_def {M : Module.{v} S} (r : R) (m : (restrict_scalars f).obj M) :
  r • m = (f r • m : M) := rfl

@[simp] lemma smul_def' {M : Module.{v} S} (r : R) (m : M) :
  (r • m : (restrict_scalars f).obj M) = (f r • m : M) := rfl


end restrict_scalars

namespace extend_scalars

open_locale tensor_product
open tensor_product

variables {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S)

section unbundled

variables (M : Type v) [add_comm_monoid M] [module R M]

localized "notation S `⨂[` R `,` f `]` M := @tensor_product R _ S M _ _
  (module.comp_hom S f) _" in change_of_rings
localized "notation s `⊗ₜ[` R `,` f `]` m := @tensor_product.tmul R _ _ _ _ _
  (module.comp_hom _ f) _ s m" in change_of_rings

/--
Since `S` has an `R`-module structure, `S ⊗[R] M` can be given an `S`-module structure.
The scalar multiplication is defined by `s • (s' ⊗ m) := (s * s') ⊗ m`
-/
instance is_module : module S (S ⨂[R, f] M) :=
@tensor_product.left_module R _ S _ S M _ _ (module.comp_hom S f) _ _
begin
  fconstructor,
  intros r s₁ s₂,
  simp only [smul_eq_mul, restrict_scalars.smul_def' f r (_ : (⟨S⟩ : Module S))],
  ring,
end

localized "notation s ` e•[` f `]` :=
  @@has_smul.smul (category_theory.Module.extend_scalars.is_module f _).to_has_smul s" in
  change_of_rings

end unbundled

open_locale change_of_rings

variables (M : Module.{v} R)

lemma smul_tmul (s s' : S) (m : M) : s e•[f] (s' ⊗ₜ[R, f] m) = (s * s') ⊗ₜ[R, f] m :=
by rw [smul_tmul', smul_eq_mul]

lemma smul_tmul' (r : R) (s : S) (m : M) : r • (s ⊗ₜ[R, f] m) = s ⊗ₜ[R, f] (r • m) :=
by rw [(@tensor_product.smul_tmul R _ R _ S M _ _ (module.comp_hom S f) _
    (module.comp_hom S f).to_distrib_mul_action _ _ r s m).symm, smul_tmul']

/--
Extension of scalars turn an `R`-module into `S`-module by M ↦ S ⨂ M
-/
def obj' : Module S := ⟨S ⨂[R, f] M⟩

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
def map' {M1 M2 : Module.{v} R} (l : M1 ⟶ M2) : (obj' f M1) ⟶ (obj' f M2) :=
@linear_map.base_change R S M1 M2 _ _ (restrict_scalars.is_algebra f S) _ _ _ _ l

lemma map'_id {M : Module.{v} R} : map' f (𝟙 M) = 𝟙 _ :=
linear_map.ext $ λ (x : S ⨂[R, f] M),
begin
  dsimp [map'],
  induction x using tensor_product.induction_on with _ _ m s ihx ihy,
  { simp only [map_zero], },
  { rw [linear_map.base_change_tmul, Module.id_apply], },
  { rw [map_add, ihx, ihy] },
end

lemma map'_comp {M₁ M₂ M₃ : Module.{v} R} (l₁₂ : M₁ ⟶ M₂) (l₂₃ : M₂ ⟶ M₃) :
  map' f (l₁₂ ≫ l₂₃) = map' f l₁₂ ≫ map' f l₂₃ :=
linear_map.ext $ λ (x : S ⨂[R, f] M₁),
begin
  dsimp [map'],
  induction x using tensor_product.induction_on with _ _ m s ihx ihy,
  { simp only [map_zero], },
  { rw [linear_map.base_change_tmul, category_theory.comp_apply, linear_map.base_change_tmul,
      linear_map.base_change_tmul], },
  { simp only [map_add, ihx, ihy], },
end

end extend_scalars

/--
Extension of scalars is a functor where an `R`-module `M` is sent to `S ⊗ M` and
`l : M1 ⟶ M2` is sent to `s ⊗ m ↦ s ⊗ l m`
-/
@[simps] def extend_scalars {R : Type u₁} {S : Type u₂} [comm_ring R] [comm_ring S] (f : R →+* S) :
  Module R ⥤ Module S :=
{ obj := λ M, extend_scalars.obj' f M,
  map := λ M1 M2 l, extend_scalars.map' f l,
  map_id' := λ _, extend_scalars.map'_id f,
  map_comp' := λ _ _ _, extend_scalars.map'_comp f }

end category_theory.Module

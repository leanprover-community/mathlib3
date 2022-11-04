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

lemma restrict_scalars.smul_def' {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)
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
-- The "by apply" part makes this require 75% fewer heartbeats to process (#16371).
by apply (@linear_map.base_change R S M1 M2 _ _ ((algebra_map S _).comp f).to_algebra _ _ _ _ l)

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

end category_theory.Module

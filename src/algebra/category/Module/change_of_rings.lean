/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
import algebra.category.Module.basic

/-!
# Change Of Rings

## Main definitions

* `category_theory.Module.restrict_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`,
  then `restrict_scalars : Module S ⥤ Module R` is defined by `M ↦ M` where `M : S-module` is seen
  as `R-module` by `r • m := f r • m` and `S`-linear map `l : M ⟶ M'` is `R`-linear as well.
* `category_theory.Module.coextend_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`m
  then `coextend_scalars : Module R ⥤ Module S` is defined by `M ↦ (S →ₗ[R] M)` where `S` is seen as
  `R-module` by restriction of scalars and `l ↦ l ∘ _`.
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


namespace coextend_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

section unbundled

variables (M : Type v) [add_comm_monoid M] [module R M]

local notation `Hom` M := (restrict_scalars f).obj ⟨S⟩ →ₗ[R] M

/--
 Given an `R`-module M, consider the Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
 means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
 -/
 instance has_smul : has_smul S $ Hom M :=
 { smul := λ s g,
   { to_fun := λ (s' : S), g (s' • s : S),
     map_add' := λ (x y : S), by simp [add_smul, map_add],
     map_smul' := λ r (t : S), by rw [ring_hom.id_apply, @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩,
       ←linear_map.map_smul, @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩, smul_assoc] } }

@[simp] lemma smul_apply (s : S) (g : Hom M) (s' : S) :
  @has_smul.smul _ _ (coextend_scalars.has_smul f _) s g s' = g (s' • s : S) := rfl

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)` such that `1 • g = g` and `(s * t) • g = s • t • g`
-/
instance mul_action : mul_action S $ Hom M :=
{ one_smul := λ g, linear_map.ext $ λ (s : S), by simp,
  mul_smul := λ (s t : S) g, linear_map.ext $ λ (x : S), by simp [mul_assoc],
  ..coextend_scalars.has_smul f _ }

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)` such that
* 1 • g = g
* (s * t) • g = s • t • g
* s • (g + h) = s • g + s • h
* s • 0 = 0
-/
instance distrib_mul_action : distrib_mul_action S $ Hom M :=
{ smul_add := λ s g h, linear_map.ext $ λ (t : S), by simp,
  smul_zero := λ s, linear_map.ext $ λ (t : S), by simp,
  ..coextend_scalars.mul_action f _ }

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
 -/
instance is_module : module S $ Hom M :=
{ add_smul := λ s1 s2 g, linear_map.ext $ λ (x : S), by simp [mul_add],
  zero_smul := λ g, linear_map.ext $ λ (x : S), by simp,
  ..coextend_scalars.distrib_mul_action f _ }

end unbundled

variable (M : Module.{v} R)

/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with scalar
multiplication defined by `s • l := x ↦ l (x • s)`-/
def obj' : Module S := ⟨(restrict_scalars f).obj ⟨S⟩ →ₗ[R] M⟩

instance : has_coe_to_fun (obj' f M) (λ g, S → M) :=
{ coe := λ g, g.to_fun }

/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h`-/
@[simps] def map' {M M' : Module R} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
{ to_fun := λ h, g.comp h,
  map_add' := λ _ _, linear_map.comp_add _ _ _,
  map_smul' := λ s h, linear_map.ext $ λ (t : S), by simpa only [smul_apply] }

end coextend_scalars

/--
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor from `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module via restriction of
scalar and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.
-/
def coextend_scalars {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  Module R ⥤ Module S :=
{ obj := coextend_scalars.obj' f,
  map := λ _ _, coextend_scalars.map' f,
  map_id' := λ M, linear_map.ext $ λ h, linear_map.ext $ λ x, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ h, linear_map.ext $ λ x, rfl }

end category_theory.Module

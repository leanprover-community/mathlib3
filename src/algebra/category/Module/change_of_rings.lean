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

* `category_theory.Module.coextend_scalars`: given rings `R, S` and a ring homomorphism `R ⟶ S`
  then `coextend_scalars : Module R ⥤ Module S` is defined by `M ↦ (S →ₗ[R] M)` where `S` is seen as
  `R-module` by restriction of scalars and `l ↦ l ∘ _`.

* `category_theory.Module.restrict_coextend_scalars_adj`: given rings `R, S` and a ring homomorphism
  `f : R ⟶ S` then `coextend_scalars f` is the right adjoint of `restrict_scalars f`.

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

namespace coextend_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

section unbundled

variables (M : Type v) [add_comm_monoid M] [module R M]

-- We use `S'` to denote `S` viewed as `R`-module, via the map `f`.
local notation `S'` := (restrict_scalars f).obj ⟨S⟩

/--
 Given an `R`-module M, consider the Hom(S, M) -- the `R`-linear maps between S (as an `R`-module by
 means of restriction of scalars) and M. `S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`
 -/
instance has_smul : has_smul S $ S' →ₗ[R] M :=
{ smul := λ s g,
  { to_fun := λ (s' : S), g (s' * s : S),
    map_add' := λ (x y : S), by simp [add_mul, map_add],
    map_smul' := λ r (t : S), by rw [ring_hom.id_apply, @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩,
      ←linear_map.map_smul, @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, smul_eq_mul,
      mul_assoc] } }

@[simp] lemma smul_apply' (s : S) (g :  S' →ₗ[R] M) (s' : S) :
  @has_smul.smul _ _ (coextend_scalars.has_smul f _) s g s' = g (s' * s : S) := rfl

instance mul_action : mul_action S $ S' →ₗ[R] M :=
{ one_smul := λ g, linear_map.ext $ λ (s : S), by simp,
  mul_smul := λ (s t : S) g, linear_map.ext $ λ (x : S), by simp [mul_assoc],
  ..coextend_scalars.has_smul f _ }

instance distrib_mul_action : distrib_mul_action S $ S' →ₗ[R] M :=
{ smul_add := λ s g h, linear_map.ext $ λ (t : S), by simp,
  smul_zero := λ s, linear_map.ext $ λ (t : S), by simp,
  ..coextend_scalars.mul_action f _ }

/--
`S` acts on Hom(S, M) by `s • g = x ↦ g (x • s)`, this action defines an `S`-module structure on
Hom(S, M).
 -/
instance is_module : module S $ S' →ₗ[R] M :=
{ add_smul := λ s1 s2 g, linear_map.ext $ λ (x : S), by simp [mul_add],
  zero_smul := λ g, linear_map.ext $ λ (x : S), by simp,
  ..coextend_scalars.distrib_mul_action f _ }

end unbundled

variable (M : Module.{v} R)

/-- If `M` is an `R`-module, then the set of `R`-linear maps `S →ₗ[R] M` is an `S`-module with
scalar multiplication defined by `s • l := x ↦ l (x • s)`-/
def obj' : Module S := ⟨(restrict_scalars f).obj ⟨S⟩ →ₗ[R] M⟩

instance : has_coe_to_fun (obj' f M) (λ g, S → M) :=
{ coe := λ g, g.to_fun }

/-- If `M, M'` are `R`-modules, then any `R`-linear map `g : M ⟶ M'` induces an `S`-linear map
`(S →ₗ[R] M) ⟶ (S →ₗ[R] M')` defined by `h ↦ g ∘ h`-/
@[simps] def map' {M M' : Module R} (g : M ⟶ M') : obj' f M ⟶ obj' f M' :=
{ to_fun := λ h, g.comp h,
  map_add' := λ _ _, linear_map.comp_add _ _ _,
  map_smul' := λ s h, linear_map.ext $ λ (t : S), by simpa only [smul_apply'] }

end coextend_scalars

/--
For any rings `R, S` and a ring homomorphism `f : R →+* S`, there is a functor from `R`-module to
`S`-module defined by `M ↦ (S →ₗ[R] M)` where `S` is considered as an `R`-module via restriction of
scalars and `g : M ⟶ M'` is sent to `h ↦ g ∘ h`.
-/
def coextend_scalars {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  Module R ⥤ Module S :=
{ obj := coextend_scalars.obj' f,
  map := λ _ _, coextend_scalars.map' f,
  map_id' := λ M, linear_map.ext $ λ h, linear_map.ext $ λ x, rfl,
  map_comp' := λ _ _ _ g h, linear_map.ext $ λ h, linear_map.ext $ λ x, rfl }

namespace coextend_scalars

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

instance (M : Module R) : has_coe_to_fun ((coextend_scalars f).obj M) (λ g, S → M) :=
(infer_instance : has_coe_to_fun (coextend_scalars.obj' f M) _)

lemma smul_apply (M : Module R) (g : (coextend_scalars f).obj M) (s s' : S) :
  (s • g) s' = g (s' * s) := rfl

lemma map_apply {M M' : Module R} (g : M ⟶ M') (x) (s : S) :
  (coextend_scalars f).map g x s = g (x s) := rfl

end coextend_scalars

namespace restriction_coextension_adj

variables {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S)

/--
Given `R`-module X and `S`-module Y, any `g : (restrict_of_scalars f).obj Y ⟶ X`
corresponds to `Y ⟶ (coextend_scalars f).obj X` by sending `y ↦ (s ↦ g (s • y))`
-/
@[simps] def hom_equiv.from_restriction {X Y} (g : (restrict_scalars f).obj Y ⟶ X) :
  Y ⟶ (coextend_scalars f).obj X :=
{ to_fun := λ (y : Y),
  { to_fun := λ (s : S), g $ (s • y : Y),
    map_add' := λ (s1 s2 : S), by simp [add_smul],
    map_smul' := λ r (s : S), by rw [ring_hom.id_apply, ←g.map_smul,
      @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_smul,
      @restrict_scalars.smul_def _ _ _ _ f Y] },
  map_add' := λ (y1 y2 : Y), linear_map.ext $ λ (s : S),
  by rw [linear_map.add_apply, linear_map.coe_mk, linear_map.coe_mk, linear_map.coe_mk,
      smul_add, map_add],
  map_smul' := λ s y, linear_map.ext $ λ (t : S), by simp [mul_smul] }

/--
Given `R`-module X and `S`-module Y, any `g : Y ⟶ (coextend_scalars f).obj X`
corresponds to `(restrict_scalars f).obj Y ⟶ X` by `y ↦ g y 1`
-/
@[simps] def hom_equiv.to_restriction {X Y} (g : Y ⟶ (coextend_scalars f).obj X) :
  (restrict_scalars f).obj Y ⟶ X :=
{ to_fun := λ (y : Y), (g y).to_fun (1 : S),
  map_add' := λ x y, by simp only [g.map_add, linear_map.to_fun_eq_coe, linear_map.add_apply],
  map_smul' := λ r (y : Y), by rw [linear_map.to_fun_eq_coe, linear_map.to_fun_eq_coe,
    ring_hom.id_apply, ←linear_map.map_smul, restrict_scalars.smul_def f r y,
    @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_one, linear_map.map_smul,
    coextend_scalars.smul_apply, one_mul], }

/--
The natural transformation from identity functor to the composition of restriction and coextension
of scalars.
-/
@[simps] protected def unit' : 𝟭 (Module S) ⟶ restrict_scalars f ⋙ coextend_scalars f :=
{ app := λ Y,
  { to_fun := λ (y : Y),
    { to_fun := λ (s : S), (s • y : Y),
      map_add' := λ s s', add_smul _ _ _,
      map_smul' := λ r (s : S), by rw [ring_hom.id_apply, @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩,
        smul_eq_mul, mul_smul, restrict_scalars.smul_def f] },
    map_add' := λ y1 y2, linear_map.ext $ λ (s : S), by rw [linear_map.add_apply, linear_map.coe_mk,
      linear_map.coe_mk, linear_map.coe_mk, smul_add],
    map_smul' := λ s (y : Y), linear_map.ext $ λ (t : S), by simp [mul_smul] },
  naturality' := λ Y Y' g, linear_map.ext $ λ (y : Y), linear_map.ext $ λ (s : S),
    by simp [coextend_scalars.map_apply] }

/--
The natural transformation from the composition of coextension and restriction of scalars to
identity functor.
-/
@[simps] protected def counit' : coextend_scalars f ⋙ restrict_scalars f ⟶ 𝟭 (Module R) :=
{ app := λ X,
  { to_fun := λ g, g.to_fun (1 : S),
    map_add' := λ x1 x2, by simp [linear_map.to_fun_eq_coe],
    map_smul' := λ r (g : (restrict_scalars f).obj ((coextend_scalars f).obj X)),
    begin
      simp only [linear_map.to_fun_eq_coe, ring_hom.id_apply],
      rw [restrict_scalars.smul_def f, coextend_scalars.smul_apply, one_mul, ←linear_map.map_smul,
        @restrict_scalars.smul_def _ _ _ _ f ⟨S⟩, smul_eq_mul, mul_one],
    end },
  naturality' := λ X X' g, linear_map.ext $ λ h, by simp [coextend_scalars.map_apply] }

end restriction_coextension_adj

/-- Restriction of scalars is left adjoint to coextension of scalars. -/
@[simps] def restrict_coextend_scalars_adj {R : Type u₁} {S : Type u₂} [ring R] [ring S]
  (f : R →+* S) : restrict_scalars f ⊣ coextend_scalars f :=
{ hom_equiv := λ X Y,
  { to_fun := restriction_coextension_adj.hom_equiv.from_restriction f,
    inv_fun := restriction_coextension_adj.hom_equiv.to_restriction f,
    left_inv := λ g, linear_map.ext $ λ (x : X), by simp,
    right_inv := λ g, linear_map.ext $ λ x, linear_map.ext $ λ (s : S), by simp },
  unit := restriction_coextension_adj.unit' f,
  counit := restriction_coextension_adj.counit' f,
  hom_equiv_unit' := λ X Y g, linear_map.ext $ λ y, rfl,
  hom_equiv_counit' := λ Y X g, linear_map.ext $ λ (y : Y), by simp }

instance {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  category_theory.is_left_adjoint (restrict_scalars f) := ⟨_, restrict_coextend_scalars_adj f⟩

instance {R : Type u₁} {S : Type u₂} [ring R] [ring S] (f : R →+* S) :
  category_theory.is_right_adjoint (coextend_scalars f) := ⟨_, restrict_coextend_scalars_adj f⟩

end category_theory.Module

/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Jakob von Raumer
-/
import group_theory.congruence
import linear_algebra.bilinear_map
import linear_algebra.tensor_product.def

/-!
# The canonical left action on a tensor product of modules

This file describes left actions of various algebraic structures on the left of the
tensor product of modules, based on the fact that if `M` is an `R'`-`R` bimodule,
`R'` acts on `M ⊗[R] N` by `r • (m ⊗ n) := (r • m ⊗ n)`.

## Tags

group action, tensor product
-/
namespace tensor_product

open_locale tensor_product

section semiring

variables {R : Type*} [semiring R]
variables {R' : Type*} [monoid R']
variables {R'' : Type*} [semiring R'']
variables {M N : Type*}
variables [add_comm_monoid M] [add_comm_monoid N]
variables [module Rᵒᵖ M] [module R N]
variables [distrib_mul_action R' M]
variables [module R'' M]


def rsmul.aux {R' : Type*} [has_scalar R' M] (r : R') :
  free_add_monoid (M × N) →+ M ⊗[R] N :=
free_add_monoid.lift $ λ p : M × N, (r • p.1) ⊗ₜ p.2

theorem rsmul.aux_of {R' : Type*} [has_scalar R' M] (r : R') (m : M) (n : N) :
  rsmul.aux r (free_add_monoid.of (m, n)) = (r • m) ⊗ₜ[R] n :=
rfl

variables [smul_comm_class Rᵒᵖ R' M]
variables [smul_comm_class Rᵒᵖ R'' M]

/-- Given two modules over a semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
 * Extension of scalars
 * A tensor product of a group representation with a module not carrying an action
-/
instance left_has_scalar : has_scalar R' (M ⊗[R] N) :=
⟨λ r, (add_con_gen (tensor_product.eqv R M N)).lift (rsmul.aux r : _ →+ M ⊗[R] N) $
add_con.add_con_gen_le $ λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
    by rw [add_monoid_hom.map_zero, rsmul.aux_of, smul_zero, zero_tmul]
| _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, rsmul.aux_of, tmul_zero]
| _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, rsmul.aux_of, smul_add, add_tmul]
| _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, rsmul.aux_of, tmul_add]
| _, _, (eqv.of_smul s m n)        := (add_con.ker_rel _).2 $
    by rw [rsmul.aux_of, rsmul.aux_of, ←smul_comm, rsmul_tmul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end⟩

theorem smul_tmul' (r : R') (m : M) (n : N) :
  r • (m ⊗ₜ[R] n) = (r • m) ⊗ₜ n :=
rfl

protected theorem smul_zero (r : R') : (r • 0 : M ⊗[R] N) = 0 :=
add_monoid_hom.map_zero _

protected theorem smul_add  (r : R') (x y : M ⊗[R] N) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
tensor_product.induction_on x
  (by rw tensor_product.smul_zero)
  (λ m n, by rw [smul_tmul', zero_smul, zero_tmul])
  (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy, add_zero])

protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
tensor_product.induction_on x
  (by rw tensor_product.smul_zero)
  (λ m n, by rw [smul_tmul', one_smul])
  (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy])

protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
have ∀ (r : R'') (m : M) (n : N), r • (m ⊗ₜ[R] n) = (r • m) ⊗ₜ n := λ _ _ _, rfl,
tensor_product.induction_on x
  (by simp_rw [tensor_product.smul_zero, add_zero])
  (λ m n, by simp_rw [this, add_smul, add_tmul])
  (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy, add_add_add_comm] })

instance left_distrib_mul_action : distrib_mul_action R' (M ⊗[R] N) :=
{ smul := (•),
  smul_add := λ r x y, tensor_product.smul_add r x y,
  mul_smul := λ r s x, tensor_product.induction_on x
    (by simp_rw tensor_product.smul_zero)
    (λ m n, by simp_rw [smul_tmul', mul_smul])
    (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy] }),
  one_smul := tensor_product.one_smul,
  smul_zero := tensor_product.smul_zero }

@[simp] lemma tmul_smul [has_scalar R'ᵒᵖ M] [is_symmetric_smul R' M]
  [has_scalar R' N] [compatible_smul R R' M N] (r : R') (x : M) (y : N) :
  x ⊗ₜ (r • y) = r • (x ⊗ₜ[R] y) :=
(smul_tmul _ _ _).symm

instance left_module : module R'' (M ⊗[R] N) :=
{ smul := (•),
  add_smul := tensor_product.add_smul,
  zero_smul := tensor_product.zero_smul,
  ..tensor_product.left_distrib_mul_action }

section
-- Like `R'`, `R'₂` provides a `distrib_mul_action R'₂ (M ⊗[R] N)`
variables {R'₂ : Type*} [monoid R'₂] [distrib_mul_action R'₂ M]
variables [smul_comm_class Rᵒᵖ R'₂ M] [has_scalar R'₂ R']

/-- `is_scalar_tower R'₂ R' M` implies `is_scalar_tower R'₂ R' (M ⊗[R] N)` -/
instance is_scalar_tower_left [is_scalar_tower R'₂ R' M] :
  is_scalar_tower R'₂ R' (M ⊗[R] N) :=
⟨λ s r x, tensor_product.induction_on x
  (by simp)
  (λ m n, by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc])
  (λ x y ihx ihy, by rw [smul_add, smul_add, smul_add, ihx, ihy])⟩

end
end semiring

section comm_semiring

variables {R : Type*} [comm_semiring R]
variables {R' : Type*} [monoid R']
variables {R'' : Type*} [comm_semiring R''] --?
variables {M N : Type*}
variables [add_comm_monoid M] [add_comm_monoid N]
variables [module Rᵒᵖ M] [module R N]
variables [distrib_mul_action R' M]

/-- The instance `tensor_product.left_has_scalar` induces this special case of `R` acting
on the right of the tensor product `M ⊗[R] N`. -/
instance right_has_scalar_comm : has_scalar Rᵒᵖ (M ⊗[R] N) := infer_instance

instance : distrib_mul_action Rᵒᵖ (M ⊗[R] N) := tensor_product.left_distrib_mul_action

instance : module Rᵒᵖ (M ⊗[R] N) := tensor_product.left_module

/-- A short-cut instance of `is_scalar_tower_left` for the common case, where the requirements
for the `compatible_smul` instances are sufficient. -/
instance is_scalar_tower [smul_comm_class Rᵒᵖ R' M] [has_scalar R' R] [is_scalar_tower R' Rᵒᵖ M] :
  is_scalar_tower R' Rᵒᵖ (M ⊗[R] N) :=
tensor_product.is_scalar_tower_left

variables (R M N)
/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk [module Rᵒᵖ N] [is_symmetric_smul R N] : M →ₗ[Rᵒᵖ] N →ₗ[Rᵒᵖ] M ⊗[R] N :=
linear_map.mk₂ Rᵒᵖ (⊗ₜ) add_tmul (λ c m n, rfl) tmul_add
  (λ c m n, by rw [←c.op_unop , is_symmetric_smul.op_smul_eq_smul, ←rsmul_tmul, smul_tmul'])
variables {R M N}

@[simp] lemma mk_apply [module Rᵒᵖ N] [is_symmetric_smul R N] (m : M) (n : N) :
  mk R M N m n = m ⊗ₜ n :=
rfl

/-- The simple (aka pure) elements span the tensor product. -/
lemma span_tmul_eq_top :
  submodule.span Rᵒᵖ { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ :=
begin
  ext t, simp only [submodule.mem_top, iff_true],
  apply t.induction_on,
  { exact submodule.zero_mem _, },
  { intros m n, apply submodule.subset_span, use [m, n], },
  { intros t₁ t₂ ht₁ ht₂, exact submodule.add_mem _ ht₁ ht₂, },
end

section UMP

variables {P Q : Type*}
variables [add_comm_monoid P] [module R P] [module Rᵒᵖ P] [is_symmetric_smul R P]
variables [add_comm_monoid Q] [module R Q] [module Rᵒᵖ Q] [is_symmetric_smul R Q]
variables [module Rᵒᵖ N] [is_symmetric_smul R N]
variables (f : M →ₗ[Rᵒᵖ] N →ₗ[Rᵒᵖ] P)

/-- Auxiliary function to constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift_aux : (M ⊗[R] N) →+ P :=
(add_con_gen (tensor_product.eqv R M N)).lift (free_add_monoid.lift $ λ p : M × N, f p.1 p.2) $
add_con.add_con_gen_le $ λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of, f.map_zero₂]
| _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, free_add_monoid.lift_eval_of, (f m).map_zero]
| _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, f.map_add₂]
| _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, free_add_monoid.lift_eval_of, (f m).map_add]
| _, _, (eqv.of_smul r m n)        := (add_con.ker_rel _).2 $
    by rw [free_add_monoid.lift_eval_of, free_add_monoid.lift_eval_of,
           f.map_smul₂, ←(f m).map_smul (opposite.op r), is_symmetric_smul.op_smul_eq_smul r n]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

lemma lift_aux_tmul (m n) : lift_aux f (m ⊗ₜ n) = f m n :=
zero_add _

variable {f}

@[simp] lemma lift_aux.smul (r : Rᵒᵖ) (x) : lift_aux f (r • x) = r • lift_aux f x :=
tensor_product.induction_on x (smul_zero _).symm
  (λ p q, by rw [lift_aux_tmul,smul_tmul', lift_aux_tmul, f.map_smul₂] )
  (λ p q ih1 ih2, by rw [smul_add, (lift_aux f).map_add, ih1, ih2, (lift_aux f).map_add, smul_add])

variable (f)
/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift : M ⊗ N →ₗ[Rᵒᵖ] P :=
{ map_smul' := lift_aux.smul,
  .. lift_aux f }
variable {f}

@[simp] lemma lift.tmul (x y) : lift f (x ⊗ₜ y) = f x y :=
zero_add _

@[simp] lemma lift.tmul' (x y) : (lift f).1 (x ⊗ₜ y) = f x y :=
lift.tmul _ _

theorem ext' {g h : (M ⊗[R] N) →ₗ[Rᵒᵖ] P}
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
linear_map.ext $ λ z, tensor_product.induction_on z (by simp_rw linear_map.map_zero) H $
λ x y ihx ihy, by rw [g.map_add, h.map_add, ihx, ihy]

theorem lift.unique {g : (M ⊗[R] N) →ₗ[Rᵒᵖ] P} (H : ∀ x y, g (x ⊗ₜ y) = f x y) :
  g = lift f :=
ext' $ λ m n, by rw [H, lift.tmul]

example : has_scalar Rᵒᵖ (M ⊗[R] N) := tensor_product.left_has_scalar

variables [module R (M ⊗[R] N)] [is_symmetric_smul R (M ⊗[R] N)]

theorem lift_mk : lift (mk R M N) = linear_map.id :=
eq.symm $ lift.unique $ λ x y, rfl

theorem lift_compr₂ (g : P →ₗ[Rᵒᵖ] Q) : lift (f.compr₂ g) = g.comp (lift f) :=
eq.symm $ lift.unique $ λ x y, by simp

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ[Rᵒᵖ] P) : lift ((mk R M N).compr₂ f) = f :=
by { rw [lift_compr₂ f, lift_mk, linear_map.comp_id], repeat { apply_instance } }

/--
This used to be an `@[ext]` lemma, but it fails very slowly when the `ext` tactic tries to apply
it in some cases, notably when one wants to show equality of two linear maps. The `@[ext]`
attribute is now added locally where it is needed. Using this as the `@[ext]` lemma instead of
`tensor_product.ext'` allows `ext` to apply lemmas specific to `M →ₗ _` and `N →ₗ _`.
See note [partially-applied ext lemmas]. -/
theorem ext {g h : M ⊗[R] N →ₗ[Rᵒᵖ] P}
  (H : (mk R M N).compr₂ g = (mk R M N).compr₂ h) : g = h :=
by rw [← lift_mk_compr₂ g, H, lift_mk_compr₂]

local attribute [ext] ext

example : M → N → (M → N → P) → P :=
λ m, flip $ λ f, f m

variables (R M N P)
/-- Linearly constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry : (M →ₗ[Rᵒᵖ] N →ₗ[Rᵒᵖ] P) →ₗ[Rᵒᵖ] M ⊗[R] N →ₗ[Rᵒᵖ] P :=
linear_map.flip $ lift $ (linear_map.lflip _ _ _ _).comp (linear_map.flip linear_map.id)
variables {R M N P}

end UMP

end comm_semiring

section ring

end ring

end tensor_product

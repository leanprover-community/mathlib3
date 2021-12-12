/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.basic
import linear_algebra.prod

/-!
# Trivial Square-Zero Extension

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.

## Main definitions

* `triv_sq_zero_ext.inl`, `triv_sq_zero_ext.inr`: the canonical inclusions into
  `triv_sq_zero_ext R M`.
* `triv_sq_zero_ext.fst`, `triv_sq_zero_ext.snd`: the canonical projections from
  `triv_sq_zero_ext R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.

-/

universes u v w

/--
"Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
def triv_sq_zero_ext (R : Type u) (M : Type v) :=
R × M

local notation `tsze` := triv_sq_zero_ext

namespace triv_sq_zero_ext

section basic
variables {R : Type u} {M : Type v}

/-- The canonical inclusion `R → triv_sq_zero_ext R M`. -/
def inl [has_zero M] (r : R) : tsze R M :=
(r, 0)

/-- The canonical inclusion `M → triv_sq_zero_ext R M`. -/
def inr [has_zero R] (m : M) : tsze R M :=
(0, m)

/-- The canonical projection `triv_sq_zero_ext R M → R`. -/
def fst (x : tsze R M) : R :=
x.1

/-- The canonical projection `triv_sq_zero_ext R M → M`. -/
def snd (x : tsze R M) : M :=
x.2

@[ext] lemma ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
prod.ext h1 h2

@[simp] lemma fst_inl [has_zero M] (r : R) : (inl r : tsze R M).fst = r := rfl
@[simp] lemma snd_inl [has_zero M] (r : R) : (inl r : tsze R M).snd = 0 := rfl
@[simp] lemma fst_inr [has_zero R] (m : M) : (inr m : tsze R M).fst = 0 := rfl
@[simp] lemma snd_inr [has_zero R] (m : M) : (inr m : tsze R M).snd = m := rfl

lemma inl_injective [has_zero M] : function.injective (inl : R → tsze R M) :=
function.left_inverse.injective fst_inl

lemma inr_injective [has_zero R] : function.injective (inr : M → tsze R M) :=
function.left_inverse.injective snd_inr

end basic

/-! ### Structures inherited from `prod`

Additive operators and scalar multiplication operate elementwise. -/

section additive

variables {T : Type*} {S : Type*} {R : Type u} {M : Type v}

instance [inhabited R] [inhabited M] : inhabited (tsze R M) :=
prod.inhabited

instance [has_zero R] [has_zero M] : has_zero (tsze R M) :=
prod.has_zero

instance [has_add R] [has_add M] : has_add (tsze R M) :=
prod.has_add

instance [has_neg R] [has_neg M] : has_neg (tsze R M) :=
prod.has_neg

instance [add_semigroup R] [add_semigroup M] : add_semigroup (tsze R M) :=
prod.add_semigroup

instance [add_zero_class R] [add_zero_class M] : add_zero_class (tsze R M) :=
prod.add_zero_class

instance [add_monoid R] [add_monoid M] : add_monoid (tsze R M) :=
prod.add_monoid

instance [add_group R] [add_group M] : add_group (tsze R M) :=
prod.add_group

instance [add_comm_semigroup R] [add_comm_semigroup M] : add_comm_semigroup (tsze R M) :=
prod.add_comm_semigroup

instance [add_comm_monoid R] [add_comm_monoid M] : add_comm_monoid (tsze R M) :=
prod.add_comm_monoid

instance [add_comm_group R] [add_comm_group M] : add_comm_group (tsze R M) :=
prod.add_comm_group

instance [has_scalar S R] [has_scalar S M] : has_scalar S (tsze R M) :=
prod.has_scalar

instance [has_scalar T R] [has_scalar T M] [has_scalar S R] [has_scalar S M] [has_scalar T S]
  [is_scalar_tower T S R] [is_scalar_tower T S M] : is_scalar_tower T S (tsze R M) :=
prod.is_scalar_tower

instance [has_scalar T R] [has_scalar T M] [has_scalar S R] [has_scalar S M]
  [smul_comm_class T S R] [smul_comm_class T S M] : smul_comm_class T S (tsze R M) :=
prod.smul_comm_class

instance [has_scalar S R] [has_scalar S M] [has_scalar Sᵐᵒᵖ R] [has_scalar Sᵐᵒᵖ M]
  [is_central_scalar S R] [is_central_scalar S M] : is_central_scalar S (tsze R M) :=
prod.is_central_scalar

instance [monoid S] [mul_action S R] [mul_action S M] : mul_action S (tsze R M) :=
prod.mul_action

instance [monoid S] [add_monoid R] [add_monoid M]
  [distrib_mul_action S R] [distrib_mul_action S M] : distrib_mul_action S (tsze R M) :=
prod.distrib_mul_action

instance [semiring S] [add_comm_monoid R] [add_comm_monoid M]
  [module S R] [module S M] : module S (tsze R M) :=
prod.module

@[simp] lemma fst_zero [has_zero R] [has_zero M] : (0 : tsze R M).fst = 0 := rfl
@[simp] lemma snd_zero [has_zero R] [has_zero M] : (0 : tsze R M).snd = 0 := rfl

@[simp] lemma fst_add [has_add R] [has_add M] (x₁ x₂ : tsze R M) :
  (x₁ + x₂).fst = x₁.fst + x₂.fst := rfl
@[simp] lemma snd_add [has_add R] [has_add M] (x₁ x₂ : tsze R M) :
  (x₁ + x₂).snd = x₁.snd + x₂.snd := rfl

@[simp] lemma fst_neg [has_neg R] [has_neg M] (x : tsze R M) : (-x).fst = -x.fst := rfl
@[simp] lemma snd_neg [has_neg R] [has_neg M] (x : tsze R M) : (-x).snd = -x.snd := rfl

@[simp] lemma fst_smul [has_scalar S R] [has_scalar S M] (s : S) (x : tsze R M) :
  (s • x).fst = s • x.fst := rfl
@[simp] lemma snd_smul [has_scalar S R] [has_scalar S M] (s : S) (x : tsze R M) :
  (s • x).snd = s • x.snd := rfl

section
variables (M)

@[simp] lemma inl_zero [has_zero R] [has_zero M] : (inl 0 : tsze R M) = 0 := rfl

@[simp] lemma inl_add [has_add R] [add_zero_class M] (r₁ r₂ : R) :
  (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
ext rfl (add_zero 0).symm

@[simp] lemma inl_neg [has_neg R] [add_group M] (r : R) :
  (inl (-r) : tsze R M) = -inl r :=
ext rfl neg_zero.symm

@[simp] lemma inl_smul [monoid S] [add_monoid M] [has_scalar S R] [distrib_mul_action S M]
  (s : S) (r : R) : (inl (s • r) : tsze R M) = s • inl r :=
ext rfl (smul_zero s).symm

end

section
variables (R)

@[simp] lemma inr_zero [has_zero R] [has_zero M] : (inr 0 : tsze R M) = 0 := rfl

@[simp] lemma inr_add [add_zero_class R] [add_zero_class M] (m₁ m₂ : M) :
  (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
ext (add_zero 0).symm rfl

@[simp] lemma inr_neg [add_group R] [has_neg M] (m : M) :
  (inr (-m) : tsze R M) = -inr m :=
ext neg_zero.symm rfl

@[simp] lemma inr_smul [has_zero R] [has_zero S] [smul_with_zero S R] [has_scalar S M]
  (r : S) (m : M) : (inr (r • m) : tsze R M) = r • inr m :=
ext (smul_zero' _ _).symm rfl

end

lemma inl_fst_add_inr_snd_eq [add_zero_class R] [add_zero_class M] (x : tsze R M) :
  inl x.fst + inr x.snd = x :=
ext (add_zero x.1) (zero_add x.2)

/-- To show a property hold on all `triv_sq_zero_ext R M` it suffices to show it holds
on terms of the form `inl r + inr m`.

This can be used as `induction x using triv_sq_zero_ext.ind`. -/
lemma ind {R M} [add_monoid R] [add_monoid M] {P : triv_sq_zero_ext R M → Prop}
  (h : ∀ r m, P (inl r + inr m)) (x) : P x :=
inl_fst_add_inr_snd_eq x ▸ h x.1 x.2

/-- The canonical `R`-linear inclusion `M → triv_sq_zero_ext R M`. -/
@[simps apply]
def inr_hom [semiring R] [add_comm_monoid M] [module R M] : M →ₗ[R] tsze R M :=
{ to_fun := inr, ..linear_map.inr _ _ _ }

end additive

/-! ### Multiplicative structure -/

section mul
variables {R : Type u} {M : Type v}

instance [has_one R] [has_zero M] : has_one (tsze R M) :=
⟨(1, 0)⟩

instance [has_mul R] [has_add M] [has_scalar R M] : has_mul (tsze R M) :=
⟨λ x y, (x.1 * y.1, x.1 • y.2 + y.1 • x.2)⟩

@[simp] lemma fst_one [has_one R] [has_zero M] : (1 : tsze R M).fst = 1 := rfl
@[simp] lemma snd_one [has_one R] [has_zero M] : (1 : tsze R M).snd = 0 := rfl

@[simp] lemma fst_mul [has_mul R] [has_add M] [has_scalar R M] (x₁ x₂ : tsze R M) :
  (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl
@[simp] lemma snd_mul [has_mul R] [has_add M] [has_scalar R M] (x₁ x₂ : tsze R M) :
  (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd := rfl

section
variables (M)

@[simp] lemma inl_one [has_one R] [has_zero M] : (inl 1 : tsze R M) = 1 := rfl

@[simp] lemma inl_mul [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ r₂ : R) :
  (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
ext rfl $ show (0 : M) = r₁ • 0 + r₂ • 0, by rw [smul_zero, zero_add, smul_zero]

lemma inl_mul_inl [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ r₂ : R) :
  (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
(inl_mul M r₁ r₂).symm

end

section
variables (R)

@[simp] lemma inr_mul_inr [semiring R] [add_comm_monoid M] [module R M] (m₁ m₂ : M) :
  (inr m₁ * inr m₂ : tsze R M) = 0 :=
ext (mul_zero _) $ show (0 : R) • m₂ + (0 : R) • m₁ = 0, by rw [zero_smul, zero_add, zero_smul]

end

lemma inl_mul_inr [semiring R] [add_comm_monoid M] [module R M] (r : R) (m : M) :
  (inl r * inr m : tsze R M) = inr (r • m) :=
ext (mul_zero r) $ show r • m + (0 : R) • 0 = r • m, by rw [smul_zero, add_zero]

lemma inr_mul_inl [semiring R] [add_comm_monoid M] [module R M] (r : R) (m : M) :
  (inr m * inl r : tsze R M) = inr (r • m) :=
ext (zero_mul r) $ show (0 : R) • 0 + r • m = r • m, by rw [smul_zero, zero_add]

instance [monoid R] [add_monoid M] [distrib_mul_action R M] : mul_one_class (tsze R M) :=
{ one_mul := λ x, ext (one_mul x.1) $ show (1 : R) • x.2 + x.1 • 0 = x.2,
    by rw [one_smul, smul_zero, add_zero],
  mul_one := λ x, ext (mul_one x.1) $ show (x.1 • 0 : M) + (1 : R) • x.2 = x.2,
    by rw [smul_zero, zero_add, one_smul],
  .. triv_sq_zero_ext.has_one,
  .. triv_sq_zero_ext.has_mul }

instance [semiring R] [add_comm_monoid M] [module R M] : non_assoc_semiring (tsze R M) :=
{ zero_mul := λ x, ext (zero_mul x.1) $ show (0 : R) • x.2 + x.1 • 0 = 0,
    by rw [zero_smul, zero_add, smul_zero],
  mul_zero := λ x, ext (mul_zero x.1) $ show (x.1 • 0 : M) + (0 : R) • x.2 = 0,
    by rw [smul_zero, zero_add, zero_smul],
  left_distrib := λ x₁ x₂ x₃, ext (mul_add x₁.1 x₂.1 x₃.1) $
    show x₁.1 • (x₂.2 + x₃.2) + (x₂.1 + x₃.1) • x₁.2 =
      x₁.1 • x₂.2 + x₂.1 • x₁.2 + (x₁.1 • x₃.2 + x₃.1 • x₁.2),
    by simp_rw [smul_add, add_smul, add_add_add_comm],
  right_distrib := λ x₁ x₂ x₃, ext (add_mul x₁.1 x₂.1 x₃.1) $
    show (x₁.1 + x₂.1) • x₃.2 + x₃.1 • (x₁.2 + x₂.2) =
      x₁.1 • x₃.2 + x₃.1 • x₁.2 + (x₂.1 • x₃.2 + x₃.1 • x₂.2),
    by simp_rw [add_smul, smul_add, add_add_add_comm],
  .. triv_sq_zero_ext.mul_one_class,
  .. triv_sq_zero_ext.add_comm_monoid }

instance [comm_monoid R] [add_monoid M] [distrib_mul_action R M] : monoid (tsze R M) :=
{ mul_assoc := λ x y z, ext (mul_assoc x.1 y.1 z.1) $
    show (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2) =
      x.1 • (y.1 • z.2 + z.1 • y.2) + (y.1 * z.1) • x.2,
    by simp_rw [smul_add, ← mul_smul, add_assoc, mul_comm],
  .. triv_sq_zero_ext.mul_one_class }

instance [comm_monoid R] [add_comm_monoid M] [distrib_mul_action R M] : comm_monoid (tsze R M) :=
{ mul_comm := λ x₁ x₂, ext (mul_comm x₁.1 x₂.1) $
    show x₁.1 • x₂.2 + x₂.1 • x₁.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2, from add_comm _ _,
  .. triv_sq_zero_ext.monoid }

instance [comm_semiring R] [add_comm_monoid M] [module R M] : comm_semiring (tsze R M) :=
{ .. triv_sq_zero_ext.comm_monoid,
  .. triv_sq_zero_ext.non_assoc_semiring }

/-- The canonical inclusion of rings `R → triv_sq_zero_ext R M`. -/
@[simps apply]
def inl_hom [semiring R] [add_comm_monoid M] [module R M] : R →+* tsze R M :=
{ to_fun := inl,
  map_one' := inl_one M,
  map_mul' := inl_mul M,
  map_zero' := inl_zero M,
  map_add' := inl_add M }

@[ext]
lemma linear_map_ext {N} [semiring R] [add_comm_monoid M] [add_comm_monoid N] [module R M]
  [module R N] ⦃f g : tsze R M →ₗ[R] N⦄
  (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) :
  f = g :=
linear_map.prod_ext (linear_map.ext hl) (linear_map.ext hr)

end mul

section algebra
variables (S : Type*) (R : Type u) (M : Type v)

instance algebra' [comm_semiring S] [comm_semiring R] [add_comm_monoid M]
  [algebra S R] [module S M] [module R M] [is_scalar_tower S R M] : algebra S (tsze R M) :=
{ commutes' := λ r x, mul_comm _ _,
  smul_def' := λ r x, ext (algebra.smul_def _ _) $
    show r • x.2 = algebra_map S R r • x.2 + x.1 • 0, by rw [smul_zero, add_zero, algebra_map_smul],
  .. triv_sq_zero_ext.inl_hom.comp (algebra_map S R) }
instance [comm_semiring R] [add_comm_monoid M] [module R M] : algebra R (tsze R M) :=
triv_sq_zero_ext.algebra' _ _ _

lemma algebra_map_eq_inl [comm_semiring R] [add_comm_monoid M] [module R M] :
  ⇑(algebra_map R (tsze R M)) = inl := rfl

/-- The canonical `R`-algebra projection `triv_sq_zero_ext R M → R`. -/
@[simps]
def fst_hom [comm_semiring R] [add_comm_monoid M] [module R M] : tsze R M →ₐ[R] R :=
{ to_fun := fst,
  map_one' := fst_one,
  map_mul' := fst_mul,
  map_zero' := fst_zero,
  map_add' := fst_add,
  commutes' := fst_inl }

/-- The canonical `R`-module projection `triv_sq_zero_ext R M → M`. -/
@[simps apply]
def snd_hom [semiring R] [add_comm_monoid M] [module R M] : tsze R M →ₗ[R] M :=
{ to_fun := snd, ..linear_map.snd _ _ _ }

variables {R S M}

lemma alg_hom_ext {A} [comm_semiring R] [add_comm_monoid M] [semiring A] [module R M]
  [algebra R A] ⦃f g : tsze R M →ₐ[R] A⦄ (h : ∀ m, f (inr m) = g (inr m)) :
  f = g :=
alg_hom.to_linear_map_injective $
  linear_map_ext (λ r, (f.commutes _).trans (g.commutes _).symm) h

@[ext]
lemma alg_hom_ext' {A} [comm_semiring R] [add_comm_monoid M] [semiring A] [module R M]
  [algebra R A]
  ⦃f g : tsze R M →ₐ[R] A⦄ (h : f.to_linear_map.comp inr_hom = g.to_linear_map.comp inr_hom) :
  f = g :=
alg_hom_ext $ linear_map.congr_fun h

end algebra

end triv_sq_zero_ext

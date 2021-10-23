/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import algebra.algebra.basic

/-!
# Trivial Square-Zero Extension

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/

universes u v w

/--
"Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
@[nolint has_inhabited_instance] def triv_sq_zero_ext (R : Type u) (M : Type v) :=
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

section add
variables (R : Type u) (M : Type v)

instance [has_zero R] [has_zero M] : has_zero (tsze R M) :=
prod.has_zero

@[simp] lemma fst_zero [has_zero R] [has_zero M] : (0 : tsze R M).fst = 0 := rfl
@[simp] lemma snd_zero [has_zero R] [has_zero M] : (0 : tsze R M).snd = 0 := rfl
@[simp] lemma inl_zero [has_zero R] [has_zero M] : (inl 0 : tsze R M) = 0 := rfl
@[simp] lemma inr_zero [has_zero R] [has_zero M] : (inr 0 : tsze R M) = 0 := rfl

instance [has_add R] [has_add M] : has_add (tsze R M) :=
prod.has_add

@[simp] lemma fst_add [has_add R] [has_add M] (x₁ x₂ : tsze R M) :
  (x₁ + x₂).fst = x₁.fst + x₂.fst := rfl
@[simp] lemma snd_add [has_add R] [has_add M] (x₁ x₂ : tsze R M) :
  (x₁ + x₂).snd = x₁.snd + x₂.snd := rfl

instance [has_neg R] [has_neg M] : has_neg (tsze R M) :=
prod.has_neg

@[simp] lemma fst_neg [has_neg R] [has_neg M] (x : tsze R M) : (-x).fst = -x.fst := rfl
@[simp] lemma snd_neg [has_neg R] [has_neg M] (x : tsze R M) : (-x).snd = -x.snd := rfl

instance [add_semigroup R] [add_semigroup M] : add_semigroup (tsze R M) :=
prod.add_semigroup

instance [add_monoid R] [add_monoid M] : add_monoid (tsze R M) :=
prod.add_monoid

@[simp] lemma inl_add [has_add R] [add_monoid M] (r₁ r₂ : R) :
  (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
ext rfl (add_zero 0).symm

@[simp] lemma inr_add [add_monoid R] [has_add M] (m₁ m₂ : M) :
  (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
ext (add_zero 0).symm rfl

lemma inl_fst_add_inr_snd_eq [add_monoid R] [add_monoid M] (x : tsze R M) :
  inl x.fst + inr x.snd = x :=
ext (add_zero x.1) (zero_add x.2)

instance [add_group R] [add_group M] : add_group (tsze R M) :=
prod.add_group

@[simp] lemma inl_neg [has_neg R] [add_group M] (r : R) :
  (inl (-r) : tsze R M) = -inl r :=
ext rfl neg_zero.symm

@[simp] lemma inr_neg [add_group R] [has_neg M] (m : M) :
  (inr (-m) : tsze R M) = -inr m :=
ext neg_zero.symm rfl

instance [add_comm_semigroup R] [add_comm_semigroup M] : add_comm_semigroup (tsze R M) :=
prod.add_comm_semigroup

instance [add_comm_monoid R] [add_comm_monoid M] : add_comm_monoid (tsze R M) :=
prod.add_comm_monoid

instance [add_comm_group R] [add_comm_group M] : add_comm_group (tsze R M) :=
prod.add_comm_group

end add

section smul
variables (R : Type u) (M : Type v)

instance [has_mul R] [has_scalar R M] : has_scalar R (tsze R M) :=
⟨λ r x, (r * x.1, r • x.2)⟩

@[simp] lemma fst_smul [has_mul R] [has_scalar R M] (r : R) (x : tsze R M) :
  (r • x).fst = r * x.fst := rfl
@[simp] lemma snd_smul [has_mul R] [has_scalar R M] (r : R) (x : tsze R M) :
  (r • x).snd = r • x.snd := rfl

@[simp] lemma inr_smul [mul_zero_class R] [has_scalar R M] (r : R) (m : M) :
  (inr (r • m) : tsze R M) = r • inr m :=
ext (mul_zero _).symm rfl

instance [monoid R] [mul_action R M] : mul_action R (tsze R M) :=
{ one_smul := λ x, ext (one_mul x.1) (one_smul R x.2) ,
  mul_smul := λ r₁ r₂ x, ext (mul_assoc r₁ r₂ x.1) (mul_smul r₁ r₂ x.2) }

instance [semiring R] [add_monoid M] [distrib_mul_action R M] : distrib_mul_action R (tsze R M) :=
{ smul_add := λ r x₁ x₂, ext (mul_add r x₁.1 x₂.1) (smul_add r x₁.2 x₂.2),
  smul_zero := λ r, ext (mul_zero r) (smul_zero r) }

instance [semiring R] [add_comm_monoid M] [module R M] : module R (tsze R M) :=
{ add_smul := λ r₁ r₂ x, ext (add_mul r₁ r₂ x.1) (add_smul r₁ r₂ x.2),
  zero_smul := λ x, ext (zero_mul x.1) (zero_smul R x.2) }

/-- The canonical `R`-linear inclusion `M → triv_sq_zero_ext R M`. -/
@[simps apply]
def inr_hom [semiring R] [add_comm_monoid M] [module R M] : M →ₗ[R] tsze R M :=
{ to_fun := inr,
  map_add' := inr_add R M,
  map_smul' := inr_smul R M }

end smul

section mul
variables (R : Type u) (M : Type v)

instance [has_one R] [has_zero M] : has_one (tsze R M) :=
⟨(1, 0)⟩

@[simp] lemma fst_one [has_one R] [has_zero M] : (1 : tsze R M).fst = 1 := rfl
@[simp] lemma snd_one [has_one R] [has_zero M] : (1 : tsze R M).snd = 0 := rfl
@[simp] lemma inl_one [has_one R] [has_zero M] : (inl 1 : tsze R M) = 1 := rfl

instance [has_mul R] [has_add M] [has_scalar R M] : has_mul (tsze R M) :=
⟨λ x y, (x.1 * y.1, x.1 • y.2 + y.1 • x.2)⟩

@[simp] lemma fst_mul [has_mul R] [has_add M] [has_scalar R M] (x₁ x₂ : tsze R M) :
  (x₁ * x₂).fst = x₁.fst * x₂.fst := rfl
@[simp] lemma snd_mul [has_mul R] [has_add M] [has_scalar R M] (x₁ x₂ : tsze R M) :
  (x₁ * x₂).snd = x₁.fst • x₂.snd + x₂.fst • x₁.snd := rfl

@[simp] lemma inl_mul [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ r₂ : R) :
  (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
ext rfl $ show (0 : M) = r₁ • 0 + r₂ • 0, by rw [smul_zero, zero_add, smul_zero]

lemma inl_mul_inl [monoid R] [add_monoid M] [distrib_mul_action R M] (r₁ r₂ : R) :
  (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
(inl_mul R M r₁ r₂).symm

lemma inl_mul_inr [semiring R] [add_comm_monoid M] [module R M] (r : R) (m : M) :
  (inl r * inr m : tsze R M) = inr (r • m) :=
ext (mul_zero r) $ show r • m + (0 : R) • 0 = r • m, by rw [smul_zero, add_zero]

lemma inr_mul_inl [semiring R] [add_comm_monoid M] [module R M] (r : R) (m : M) :
  (inr m * inl r : tsze R M) = inr (r • m) :=
ext (zero_mul r) $ show (0 : R) • 0 + r • m = r • m, by rw [smul_zero, zero_add]

@[simp] lemma inr_mul_inr [semiring R] [add_comm_monoid M] [module R M] (m₁ m₂ : M) :
  (inr m₁ * inr m₂ : tsze R M) = 0 :=
ext (mul_zero _) $ show (0 : R) • m₂ + (0 : R) • m₁ = 0, by rw [zero_smul, zero_add, zero_smul]

instance [comm_monoid R] [add_monoid M] [distrib_mul_action R M] : monoid (tsze R M) :=
{ mul_assoc := λ x y z, ext (mul_assoc x.1 y.1 z.1) $
    show (x.1 * y.1) • z.2 + z.1 • (x.1 • y.2 + y.1 • x.2) =
      x.1 • (y.1 • z.2 + z.1 • y.2) + (y.1 * z.1) • x.2,
    by simp_rw [smul_add, ← mul_smul, add_assoc, mul_comm],
  one_mul := λ x, ext (one_mul x.1) $ show (1 : R) • x.2 + x.1 • 0 = x.2,
    by rw [one_smul, smul_zero, add_zero],
  mul_one := λ x, ext (mul_one x.1) $ show (x.1 • 0 : M) + (1 : R) • x.2 = x.2,
    by rw [smul_zero, zero_add, one_smul],
  .. triv_sq_zero_ext.has_one R M,
  .. triv_sq_zero_ext.has_mul R M }

instance [comm_semiring R] [add_comm_monoid M] [module R M] : comm_semiring (tsze R M) :=
{ mul_comm := λ x₁ x₂, ext (mul_comm x₁.1 x₂.1) $
    show x₁.1 • x₂.2 + x₂.1 • x₁.2 = x₂.1 • x₁.2 + x₁.1 • x₂.2, from add_comm _ _,
  zero_mul := λ x, ext (zero_mul x.1) $ show (0 : R) • x.2 + x.1 • 0 = 0,
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
  .. triv_sq_zero_ext.monoid R M,
  .. triv_sq_zero_ext.add_comm_monoid R M }

/-- The canonical inclusion of rings `R → triv_sq_zero_ext R M`. -/
@[simps apply]
def inl_hom [comm_semiring R] [add_comm_monoid M] [module R M] : R →+* tsze R M :=
{ to_fun := inl,
  map_one' := inl_one R M,
  map_mul' := inl_mul R M,
  map_zero' := inl_zero R M,
  map_add' := inl_add R M }

end mul

section algebra
variables (R : Type u) (M : Type v)

instance [comm_semiring R] [add_comm_monoid M] [module R M] : algebra R (tsze R M) :=
{ commutes' := λ r x, mul_comm _ _,
  smul_def' := λ r x, ext rfl $ show r • x.2 = r • x.2 + x.1 • 0, by rw [smul_zero, add_zero],
  .. triv_sq_zero_ext.module R M,
  .. triv_sq_zero_ext.inl_hom R M }

/-- The canonical `R`-algebra projection `triv_sq_zero_ext R M → R`. -/
def fst_hom [comm_semiring R] [add_comm_monoid M] [module R M] : tsze R M →ₐ[R] R :=
{ to_fun := fst,
  map_one' := fst_one R M,
  map_mul' := fst_mul R M,
  map_zero' := fst_zero R M,
  map_add' := fst_add R M,
  commutes' := fst_inl }

/-- The canonical `R`-module projection `triv_sq_zero_ext R M → M`. -/
@[simps apply]
def snd_hom [semiring R] [add_comm_monoid M] [module R M] : tsze R M →ₗ[R] M :=
{ to_fun := snd,
  map_add' := snd_add R M,
  map_smul' := snd_smul R M}

end algebra

end triv_sq_zero_ext

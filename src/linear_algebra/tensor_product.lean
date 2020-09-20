/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/

import group_theory.congruence
import linear_algebra.basic

/-!
# Tensor product of semimodules over commutative semirings.

This file constructs the tensor product of semimodules over commutative semirings. Given a semiring
`R` and semimodules over it `M` and `N`, the standard construction of the tensor product is
`tensor_product R M N`. It is also a semimodule over `R`.

It comes with a canonical bilinear map `M → N → tensor_product R M N`.

Given any bilinear map `M → N → P`, there is a unique linear map `tensor_product R M N → P` whose
composition with the canonical bilinear map `M → N → tensor_product R M N` is the given bilinear
map `M → N → P`.

We start by proving basic lemmas about bilinear maps.

## Notations

This file uses the localized notation `M ⊗ N` and `M ⊗[R] N` for `tensor_product R M N`, as well
as `m ⊗ₜ n` and `m ⊗ₜ[R] n` for `tensor_product.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

namespace linear_map

variables {R : Type*} [comm_semiring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S]
variables [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S]
include R

variables (R)
/-- Create a bilinear map from a function that is linear in each component. -/
def mk₂ (f : M → N → P)
  (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)
  (H2 : ∀ (c:R) m n, f (c • m) n = c • f m n)
  (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)
  (H4 : ∀ (c:R) m n, f m (c • n) = c • f m n) : M →ₗ N →ₗ P :=
⟨λ m, ⟨f m, H3 m, λ c, H4 c m⟩,
λ m₁ m₂, linear_map.ext $ H1 m₁ m₂,
λ c m, linear_map.ext $ H2 c m⟩
variables {R}

@[simp] theorem mk₂_apply
  (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  (mk₂ R f H1 H2 H3 H4 : M →ₗ[R] N →ₗ P) m n = f m n := rfl

theorem ext₂ {f g : M →ₗ[R] N →ₗ[R] P}
  (H : ∀ m n, f m n = g m n) : f = g :=
linear_map.ext (λ m, linear_map.ext $ λ n, H m n)

/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to
`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def flip (f : M →ₗ[R] N →ₗ[R] P) : N →ₗ M →ₗ P :=
mk₂ R (λ n m, f m n)
  (λ n₁ n₂ m, (f m).map_add _ _)
  (λ c n m, (f m).map_smul _ _)
  (λ n m₁ m₂, by rw f.map_add; refl)
  (λ c n m, by rw f.map_smul; refl)

variable (f : M →ₗ[R] N →ₗ[R] P)

@[simp] theorem flip_apply (m : M) (n : N) : flip f n m = f m n := rfl

variables {R}
theorem flip_inj {f g : M →ₗ[R] N →ₗ P} (H : flip f = flip g) : f = g :=
ext₂ $ λ m n, show flip f n m = flip g n m, by rw H

variables (R M N P)
/-- Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map `M → N → P`,
change the order of variables and get a linear map from `N` to linear maps from `M` to `P`. -/
def lflip : (M →ₗ[R] N →ₗ P) →ₗ[R] N →ₗ M →ₗ P :=
⟨flip, λ _ _, rfl, λ _ _, rfl⟩
variables {R M N P}

@[simp] theorem lflip_apply (m : M) (n : N) : lflip R M N P f n m = f m n := rfl

theorem map_zero₂ (y) : f 0 y = 0 := (flip f y).map_zero

theorem map_neg₂ {R : Type*} [comm_ring R] {M N P : Type*}
  [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [module R M] [module R N] [module R P] (f : M →ₗ[R] N →ₗ[R] P) (x y) :
  f (-x) y = -f x y :=
(flip f y).map_neg _

theorem map_add₂ (x₁ x₂ y) : f (x₁ + x₂) y = f x₁ y + f x₂ y := (flip f y).map_add _ _

theorem map_smul₂ (r:R) (x y) : f (r • x) y = r • f x y := (flip f y).map_smul _ _

variables (R P)
/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def lcomp (f : M →ₗ[R] N) : (N →ₗ[R] P) →ₗ[R] M →ₗ[R] P :=
flip $ linear_map.comp (flip id) f

variables {R P}

@[simp] theorem lcomp_apply (f : M →ₗ[R] N) (g : N →ₗ P) (x : M) :
  lcomp R P f g x = g (f x) := rfl

variables (R M N P)
/-- Composing a linear map `M → N` and a linear map `N → P` to form a linear map `M → P`. -/
def llcomp : (N →ₗ[R] P) →ₗ[R] (M →ₗ[R] N) →ₗ M →ₗ P :=
flip ⟨lcomp R P,
  λ f f', ext₂ $ λ g x, g.map_add _ _,
  λ c f, ext₂ $ λ g x, g.map_smul _ _⟩
variables {R M N P}

section
@[simp] theorem llcomp_apply (f : N →ₗ[R] P) (g : M →ₗ[R] N) (x : M) :
  llcomp R M N P f g x = f (g x) := rfl
end

/-- Composing a linear map `Q → N` and a bilinear map `M → N → P` to
form a bilinear map `M → Q → P`. -/
def compl₂ (g : Q →ₗ N) : M →ₗ Q →ₗ P := (lcomp R _ g).comp f

@[simp] theorem compl₂_apply (g : Q →ₗ[R] N) (m : M) (q : Q) :
  f.compl₂ g m q = f m (g q) := rfl

/-- Composing a linear map `P → Q` and a bilinear map `M × N → P` to
form a bilinear map `M → N → Q`. -/
def compr₂ (g : P →ₗ Q) : M →ₗ N →ₗ Q :=
linear_map.comp (llcomp R N P Q g) f

@[simp] theorem compr₂_apply (g : P →ₗ[R] Q) (m : M) (n : N) :
  f.compr₂ g m n = g (f m n) := rfl

variables (R M)
/-- Scalar multiplication as a bilinear map `R → M → M`. -/
def lsmul : R →ₗ M →ₗ M :=
mk₂ R (•) add_smul (λ _ _ _, mul_smul _ _ _) smul_add
(λ r s m, by simp only [smul_smul, smul_eq_mul, mul_comm])
variables {R M}

@[simp] theorem lsmul_apply (r : R) (m : M) : lsmul R M r m = r • m := rfl

end linear_map

section semiring
variables {R : Type*} [comm_semiring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}

variables [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid P] [add_comm_monoid Q] [add_comm_monoid S]
variables [semimodule R M] [semimodule R N] [semimodule R P] [semimodule R Q] [semimodule R S]
include R

variables (M N)

namespace tensor_product

section
-- open free_add_monoid
variables (R)

/-- The relation on `free_add_monoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
inductive eqv : free_add_monoid (M × N) → free_add_monoid (M × N) → Prop
| of_zero_left : ∀ n : N, eqv (free_add_monoid.of (0, n)) 0
| of_zero_right : ∀ m : M, eqv (free_add_monoid.of (m, 0)) 0
| of_add_left : ∀ (m₁ m₂ : M) (n : N), eqv
    (free_add_monoid.of (m₁, n) + free_add_monoid.of (m₂, n)) (free_add_monoid.of (m₁ + m₂, n))
| of_add_right : ∀ (m : M) (n₁ n₂ : N), eqv
    (free_add_monoid.of (m, n₁) + free_add_monoid.of (m, n₂)) (free_add_monoid.of (m, n₁ + n₂))
| of_smul : ∀ (r : R) (m : M) (n : N), eqv
    (free_add_monoid.of (r • m, n)) (free_add_monoid.of (m, r • n))
| add_comm : ∀ x y, eqv (x + y) (y + x)
end

end tensor_product

variables (R)

/-- The tensor product of two semimodules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open_locale tensor_product`. -/
def tensor_product : Type* :=
(add_con_gen (tensor_product.eqv R M N)).quotient

variables {R}

localized "infix ` ⊗ `:100 := tensor_product _" in tensor_product
localized "notation M ` ⊗[`:100 R `] ` N:100 := tensor_product R M N" in tensor_product

namespace tensor_product

section module

instance : add_comm_monoid (M ⊗[R] N) :=
{ add_comm := λ x y, add_con.induction_on₂ x y $ λ x y, quotient.sound' $
    add_con_gen.rel.of _ _ $ eqv.add_comm _ _,
  .. (add_con_gen (tensor_product.eqv R M N)).add_monoid }

instance : inhabited (M ⊗[R] N) := ⟨0⟩

variables (R) {M N}
/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open_locale tensor_product`. -/
def tmul (m : M) (n : N) : M ⊗[R] N := add_con.mk' _ $ free_add_monoid.of (m, n)
variables {R}

infix ` ⊗ₜ `:100 := tmul _
notation x ` ⊗ₜ[`:100 R `] ` y := tmul R x y

@[elab_as_eliminator]
protected theorem induction_on
  {C : (M ⊗[R] N) → Prop}
  (z : M ⊗[R] N)
  (C0 : C 0)
  (C1 : ∀ {x y}, C $ x ⊗ₜ[R] y)
  (Cp : ∀ {x y}, C x → C y → C (x + y)) : C z :=
add_con.induction_on z $ λ x, free_add_monoid.rec_on x C0 $ λ ⟨m, n⟩ y ih,
by { rw add_con.coe_add, exact Cp C1 ih }

variables (M)
@[simp] lemma zero_tmul (n : N) : (0 ⊗ₜ n : M ⊗[R] N)  = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_left _
variables {M}

lemma add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_left _ _ _

variables (N)
@[simp] lemma tmul_zero (m : M) : (m ⊗ₜ 0 : M ⊗[R] N)  = 0 :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_zero_right _
variables {N}

lemma tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
eq.symm $ quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_add_right _ _ _

lemma smul_tmul (r : R) (m : M) (n : N) : (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
quotient.sound' $ add_con_gen.rel.of _ _ $ eqv.of_smul _ _ _

/-- Auxiliary function to defining scalar multiplication on tensor product. -/
def smul.aux (r : R) : free_add_monoid (M × N) →+ M ⊗[R] N :=
free_add_monoid.lift $ λ p : M × N, (r • p.1) ⊗ₜ p.2

theorem smul.aux_of (r : R) (m : M) (n : N) :
  smul.aux r (free_add_monoid.of (m, n)) = (r • m) ⊗ₜ n :=
rfl

instance : has_scalar R (M ⊗[R] N) :=
⟨λ r, (add_con_gen (tensor_product.eqv R M N)).lift (smul.aux r) $ add_con.add_con_gen_le $
λ x y hxy, match x, y, hxy with
| _, _, (eqv.of_zero_left n)       := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, smul_zero, zero_tmul]
| _, _, (eqv.of_zero_right m)      := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_zero, smul.aux_of, tmul_zero]
| _, _, (eqv.of_add_left m₁ m₂ n)  := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, smul.aux_of, smul_add, add_tmul]
| _, _, (eqv.of_add_right m n₁ n₂) := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, smul.aux_of, tmul_add]
| _, _, (eqv.of_smul s m n)        := (add_con.ker_rel _).2 $
    by simp_rw [smul.aux_of, smul_tmul, smul_smul, mul_comm]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end⟩

protected theorem smul_zero (r : R) : (r • 0 : M ⊗[R] N) = 0 :=
add_monoid_hom.map_zero _

protected theorem smul_add (r : R) (x y : M ⊗[R] N) :
  r • (x + y) = r • x + r • y :=
add_monoid_hom.map_add _ _ _

theorem smul_tmul' (r : R) (m : M) (n : N) :
  r • (m ⊗ₜ n : M ⊗[R] N) = (r • m) ⊗ₜ n :=
rfl

instance : semimodule R (M ⊗[R] N) :=
{ smul := (•),
  smul_add := λ r x y, tensor_product.smul_add r x y,
  mul_smul := λ r s x, tensor_product.induction_on x
    (by simp_rw tensor_product.smul_zero)
    (λ m n, by simp_rw [smul_tmul', mul_smul])
    (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy] }),
  one_smul := λ x, tensor_product.induction_on x
    (by rw tensor_product.smul_zero)
    (λ m n, by rw [smul_tmul', one_smul])
    (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy]),
  add_smul := λ r s x, tensor_product.induction_on x
    (by simp_rw [tensor_product.smul_zero, add_zero])
    (λ m n, by simp_rw [smul_tmul', add_smul, add_tmul])
    (λ x y ihx ihy, by { simp_rw tensor_product.smul_add, rw [ihx, ihy, add_add_add_comm] }),
  smul_zero := λ r, tensor_product.smul_zero r,
  zero_smul := λ x, tensor_product.induction_on x
    (by rw tensor_product.smul_zero)
    (λ m n, by rw [smul_tmul', zero_smul, zero_tmul])
    (λ x y ihx ihy, by rw [tensor_product.smul_add, ihx, ihy, add_zero]) }

@[simp] lemma tmul_smul (r : R) (x : M) (y : N) : x ⊗ₜ (r • y) = r • (x ⊗ₜ[R] y) :=
(smul_tmul _ _ _).symm

variables (R M N)
/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
def mk : M →ₗ N →ₗ M ⊗[R] N :=
linear_map.mk₂ R (⊗ₜ) add_tmul (λ c m n, by rw [smul_tmul, tmul_smul]) tmul_add tmul_smul
variables {R M N}

@[simp] lemma mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n := rfl

lemma ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [decidable P] :
  ((if P then x₁ else 0) ⊗ₜ[R] x₂) = if P then (x₁ ⊗ₜ x₂) else 0 :=
by { split_ifs; simp }

lemma tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [decidable P] :
  (x₁ ⊗ₜ[R] (if P then x₂ else 0)) = if P then (x₁ ⊗ₜ x₂) else 0 :=
by { split_ifs; simp }

section
open_locale big_operators

lemma sum_tmul {α : Type*} (s : finset α) (m : α → M) (n : N) :
  ((∑ a in s, m a) ⊗ₜ[R] n) = ∑ a in s, m a ⊗ₜ[R] n :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp, },
  { simp [finset.sum_insert has, add_tmul, ih], },
end

lemma tmul_sum (m : M) {α : Type*} (s : finset α) (n : α → N) :
  (m ⊗ₜ[R] (∑ a in s, n a)) = ∑ a in s, m ⊗ₜ[R] n a :=
begin
  classical,
  induction s using finset.induction with a s has ih h,
  { simp, },
  { simp [finset.sum_insert has, tmul_add, ih], },
end
end

end module

section UMP

variables {M N P Q}
variables (f : M →ₗ[R] N →ₗ[R] P)

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
    by simp_rw [free_add_monoid.lift_eval_of, f.map_smul₂, (f m).map_smul]
| _, _, (eqv.add_comm x y)         := (add_con.ker_rel _).2 $
    by simp_rw [add_monoid_hom.map_add, add_comm]
end

lemma lift_aux_tmul (m n) : lift_aux f (m ⊗ₜ n) = f m n :=
zero_add _

variable {f}

@[simp] lemma lift_aux.smul (r : R) (x) : lift_aux f (r • x) = r • lift_aux f x :=
tensor_product.induction_on x (smul_zero _).symm
  (λ p q, by rw [← tmul_smul, lift_aux_tmul, lift_aux_tmul, (f p).map_smul])
  (λ p q ih1 ih2, by rw [smul_add, (lift_aux f).map_add, ih1, ih2, (lift_aux f).map_add, smul_add])

variable (f)
/-- Constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P` with the property that
its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift : M ⊗ N →ₗ P :=
{ map_smul' := lift_aux.smul,
  .. lift_aux f }
variable {f}

@[simp] lemma lift.tmul (x y) : lift f (x ⊗ₜ y) = f x y :=
zero_add _

@[simp] lemma lift.tmul' (x y) : (lift f).1 (x ⊗ₜ y) = f x y :=
lift.tmul _ _

@[ext]
theorem ext {g h : (M ⊗[R] N) →ₗ[R] P}
  (H : ∀ x y, g (x ⊗ₜ y) = h (x ⊗ₜ y)) : g = h :=
linear_map.ext $ λ z, tensor_product.induction_on z (by simp_rw linear_map.map_zero) H $
λ x y ihx ihy, by rw [g.map_add, h.map_add, ihx, ihy]

theorem lift.unique {g : (M ⊗[R] N) →ₗ[R] P} (H : ∀ x y, g (x ⊗ₜ y) = f x y) :
  g = lift f :=
ext $ λ m n, by rw [H, lift.tmul]

theorem lift_mk : lift (mk R M N) = linear_map.id :=
eq.symm $ lift.unique $ λ x y, rfl

theorem lift_compr₂ (g : P →ₗ Q) : lift (f.compr₂ g) = g.comp (lift f) :=
eq.symm $ lift.unique $ λ x y, by simp

theorem lift_mk_compr₂ (f : M ⊗ N →ₗ P) : lift ((mk R M N).compr₂ f) = f :=
by rw [lift_compr₂ f, lift_mk, linear_map.comp_id]

theorem mk_compr₂_inj {g h : M ⊗ N →ₗ P}
  (H : (mk R M N).compr₂ g = (mk R M N).compr₂ h) : g = h :=
by rw [← lift_mk_compr₂ g, H, lift_mk_compr₂]

example : M → N → (M → N → P) → P :=
λ m, flip $ λ f, f m

variables (R M N P)
/-- Linearly constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def uncurry : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] M ⊗[R] N →ₗ[R] P :=
linear_map.flip $ lift $ (linear_map.lflip _ _ _ _).comp (linear_map.flip linear_map.id)
variables {R M N P}

@[simp] theorem uncurry_apply (f : M →ₗ[R] N →ₗ[R] P) (m : M) (n : N) :
  uncurry R M N P f (m ⊗ₜ n) = f m n :=
by rw [uncurry, linear_map.flip_apply, lift.tmul]; refl

variables (R M N P)
/-- A linear equivalence constructing a linear map `M ⊗ N → P` given a bilinear map `M → N → P`
with the property that its composition with the canonical bilinear map `M → N → M ⊗ N` is
the given bilinear map `M → N → P`. -/
def lift.equiv : (M →ₗ N →ₗ P) ≃ₗ (M ⊗ N →ₗ P) :=
{ inv_fun := λ f, (mk R M N).compr₂ f,
  left_inv := λ f, linear_map.ext₂ $ λ m n, lift.tmul _ _,
  right_inv := λ f, ext $ λ m n, lift.tmul _ _,
  .. uncurry R M N P }

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def lcurry : (M ⊗[R] N →ₗ[R] P) →ₗ[R] M →ₗ[R] N →ₗ[R] P :=
(lift.equiv R M N P).symm
variables {R M N P}

@[simp] theorem lcurry_apply (f : M ⊗[R] N →ₗ[R] P) (m : M) (n : N) :
  lcurry R M N P f m n = f (m ⊗ₜ n) := rfl

/-- Given a linear map `M ⊗ N → P`, compose it with the canonical bilinear map `M → N → M ⊗ N` to
form a bilinear map `M → N → P`. -/
def curry (f : M ⊗ N →ₗ P) : M →ₗ N →ₗ P := lcurry R M N P f

@[simp] theorem curry_apply (f : M ⊗ N →ₗ[R] P) (m : M) (n : N) :
  curry f m n = f (m ⊗ₜ n) := rfl

theorem ext_threefold {g h : (M ⊗[R] N) ⊗[R] P →ₗ[R] Q}
  (H : ∀ x y z, g ((x ⊗ₜ y) ⊗ₜ z) = h ((x ⊗ₜ y) ⊗ₜ z)) : g = h :=
begin
  let e := linear_equiv.to_equiv (lift.equiv R (M ⊗[R] N) P Q),
  apply e.symm.injective,
  refine ext _,
  intros x y,
  ext z,
  exact H x y z
end

-- We'll need this one for checking the pentagon identity!
theorem ext_fourfold {g h : ((M ⊗[R] N) ⊗[R] P) ⊗[R] Q →ₗ[R] S}
  (H : ∀ w x y z, g (((w ⊗ₜ x) ⊗ₜ y) ⊗ₜ z) = h (((w ⊗ₜ x) ⊗ₜ y) ⊗ₜ z)) : g = h :=
begin
  let e := linear_equiv.to_equiv (lift.equiv R ((M ⊗[R] N) ⊗[R] P) Q S),
  apply e.symm.injective,
  refine ext_threefold _,
  intros x y z,
  ext w,
  exact H x y z w,
end

end UMP

variables {M N}
section
variables (R M)

/--
The base ring is a left identity for the tensor product of modules, up to linear equivalence.
-/
protected def lid : R ⊗ M ≃ₗ M :=
linear_equiv.of_linear (lift $ linear_map.lsmul R M) (mk R R M 1)
  (linear_map.ext $ λ _, by simp)
  (ext $ λ r m, by simp; rw [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])
end

@[simp] theorem lid_tmul (m : M) (r : R) :
  ((tensor_product.lid R M) : (R ⊗ M → M)) (r ⊗ₜ m) = r • m :=
begin
  dsimp [tensor_product.lid],
  simp,
end

section
variables (R M N)

/--
The tensor product of modules is commutative, up to linear equivalence.
-/
protected def comm : M ⊗ N ≃ₗ N ⊗ M :=
linear_equiv.of_linear (lift (mk R N M).flip) (lift (mk R M N).flip)
  (ext $ λ m n, rfl)
  (ext $ λ m n, rfl)

@[simp] theorem comm_tmul (m : M) (n : N) :
  ((tensor_product.comm R M N) : (M ⊗ N → N ⊗ M)) (m ⊗ₜ n) = n ⊗ₜ m :=
begin
  dsimp [tensor_product.comm],
  simp,
end

end

section
variables (R M)

/--
The base ring is a right identity for the tensor product of modules, up to linear equivalence.
-/
protected def rid : M ⊗[R] R ≃ₗ M := linear_equiv.trans (tensor_product.comm R M R) (tensor_product.lid R M)
end

@[simp] theorem rid_tmul (m : M) (r : R) :
  ((tensor_product.rid R M) : (M ⊗ R → M)) (m ⊗ₜ r) = r • m :=
begin
  dsimp [tensor_product.rid, tensor_product.comm, tensor_product.lid],
  simp,
end

open linear_map
section
variables (R M N P)

/-- The associator for tensor product of R-modules, as a linear equivalence. -/
protected def assoc : (M ⊗[R] N) ⊗[R] P ≃ₗ[R] M ⊗[R] (N ⊗[R] P) :=
begin
  refine linear_equiv.of_linear
    (lift $ lift $ comp (lcurry R _ _ _) $ mk _ _ _)
    (lift $ comp (uncurry R _ _ _) $ curry $ mk _ _ _)
    (mk_compr₂_inj $ linear_map.ext $ λ m, ext $ λ n p, _)
    (mk_compr₂_inj $ flip_inj $ linear_map.ext $ λ p, ext $ λ m n, _);
  repeat { rw lift.tmul <|> rw compr₂_apply <|> rw comp_apply <|>
    rw mk_apply <|> rw flip_apply <|> rw lcurry_apply <|>
    rw uncurry_apply <|> rw curry_apply <|> rw id_apply }
end
end

@[simp] theorem assoc_tmul (m : M) (n : N) (p : P) :
  ((tensor_product.assoc R M N P) : (M ⊗[R] N) ⊗[R] P → M ⊗[R] (N ⊗[R] P)) ((m ⊗ₜ n) ⊗ₜ p) = m ⊗ₜ (n ⊗ₜ p) :=
rfl

/-- The tensor product of a pair of linear maps between modules. -/
def map (f : M →ₗ[R] P) (g : N →ₗ Q) : M ⊗ N →ₗ[R] P ⊗ Q :=
lift $ comp (compl₂ (mk _ _ _) g) f

@[simp] theorem map_tmul (f : M →ₗ[R] P) (g : N →ₗ[R] Q) (m : M) (n : N) :
  map f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

/-- If M and P are linearly equivalent and N and Q are linearly equivalent
then M ⊗ N and P ⊗ Q are linearly equivalent. -/
def congr (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) : M ⊗ N ≃ₗ[R] P ⊗ Q :=
linear_equiv.of_linear (map f g) (map f.symm g.symm)
  (ext $ λ m n, by simp; simp only [linear_equiv.apply_symm_apply])
  (ext $ λ m n, by simp; simp only [linear_equiv.symm_apply_apply])

@[simp] theorem congr_tmul (f : M ≃ₗ[R] P) (g : N ≃ₗ[R] Q) (m : M) (n : N) :
  congr f g (m ⊗ₜ n) = f m ⊗ₜ g n :=
rfl

end tensor_product

end semiring

section ring

namespace tensor_product

variables {R : Type*} [comm_ring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*} {S : Type*}

variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q] [add_comm_group S]
variables [module R M] [module R N] [module R P] [module R Q] [module R S]

open_locale tensor_product
open linear_map

instance : add_comm_group (M ⊗[R] N) :=
{ neg := tensor_product.lift $ (mk R M N).comp $ (-1 : R) • linear_map.id,
  add_left_neg := λ x,
    suffices (tensor_product.lift $ (mk R M N).comp $ (-1 : R) • linear_map.id) + linear_map.id = 0,
      from linear_map.ext_iff.1 this x,
    ext $ λ m n, by rw [add_apply, lift.tmul, comp_apply, mk_apply, smul_apply, neg_one_smul,
        id_apply, id_apply, ← add_tmul, neg_add_self, zero_tmul, zero_apply],
  .. tensor_product.add_comm_monoid M N }

lemma neg_tmul (m : M) (n : N) : (-m) ⊗ₜ n = -(m ⊗ₜ[R] n) := (mk R M N).map_neg₂ _ _
lemma tmul_neg (m : M) (n : N) : m ⊗ₜ (-n) = -(m ⊗ₜ[R] n) := (mk R M N _).map_neg _

end tensor_product

end ring

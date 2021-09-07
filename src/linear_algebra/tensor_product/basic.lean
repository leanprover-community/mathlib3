/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.congruence
import linear_algebra.bilinear_map

/-!
# Abstract typeclasses for tensor products
-/

open_locale big_operators

-- TODO: once there is a class for tensor products of algebras, mention it in this docstring.
/-- `has_tmul R M N T` is a typeclass that provides a tensor product `M → N → T` over `R`.
Morally, this asserts that `T` is the (`R`-linear) tensor product of `M` and `N`.
But this class only provides the raw function, and does not require any linearity conditions.
See `is_tensor_product R M N T` for the class that does assert such conditions.

The locale `tensor_product` provides notation `x ⊗[R] y` for this function. -/
class has_tmul (R M N : Type*) (T : out_param $ Type*) :=
(tmul : M → N → T)

localized "infix ` ⊗ `:100 := has_tmul.tmul _" in tensor_product
localized "notation x ` ⊗[`:100 R `] `:0 y:100 := has_tmul.tmul R x y" in tensor_product

instance has_scalar.to_has_tmul (R M : Type*) [has_scalar R M] : has_tmul R R M M :=
{ tmul := λ r m, r • m }

variables (R M N T : Type*)

/-- Uncurried version `M × N → T` of the tensor product: `(x, y) ↦ x ⊗ y`. -/
def tmul' [has_tmul R M N T] : M × N → T := function.uncurry $ has_tmul.tmul R

@[simp] lemma tmul'_apply [has_tmul R M N T] (x : M) (y : N) :
  tmul' R M N T (x,y) = x ⊗[R] y := rfl

/-- A typeclass predicate that asserts that a scalar product is compatible with a tensor product.
Assume `has_tmul R M N T`, which means that `T` is the (`R`-linear) tensor product of `M` and `N`,
and assume that `S` acts on both `M` and `T`.
Then this type class asserts `(c • x) ⊗[R] y = c • (x ⊗[R] y)`,
for all scalars `c : S`, and elements `x : M` and `y : N`. -/
class smul_tmul_class (S R M N : Type*) (T : out_param $ Type*)
  [has_tmul R M N T] [has_scalar S M] [has_scalar S T] :=
(smul_tmul' : ∀ (c : S) (x : M) (y : N), (c • x) ⊗[R] y = c • (x ⊗[R] y))

@[simp] lemma smul_tmul {S R M N T : Type*}
  [has_tmul R M N T] [has_scalar S M] [has_scalar S T] [smul_tmul_class S R M N T]
  (c : S) (x : M) (y : N) : (c • x) ⊗[R] y = c • (x ⊗[R] y) :=
smul_tmul_class.smul_tmul' c x y

/-- A typeclass predicate that asserts that a scalar product is compatible with a tensor product.
Assume `has_tmul R M N T`, which means that `T` is the (`R`-linear) tensor product of `M` and `N`,
and assume that `S` acts on both `N` and `T`.
Then this type class asserts `x ⊗[R] (c • y) = c • (x ⊗[R] y)`,
for all scalars `c : S`, and elements `x : M` and `y : N`. -/
class tmul_smul_class (R M N : Type*) (T : out_param $ Type*) (S : Type*)
  [has_tmul R M N T] [has_scalar S N] [has_scalar S T] :=
(tmul_smul' : ∀ (c : S) (x : M) (y : N), x ⊗[R] (c • y) = c • (x ⊗[R] y))

@[simp] lemma tmul_smul {R M N T S : Type*}
  [has_tmul R M N T] [has_scalar S N] [has_scalar S T] [tmul_smul_class R M N T S]
  (c : S) (x : M) (y : N) : x ⊗[R] (c • y) = c • (x ⊗[R] y) :=
tmul_smul_class.tmul_smul' c x y

namespace tensor_product

variables [semiring R] [add_comm_monoid M] [add_comm_monoid N]
variables [module R M] [module R N]

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

end tensor_product

-- TODO: generalize to noncommutative setup
/-- `is_tensor_product R M N T` asserts that `T` is the `R`-linear tensor product of `M` and `N`. -/
class is_tensor_product (R M N : Type*) (T : out_param $ Type*)
  [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T]
  [module R M] [module R N] [module R T]
  extends has_tmul R M N T, smul_tmul_class R R M N T, tmul_smul_class R M N T R :=
(add_tmul' : ∀ (x₁ x₂ : M) (y : N), (x₁ + x₂) ⊗[R] y = x₁ ⊗[R] y + x₂ ⊗[R] y)
(tmul_add' : ∀ (x : M) (y₁ y₂ : N), x ⊗[R] (y₁ + y₂) = x ⊗[R] y₁ + x ⊗[R] y₂)
(span_tmul : submodule.span R {t : T | ∃ (x : M) (y : N), x ⊗[R] y = t} = ⊤)
(add_con   : add_con.ker (free_add_monoid.lift (tmul' R M N T)) =
             add_con_gen (tensor_product.eqv R M N))

section is_tensor_product

variables {R M N T}
variables [comm_semiring R] [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T]
variables [module R M] [module R N] [module R T] [is_tensor_product R M N T]

include T

lemma span_tmul : submodule.span R {t : T | ∃ (x : M) (y : N), x ⊗[R] y = t} = ⊤ :=
is_tensor_product.span_tmul

lemma add_tmul (x₁ x₂ : M) (y : N) : (x₁ + x₂) ⊗[R] y = x₁ ⊗[R] y + x₂ ⊗[R] y :=
is_tensor_product.add_tmul' _ _ _

lemma tmul_add (x : M) (y₁ y₂ : N) : x ⊗[R] (y₁ + y₂) = x ⊗[R] y₁ + x ⊗[R] y₂ :=
is_tensor_product.tmul_add' _ _ _

variables (R M N)

/-- The `R`-linear tensor product as bilinear map. -/
@[simps] def tmul : M →ₗ[R] N →ₗ[R] T :=
linear_map.mk₂ R (λ x y, x ⊗[R] y) add_tmul smul_tmul tmul_add tmul_smul

variables {R M N}

section add_con

local notation `Φ` := free_add_monoid.lift (tmul' R M N T)

@[simp] lemma zero_tmul (y : N) : (0:M) ⊗[R] y = (0:T) :=
show tmul _ _ _ (0:M) y = (0:T), by simp only [linear_map.map_zero, linear_map.zero_apply]

@[simp] lemma tmul_zero (x : M) : x ⊗[R] (0:N) = (0:T) :=
show tmul _ _ _ x (0:N) = (0:T), by simp only [linear_map.map_zero]

end add_con

lemma ite_tmul (x : M) (y : N) (P : Prop) [decidable P] :
  (if P then x else 0) ⊗[R] y = if P then x ⊗[R] y else (0:T) :=
by { split_ifs; simp only [zero_tmul, eq_self_iff_true] }

lemma tmul_ite (x : M) (y : N) (P : Prop) [decidable P] :
  x ⊗[R] (if P then y else 0) = if P then x ⊗[R] y else (0:T) :=
by { split_ifs; simp only [tmul_zero, eq_self_iff_true] }

lemma sum_tmul {α : Type*} (s : finset α) (m : α → M) (n : N) :
  (∑ a in s, m a) ⊗[R] n = ∑ a in s, m a ⊗[R] n :=
show tmul _ _ _ (∑ a in s, m a) n = ∑ a in s, tmul _ _ _ (m a) n,
by simp only [finset.sum_apply, linear_map.coe_fn_sum, linear_map.map_sum]

lemma tmul_sum (m : M) {α : Type*} (s : finset α) (n : α → N) :
  m ⊗[R] (∑ a in s, n a) = ∑ a in s, m ⊗[R] n a :=
show tmul _ _ _ m (∑ a in s, n a) = ∑ a in s, tmul _ _ _ m (n a),
by simp only [linear_map.map_sum]

end is_tensor_product

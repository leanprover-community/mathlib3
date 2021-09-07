/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import group_theory.congruence
import linear_algebra.basic

/-!
# Abstract typeclasses for tensor products
-/

open_locale big_operators

class has_tmul (R M N : Type*) (T : out_param $ Type*) :=
(tmul : M → N → T)

localized "infix ` ⊗ `:100 := has_tmul.tmul _" in tensor_product
localized "notation x ` ⊗[`:100 R `] `:0 y:100 := has_tmul.tmul R x y" in tensor_product

variables (R M N T : Type*) [has_tmul R M N T]

def tmul' : M × N → T := function.uncurry $ has_tmul.tmul R

class smul_tmul_class (S R M N : Type*) (T : out_param $ Type*)
  [has_tmul R M N T] [has_scalar S M] [has_scalar S T] :=
(smul_tmul' : ∀ (c : S) (x : M) (y : N), ((c • x) ⊗[R] y) = c • (x ⊗[R] y))

class tmul_smul_class (R M N : Type*) (T : out_param $ Type*) (S : Type*)
  [has_tmul R M N T] [has_scalar S N] [has_scalar S T] :=
(tmul_smul' : ∀ (c : S) (x : M) (y : N), (x ⊗[R] (c • y)) = c • (x ⊗[R] y))

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
class is_tensor_product (R M N : Type*) (T : out_param $ Type*)
  [semiring R] [add_comm_monoid M] [add_comm_monoid N] [add_comm_monoid T]
  [module R M] [module R N] [module R T]
  extends has_tmul R M N T, smul_tmul_class R R M N T, tmul_smul_class R M N T R :=
(add_tmul' : ∀ (x₁ x₂ : M) (y : N), (x₁ + x₂) ⊗[R] y = x₁ ⊗[R] y + x₂ ⊗[R] y)
(tmul_add' : ∀ (x : M) (y₁ y₂ : N), x ⊗[R] (y₁ + y₂) = x ⊗[R] y₁ + x ⊗[R] y₂)
(span_tmul : submodule.span R {t : T | ∃ (x : M) (y : N), x ⊗[R] y = t} = ⊤)
(add_con   : add_con.ker (free_add_monoid.lift (tmul' R M N T)) =
             add_con_gen (tensor_product.eqv R M N))

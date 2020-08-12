/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Utensil Song.
-/

import ..quadratic_form
import ..tensor_algebra
import group_theory.perm.sign

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic_form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic_form `Q` is denoted as
`clifford_algebra R M Q`.

Later on the module `M` can be specialized to a vector space `V` over a field `K` of
characteristic ≠ 2, or simply characteristic = 0. Some results only hold at the level of
generality of the space `clifford_algebra K V Qv`.

## Theorems

## Implementation details

-/

variables (R : Type*) [comm_ring R]
variables (M : Type*) [add_comm_group M] [module R M]
variables (Q : quadratic_form R M)

variables (K : Type*) [field K] [char_zero K] -- TODO: generalize to characteristic ≠ 2
variables (V : Type*) [add_comm_group V] [vector_space K V]
variables (Qv : quadratic_form K V)

variable {n : ℕ}

namespace clifford_algebra
open tensor_algebra

/--
An inductively defined relation on `tensor_algebra R M` used to define the Clifford algebra.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R M m) * (ι R M m)) (algebra_map _ _ (Q m))
| add_compat_left {a b c} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c} : rel a b → rel (c + a) (c + b)
| mul_compat_left {a b c} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c} : rel a b → rel (c * a) (c * b)

end clifford_algebra

/--
The Clifford algebra of an `R`-module `M` equipped with a quadratic_form `Q`.
-/
def clifford_algebra := quot (clifford_algebra.rel R M Q)

namespace clifford_algebra

instance : semiring (clifford_algebra R M Q) :=
{
  add := quot.map₂ (+) (λ _ _ _, rel.add_compat_right) (λ _ _ _, rel.add_compat_left),
  add_assoc := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_assoc, refl},
  zero := quot.mk _ 0,
  zero_add := by {rintros ⟨⟩, change quot.mk _ _ = _, rw zero_add },
  add_zero := by {rintros ⟨⟩, change quot.mk _ _ = _, rw add_zero },
  add_comm := by {rintros ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw add_comm, refl },
  mul := quot.map₂ (*) (λ _ _ _, rel.mul_compat_right) (λ _ _ _, rel.mul_compat_left),
  mul_assoc := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw mul_assoc, refl },
  one := quot.mk _ 1,
  one_mul := by {rintros ⟨⟩, change quot.mk _ _ = _, rw one_mul },
  mul_one := by {rintros ⟨⟩, change quot.mk _ _ = _, rw mul_one },
  zero_mul := by {rintros ⟨⟩, change quot.mk _ _ = _, rw zero_mul },
  mul_zero := by {rintros ⟨⟩, change quot.mk _ _ = _, rw mul_zero },
  left_distrib := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw left_distrib, refl },
  right_distrib := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw right_distrib, refl }
}

instance : inhabited (clifford_algebra R M Q) := ⟨0⟩

instance : has_scalar R (clifford_algebra R M Q) :=
{
  smul := λ r m, quot.lift_on m (λ x, quot.mk _ $ r • x) $
    λ a b h, by {simp_rw algebra.smul_def, exact quot.sound (rel.mul_compat_right h)}
}

instance : algebra R (clifford_algebra R M Q) :=
{
  to_fun := λ r, (quot.mk _ $ algebra_map _ _ r),
  map_one' := rfl,
  map_mul' := λ _ _, by {rw ring_hom.map_mul, refl },
  map_zero' := rfl,
  map_add' := λ _ _, by {rw ring_hom.map_add, refl },
  commutes' := begin
    rintros r ⟨⟩,
    change quot.mk _ _ = _,
    rw algebra.commutes r x,
    refl,
  end,
  smul_def' := begin
    rintros r ⟨⟩,
    change quot.mk _ _ = _,
    rw algebra.smul_def,
    refl,
  end
}

instance : ring (clifford_algebra K V Qv) := algebra.ring_of_comm_ring_algebra K

/-
TODO: The canonical quotient map `tensor_algebra R M → clifford_algebra R M Q`.
-/

/-
TODO: The canonical linear map `M →ₗ[R] clifford_algebra R M Q`.
-/

/-
TODO: The canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra R M Q` to `A`.
-/

variables {R M}

/-
TODO: theorems
-/

variables (R M)

/--
The canonical multilinear map from `fin n → M` into `clifford_algebra R M Q`.
-/
-- def prod : multilinear_map R (λ i : fin n, M) (clifford_algebra R M Q) := _

variables {R M}

/-
TODO: prod lemmas
-/

end clifford_algebra

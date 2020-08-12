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

/--
The canonical quotient map `tensor_algebra R M → clifford_algebra R M Q`.
-/
protected def quot : tensor_algebra R M →ₐ[R] clifford_algebra R M Q :=
  by refine_struct { to_fun := λ m, quot.mk _ m }; tauto

/-
The canonical linear map `M →ₗ[R] clifford_algebra R M Q`.
-/
def ι : M →ₗ[R] clifford_algebra R M Q :=
  (clifford_algebra.quot R M Q).to_linear_map.comp (tensor_algebra.ι R M)

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `clifford_algebra R M Q` to `A`.
-/
def lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m, f m * f m = (algebra_map _ _ (Q m)) ) :
  clifford_algebra R M Q →ₐ[R] A :=
{
  to_fun := λ a, quot.lift_on a (tensor_algebra.lift R M f) $ λ x y h,
  begin
    induction h,
    { simp only [cond, alg_hom.commutes, tensor_algebra.ι_comp_lift', alg_hom.map_mul] },
    repeat { simp only [alg_hom.map_add, h_ih] },
    repeat { simp only [alg_hom.map_mul, h_ih] },
  end,
  map_one' := by {change algebra_map _ _ _ = _, simp},
  map_mul' := begin
    rintros ⟨⟩ ⟨⟩,
    change tensor_algebra.lift _ _ _ _ = _,
    rw alg_hom.map_mul,
  end,
  map_zero' := by {change algebra_map _ _ _ = _, simp},
  map_add' := begin
    rintros ⟨⟩ ⟨⟩,
    change tensor_algebra.lift _ _ _ _ = _,
    rw alg_hom.map_add,
  end,
  commutes' := by tauto
}

variables {R M Q}

/-
TODO: theorems
-/
@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m, f m * f m = (algebra_map _ _ (Q m)) ) :
  (lift R M Q f cond).to_linear_map.comp (ι R M Q) = f :=
  by {ext, refl}

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m : M, f m * f m = (algebra_map _ _ (Q m)) )
  (g : clifford_algebra R M Q →ₐ[R] A) :
  g.to_linear_map.comp (ι R M Q) = f ↔ g = lift R M Q f cond :=
begin
  refine ⟨λ hyp, _, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  ext,
  rcases x,
  change (g.comp (clifford_algebra.quot _ _ _)) _ = tensor_algebra.lift _ _ _ _,
  suffices : g.comp (clifford_algebra.quot R M Q) = tensor_algebra.lift R M f, by rw this,
  apply tensor_algebra.hom_ext,
  finish,
end

@[simp]
theorem ι_square_quad (m : M) : (ι R M Q m) * (ι R M Q m) = (algebra_map _ _ (Q m)) :=
by apply quot.sound (rel.of _)

@[simp]
theorem comp_ι_square_quad {A: Type*} [semiring A] [algebra R A]
  (g : clifford_algebra R M Q →ₐ[R] A) (m : M) :
  (g.to_linear_map.comp (ι R M Q)) m * (g.to_linear_map.comp (ι R M Q)) m
    = (algebra_map _ _ (Q m)) :=
begin
  change g _ * g _ = (algebra_map _ _ (Q m)),
  simp [←alg_hom.map_mul, ι_square_quad, alg_hom.map_zero],
end

@[simp]
theorem lift_comp_ι {A : Type*} [semiring A] [algebra R A] (g : clifford_algebra R M Q →ₐ[R] A) :
  lift R M Q (g.to_linear_map.comp (ι R M Q)) (comp_ι_square_quad _) = g :=
  by {symmetry, rw ←lift_unique}

theorem hom_ext {A : Type*} [semiring A] [algebra R A] {f g : clifford_algebra R M Q →ₐ[R] A} :
  f.to_linear_map.comp (ι R M Q) = g.to_linear_map.comp (ι R M Q) → f = g :=
begin
  intro hyp,
  let h := g.to_linear_map.comp (ι R M Q),
  have : g = lift R M Q h (comp_ι_square_quad _), by rw ←lift_unique,
  rw [this, ←lift_unique, hyp],
end

lemma ι_add_mul (x y z : M) : ι R M Q (x + y) * ι R M Q z =
  ι R M Q x * ι R M Q z + ι R M Q y * ι R M Q z :=
by rw [linear_map.map_add, right_distrib]

lemma ι_mul_add (x y z : M) : ι R M Q x * ι R M Q (y + z) =
  ι R M Q x * ι R M Q y + ι R M Q x * ι R M Q z :=
by rw [linear_map.map_add, left_distrib]

local postfix ` ² `:71 := λ x, x * x

@[simp]
lemma ι_add_swap (x y : M) [invertible (2 : R)]:
  let
    π := ι R M Q,
    Φ := (quadratic_form.associated Q),
    π₀ := (algebra_map R (clifford_algebra R M Q)) in
  π x * π y + π y * π x = (π₀ (Φ x y))
    := sorry

variables (R M)

/--
The canonical multilinear map from `fin n → M` into `clifford_algebra R M Q`.
-/
def prod : multilinear_map R (λ i : fin n, M) (clifford_algebra R M Q) :=
{
  to_fun := λ ν : fin n → M , clifford_algebra.quot R M Q (tensor_algebra.mk R M ν),
  map_add' := λ _ _ _ _, by simp,
  map_smul' := λ _ _ _ _, by simp
}

variables {R M}

lemma prod_split (ν : fin n.succ → M) :
prod R M ν = ι R M Q (ν 0) * prod R M (λ i : fin n, ν i.succ) :=
begin
  change clifford_algebra.quot R M Q _ = _,
  rw tensor_algebra.mk_split,
  refl,
end

end clifford_algebra
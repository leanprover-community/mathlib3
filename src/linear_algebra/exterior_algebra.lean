/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Adam Topaz.
-/

import .tensor_algebra

/-!
# Exterior Algebras

We construct the exterior algebra of a semimodule `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-semimodule `M` is denoted as `exterior_algebra R M`.
It is endowed with the structure of an `R`-algebra.

Given a linear morphism `f : M → A` from a semimodule `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `exterior_algebra.lift R M f cond`.

The canonical linear map `M → exterior_algebra R M` is denoted `exterior_algebra.ι R M`.

## Theorems

The main theorems proved ensure that `exterior_algebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is  fact that the composition of `ι R M` with `lift R M f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R M f cond` with respect to 1.

## Implementation details

The exterior algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `exterior_algebra.rel R M` on `tensor_algebra R M`.
  This is the smallest relation which identifies squares of elements of `M` with `0`,
  and which is compatible with addition and multiplication.
2. The exterior algebra is the quotient of the tensor algebra by this relation.

-/

variables (R : Type*) [comm_semiring R]
variables (M : Type*) [add_comm_group M] [semimodule R M]

namespace exterior_algebra
open tensor_algebra

/--
An inductively defined relation on `tensor_algebra R M` used to define the exterior algebra.
-/
inductive rel : tensor_algebra R M → tensor_algebra R M → Prop
| of (m : M) : rel ((ι R M m) * (ι R M m)) 0
| add_compat_left {a b c} : rel a b → rel (a + c) (b + c)
| add_compat_right {a b c} : rel a b → rel (c + a) (c + b)
| mul_compat_left {a b c} : rel a b → rel (a * c) (b * c)
| mul_compat_right {a b c} : rel a b → rel (c * a) (c * b)

end exterior_algebra

/--
The exterior algebra of an `R`-semimodule `M`.
-/
def exterior_algebra := quot (exterior_algebra.rel R M)

namespace exterior_algebra


instance : semiring (exterior_algebra R M) :=
{ add := quot.map₂ (+) (λ _ _ _, rel.add_compat_right) (λ _ _ _, rel.add_compat_left),
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
  right_distrib := by {rintros ⟨⟩ ⟨⟩ ⟨⟩, change quot.mk _ _ = _, rw right_distrib, refl } }

instance : inhabited (exterior_algebra R M) := ⟨0⟩

instance : has_scalar R (exterior_algebra R M) :=
{ smul := λ r m, quot.lift_on m (λ x, quot.mk _ $ r • x) $
  λ a b h, by {simp_rw algebra.smul_def, exact quot.sound (rel.mul_compat_right h)} }

instance : algebra R (exterior_algebra R M) :=
{ to_fun := λ r, (quot.mk _ $ algebra_map _ _ r),
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
  end }

/--
The canonical linear map `M →ₗ[R] exterior_algebra R M`.
-/
def ι : M →ₗ[R] exterior_algebra R M :=
{ to_fun := λ m, quot.mk _ (tensor_algebra.ι _ _ m),
  map_add' := begin
    intros m n,
    rw linear_map.map_add,
    refl,
  end,
  map_smul' := begin
    intros r m,
    rw linear_map.map_smul,
    refl,
  end }

/--
The canonical quotient map `tensor_algebra R M → exterior_algebra R M`.
-/
protected def quot : tensor_algebra R M →ₐ[R] exterior_algebra R M :=
  by refine_struct { to_fun := λ m, quot.mk _ m }; tauto

/--
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `exterior_algebra R M` to `A`.
-/
def lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
  exterior_algebra R M →ₐ[R] A :=
{ to_fun := λ a, quot.lift_on a (tensor_algebra.lift R M f) $ λ x y h,
  begin
    induction h,
    { simp only [alg_hom.map_mul,tensor_algebra.ι_comp_lift',cond,alg_hom.map_zero] },
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
  commutes' := by tauto }

variables {R M}

@[simp]
theorem ι_comp_lift {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m, f m * f m = 0) : (lift R M f cond).to_linear_map.comp (ι R M) = f :=
  by {ext, refl}

@[simp]
theorem lift_unique {A : Type*} [semiring A] [algebra R A] (f : M →ₗ[R] A)
  (cond : ∀ m : M, f m * f m = 0)
  (g : exterior_algebra R M →ₐ[R] A) : g.to_linear_map.comp (ι R M) = f ↔ g = lift R M f cond :=
begin
  refine ⟨λ hyp, _, λ hyp, by rw [hyp, ι_comp_lift]⟩,
  ext,
  rcases x,
  change (g.comp (exterior_algebra.quot _ _)) _ = tensor_algebra.lift _ _ _ _,
  suffices : g.comp (exterior_algebra.quot R M) = tensor_algebra.lift R M f, by rw this,
  apply tensor_algebra.hom_ext,
  finish,
end

end exterior_algebra

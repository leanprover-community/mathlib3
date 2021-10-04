/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.basic

/-!

# The `restrict_scalars` type alias

See the documentation attached to the `restrict_scalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `is_scalar_tower`
typeclass instead.

## Main definitions

* `restrict_scalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
* `restrict_scalars.linear_equiv : restrict_scalars R S M ≃ₗ[S] M`: the equivalence as an
  `S`-module between the restricted and origianl space.
* `restrict_scalars.alg_equiv : restrict_scalars R S A ≃ₐ[S] A`: the equivalence as an `S`-algebra
   between the restricted and original space.

## See also

There are many similarly-named definitions elsewhere which do not refer to this type alias. These
refer to restricting the scalar type in a bundled type, such as from `A →ₗ[R] B` to `A →ₗ[S] B`:

* `linear_map.restrict_scalars`
* `linear_equiv.restrict_scalars`
* `alg_hom.restrict_scalars`
* `alg_equiv.restrict_scalars`
* `submodule.restrict_scalars`
* `subalgebra.restrict_scalars`
-/

variables (R S M A : Type*)

/-- If we put an `R`-algebra structure on a semiring `S`, we get a natural equivalence from the
category of `S`-modules to the category of representations of the algebra `S` (over `R`). The type
synonym `restrict_scalars` is essentially this equivalence.

Warning: use this type synonym judiciously! Consider an example where we want to construct an
`R`-linear map from `M` to `S`, given:
```lean
variables (R S M : Type*)
variables [comm_semiring R] [semiring S] [algebra R S] [add_comm_monoid M] [module S M]
```
With the assumptions above we can't directly state our map as we have no `module R M` structure, but
`restrict_scalars` permits it to be written as:
```lean
-- an `R`-module structure on `M` is provided by `restrict_scalars` which is compatible
example : restrict_scalars R S M →ₗ[R] S := sorry
```
However, it is usually better just to add this extra structure as an argument:
```lean
-- an `R`-module structure on `M` and proof of its compatibility is provided by the user
example [module R M] [is_scalar_tower R S M] : M →ₗ[R] S := sorry
```
The advantage of the second approach is that it defers the duty of providing the missing typeclasses
`[module R M] [is_scalar_tower R S M]`. If some concrete `M` naturally carries these (as is often
the case) then we have avoided `restrict_scalars` entirely. If not, we can pass
`restrict_scalars R S M` later on instead of `M`.

Note that this means we almost always want to state definitions and lemmas in the language of
`is_scalar_tower` rather than `restrict_scalars`.

An example of when one might want to use `restrict_scalars` would be if one has a vector space
over a field of characteristic zero and wishes to make use of the `ℚ`-algebra structure. -/
@[nolint unused_arguments]
def restrict_scalars (R S M : Type*) : Type* := M

instance [I : inhabited M] : inhabited (restrict_scalars R S M) := I

instance [I : add_comm_monoid M] : add_comm_monoid (restrict_scalars R S M) := I

instance [I : add_comm_group M] : add_comm_group (restrict_scalars R S M) := I

instance restrict_scalars.module_orig [semiring S] [add_comm_monoid M] [I : module S M] :
  module S (restrict_scalars R S M) := I

/-- `restrict_scalars.linear_equiv` is an equivalence of modules over the semiring `S`. -/
def restrict_scalars.linear_equiv [semiring S] [add_comm_monoid M] [module S M] :
  restrict_scalars R S M ≃ₗ[S] M :=
linear_equiv.refl S M

section module
variables [semiring S] [add_comm_monoid M] [comm_semiring R] [algebra R S] [module S M]

/--
When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[module R M] [module S M] [is_scalar_tower R S M]`.
-/
instance : module R (restrict_scalars R S M) :=
module.comp_hom M (algebra_map R S)

lemma restrict_scalars_smul_def (c : R) (x : restrict_scalars R S M) :
  c • x = ((algebra_map R S c) • x : M) := rfl

@[simp] lemma restrict_scalars.linear_equiv_map_smul (t : R) (x : restrict_scalars R S M) :
  restrict_scalars.linear_equiv R S M (t • x)
  = (algebra_map R S t) • restrict_scalars.linear_equiv R S M x :=
rfl

instance : is_scalar_tower R S (restrict_scalars R S M) :=
⟨λ r S M, by { rw [algebra.smul_def, mul_smul], refl }⟩

end module

section algebra

instance [I : semiring A] : semiring (restrict_scalars R S A) := I
instance [I : ring A] : ring (restrict_scalars R S A) := I
instance [I : comm_semiring A] : comm_semiring (restrict_scalars R S A) := I
instance [I : comm_ring A] : comm_ring (restrict_scalars R S A) := I

variables [comm_semiring S] [semiring A]

instance restrict_scalars.algebra_orig [I : algebra S A] : algebra S (restrict_scalars R S A) := I

variables [algebra S A]

/-- Tautological `S`-algebra isomorphism `restrict_scalars R S A ≃ₐ[S] A`. -/
def restrict_scalars.alg_equiv : restrict_scalars R S A ≃ₐ[S] A := alg_equiv.refl

variables [comm_semiring R] [algebra R S]

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance : algebra R (restrict_scalars R S A) :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _,
  .. (algebra_map S A).comp (algebra_map R S) }

end algebra

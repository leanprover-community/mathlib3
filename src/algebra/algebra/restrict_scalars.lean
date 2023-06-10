/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
import algebra.algebra.tower

/-!

# The `restrict_scalars` type alias

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

See the documentation attached to the `restrict_scalars` definition for advice on how and when to
use this type alias. As described there, it is often a better choice to use the `is_scalar_tower`
typeclass instead.

## Main definitions

* `restrict_scalars R S M`: the `S`-module `M` viewed as an `R` module when `S` is an `R`-algebra.
  Note that by default we do *not* have a `module S (restrict_scalars R S M)` instance
  for the original action.
  This is available as a def `restrict_scalars.module_orig` if really needed.
* `restrict_scalars.add_equiv : restrict_scalars R S M ≃+ M`: the additive equivalence
  between the restricted and original space (in fact, they are definitionally equal,
  but sometimes it is helpful to avoid using this fact, to keep instances from leaking).
* `restrict_scalars.ring_equiv : restrict_scalars R S A ≃+* A`: the ring equivalence
   between the restricted and original space when the module is an algebra.

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

section module

section
variables [semiring S] [add_comm_monoid M]

/-- We temporarily install an action of the original ring on `restrict_sclars R S M`. -/
def restrict_scalars.module_orig [I : module S M] :
  module S (restrict_scalars R S M) := I

variables [comm_semiring R] [algebra R S]
section
local attribute [instance] restrict_scalars.module_orig

/--
When `M` is a module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
module structure over `R`.

The preferred way of setting this up is `[module R M] [module S M] [is_scalar_tower R S M]`.
-/
instance [module S M] : module R (restrict_scalars R S M) :=
module.comp_hom M (algebra_map R S)

/--
This instance is only relevant when `restrict_scalars.module_orig` is available as an instance.
-/
instance [module S M] : is_scalar_tower R S (restrict_scalars R S M) :=
⟨λ r S M, by { rw [algebra.smul_def, mul_smul], refl }⟩

end

/--
When `M` is a right-module over a ring `S`, and `S` is an algebra over `R`, then `M` inherits a
right-module structure over `R`.
The preferred way of setting this up is
`[module Rᵐᵒᵖ M] [module Sᵐᵒᵖ M] [is_scalar_tower Rᵐᵒᵖ Sᵐᵒᵖ M]`.
-/
instance restrict_scalars.op_module [module Sᵐᵒᵖ M] : module Rᵐᵒᵖ (restrict_scalars R S M) :=
begin
  letI : module Sᵐᵒᵖ (restrict_scalars R S M) := ‹module Sᵐᵒᵖ M›,
  exact module.comp_hom M (algebra_map R S).op
end

instance restrict_scalars.is_central_scalar [module S M] [module Sᵐᵒᵖ M] [is_central_scalar S M] :
  is_central_scalar R (restrict_scalars R S M) :=
{ op_smul_eq_smul := λ r x, (op_smul_eq_smul (algebra_map R S r) (_ : M) : _)}

/--
The `R`-algebra homomorphism from the original coefficient algebra `S` to endomorphisms
of `restrict_scalars R S M`.
-/
def restrict_scalars.lsmul [module S M] : S →ₐ[R] module.End R (restrict_scalars R S M) :=
begin
  -- We use `restrict_scalars.module_orig` in the implementation,
  -- but not in the type.
  letI : module S (restrict_scalars R S M) := restrict_scalars.module_orig R S M,
  exact algebra.lsmul R (restrict_scalars R S M),
end

end

variables [add_comm_monoid M]

/-- `restrict_scalars.add_equiv` is the additive equivalence with the original module. -/
def restrict_scalars.add_equiv : restrict_scalars R S M ≃+ M :=
add_equiv.refl M

variables [comm_semiring R] [semiring S] [algebra R S] [module S M]

@[simp] lemma restrict_scalars.add_equiv_map_smul (c : R) (x : restrict_scalars R S M) :
  restrict_scalars.add_equiv R S M (c • x)
  = (algebra_map R S c) • restrict_scalars.add_equiv R S M x :=
rfl

lemma restrict_scalars.smul_def (c : R) (x : restrict_scalars R S M) :
  c • x = (restrict_scalars.add_equiv R S M).symm
    (algebra_map R S c • restrict_scalars.add_equiv R S M x) :=
rfl

lemma restrict_scalars.add_equiv_symm_map_algebra_map_smul (r : R) (x : M) :
  (restrict_scalars.add_equiv R S M).symm (algebra_map R S r • x)
  = r • (restrict_scalars.add_equiv R S M).symm x :=
rfl

lemma restrict_scalars.add_equiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
  (restrict_scalars.add_equiv R S M).symm ((r • s) • x)
  = r • (restrict_scalars.add_equiv R S M ).symm (s • x) :=
by { rw [algebra.smul_def, mul_smul], refl, }

lemma restrict_scalars.lsmul_apply_apply (s : S) (x : restrict_scalars R S M) :
  restrict_scalars.lsmul R S M s x =
    (restrict_scalars.add_equiv R S M).symm (s • (restrict_scalars.add_equiv R S M x)) :=
rfl

end module

section algebra

instance [I : semiring A] : semiring (restrict_scalars R S A) := I
instance [I : ring A] : ring (restrict_scalars R S A) := I
instance [I : comm_semiring A] : comm_semiring (restrict_scalars R S A) := I
instance [I : comm_ring A] : comm_ring (restrict_scalars R S A) := I

variables [semiring A]

/-- Tautological ring isomorphism `restrict_scalars R S A ≃+* A`. -/
def restrict_scalars.ring_equiv : restrict_scalars R S A ≃+* A := ring_equiv.refl _

variables [comm_semiring S] [algebra S A] [comm_semiring R] [algebra R S]

@[simp] lemma restrict_scalars.ring_equiv_map_smul (r : R) (x : restrict_scalars R S A) :
  restrict_scalars.ring_equiv R S A (r • x)
  = (algebra_map R S r) • restrict_scalars.ring_equiv R S A x :=
rfl

/-- `R ⟶ S` induces `S-Alg ⥤ R-Alg` -/
instance : algebra R (restrict_scalars R S A) :=
{ smul := (•),
  commutes' := λ r x, algebra.commutes _ _,
  smul_def' := λ _ _, algebra.smul_def _ _,
  .. (algebra_map S A).comp (algebra_map R S) }

@[simp] lemma restrict_scalars.ring_equiv_algebra_map (r : R) :
  restrict_scalars.ring_equiv R S A (algebra_map R (restrict_scalars R S A) r) =
    algebra_map S A (algebra_map R S r) :=
rfl

end algebra

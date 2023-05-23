/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import ring_theory.tensor_product

/-!
# Bimodules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

One frequently encounters situations in which several sets of scalars act on a single space, subject
to compatibility condition(s). A distinguished instance of this is the theory of bimodules: one has
two rings `R`, `S` acting on an additive group `M`, with `R` acting covariantly ("on the left")
and `S` acting contravariantly ("on the right"). The compatibility condition is just:
`(r • m) • s = r • (m • s)` for all `r : R`, `s : S`, `m : M`.

This situation can be set up in Mathlib as:
```lean
variables (R S M : Type*) [ring R] [ring S]
variables [add_comm_group M] [module R M] [module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]
```
The key fact is:
```lean
example : module (R ⊗[ℕ] Sᵐᵒᵖ) M := tensor_product.algebra.module
```
Note that the corresponding result holds for the canonically isomorphic ring `R ⊗[ℤ] Sᵐᵒᵖ` but it is
preferable to use the `R ⊗[ℕ] Sᵐᵒᵖ` instance since it works without additive inverses.

Bimodules are thus just a special case of `module`s and most of their properties follow from the
theory of `module`s`. In particular a two-sided submodule of a bimodule is simply a term of type
`submodule (R ⊗[ℕ] Sᵐᵒᵖ) M`.

This file is a place to collect results which are specific to bimodules.

## Main definitions

 * `subbimodule.mk`
 * `subbimodule.smul_mem`
 * `subbimodule.smul_mem'`
 * `subbimodule.to_submodule`
 * `subbimodule.to_submodule'`

## Implementation details

For many definitions and lemmas it is preferable to set things up without opposites, i.e., as:
`[module S M] [smul_comm_class R S M]` rather than `[module Sᵐᵒᵖ M] [smul_comm_class R Sᵐᵒᵖ M]`.
The corresponding results for opposites then follow automatically and do not require taking
advantage of the fact that `(Sᵐᵒᵖ)ᵐᵒᵖ` is defeq to `S`.

## TODO

Develop the theory of two-sided ideals, which have type `submodule (R ⊗[ℕ] Rᵐᵒᵖ) R`.

-/

open_locale tensor_product

local attribute [instance] tensor_product.algebra.module

namespace subbimodule

section algebra

variables {R A B M : Type*}
variables [comm_semiring R] [add_comm_monoid M] [module R M]
variables [semiring A] [semiring B] [module A M] [module B M]
variables [algebra R A] [algebra R B]
variables [is_scalar_tower R A M] [is_scalar_tower R B M]
variables [smul_comm_class A B M]

/-- A constructor for a subbimodule which demands closure under the two sets of scalars
individually, rather than jointly via their tensor product.

Note that `R` plays no role but it is convenient to make this generalisation to support the cases
`R = ℕ` and `R = ℤ` which both show up naturally. See also `base_change`. -/
@[simps] def mk (p : add_submonoid M)
  (hA : ∀ (a : A) {m : M}, m ∈ p → a • m ∈ p)
  (hB : ∀ (b : B) {m : M}, m ∈ p → b • m ∈ p) : submodule (A ⊗[R] B) M :=
{ carrier := p,
  smul_mem' := λ ab m, tensor_product.induction_on ab
   (λ hm, by simpa only [zero_smul] using p.zero_mem)
   (λ a b hm, by simpa only [tensor_product.algebra.smul_def] using hA a (hB b hm))
   (λ z w hz hw hm, by simpa only [add_smul] using p.add_mem (hz hm) (hw hm)),
  .. p }

lemma smul_mem (p : submodule (A ⊗[R] B) M) (a : A) {m : M} (hm : m ∈ p) : a • m ∈ p :=
begin
  suffices : a • m = a ⊗ₜ[R] (1 : B) • m, { exact this.symm ▸ p.smul_mem _ hm, },
  simp [tensor_product.algebra.smul_def],
end

lemma smul_mem' (p : submodule (A ⊗[R] B) M) (b : B) {m : M} (hm : m ∈ p) : b • m ∈ p :=
begin
  suffices : b • m = (1 : A) ⊗ₜ[R] b • m, { exact this.symm ▸ p.smul_mem _ hm, },
  simp [tensor_product.algebra.smul_def],
end

/-- If `A` and `B` are also `algebra`s over yet another set of scalars `S` then we may "base change"
from `R` to `S`. -/
@[simps] def base_change (S : Type*) [comm_semiring S] [module S M] [algebra S A] [algebra S B]
  [is_scalar_tower S A M] [is_scalar_tower S B M] (p : submodule (A ⊗[R] B) M) :
  submodule (A ⊗[S] B) M :=
mk p.to_add_submonoid (smul_mem p) (smul_mem' p)

/-- Forgetting the `B` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `A`. -/
@[simps] def to_submodule (p : submodule (A ⊗[R] B) M) : submodule A M :=
{ carrier := p,
  smul_mem' := smul_mem p,
  .. p }

/-- Forgetting the `A` action, a `submodule` over `A ⊗[R] B` is just a `submodule` over `B`. -/
@[simps] def to_submodule' (p : submodule (A ⊗[R] B) M) : submodule B M :=
{ carrier := p,
  smul_mem' := smul_mem' p,
  .. p }

end algebra

section ring

variables (R S M : Type*) [ring R] [ring S]
variables [add_comm_group M] [module R M] [module S M] [smul_comm_class R S M]

/-- A `submodule` over `R ⊗[ℕ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℤ] S`. -/
@[simps] def to_subbimodule_int (p : submodule (R ⊗[ℕ] S) M) : submodule (R ⊗[ℤ] S) M :=
base_change ℤ p

/-- A `submodule` over `R ⊗[ℤ] S` is naturally also a `submodule` over the canonically-isomorphic
ring `R ⊗[ℕ] S`. -/
@[simps] def to_subbimodule_nat (p : submodule (R ⊗[ℤ] S) M) : submodule (R ⊗[ℕ] S) M :=
base_change ℕ p

end ring

end subbimodule

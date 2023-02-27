/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import algebra.graded_monoid

/-!
# Additively-graded multiplicative action structures

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides a set of heterogeneous typeclasses for defining a multiplicative structure
over the sigma type `graded_monoid A` such that `(•) : A i → M j → M (i + j)`; that is to say, `A`
has an additively-graded multiplicative action on `M`. The typeclasses are:

* `graded_monoid.ghas_smul A M`
* `graded_monoid.gmul_action A M`

With the `sigma_graded` locale open, these respectively imbue:

* `has_smul (graded_monoid A) (graded_monoid M)`
* `mul_action (graded_monoid A) (graded_monoid M)`

For now, these typeclasses are primarily used in the construction of `direct_sum.gmodule.module` and
the rest of that file.

## Internally graded multiplicative actions

In addition to the above typeclasses, in the most frequent case when `A` is an indexed collection of
`set_like` subobjects (such as `add_submonoid`s, `add_subgroup`s, or `submodule`s), this file
provides the `Prop` typeclasses:

* `set_like.has_graded_smul A M` (which provides the obvious `graded_monoid.ghas_smul A` instance)

which provides the API lemma

* `set_like.graded_smul_mem_graded`

Note that there is no need for `set_like.graded_mul_action` or similar, as all the information it
would contain is already supplied by `has_graded_smul` when the objects within `A` and `M` have
a `mul_action` instance.

## tags

graded action
-/

set_option old_structure_cmd true

variables {ι : Type*}

namespace graded_monoid

/-! ### Typeclasses -/
section defs

variables (A : ι → Type*) (M : ι → Type*)

/-- A graded version of `has_smul`. Scalar multiplication combines grades additively, i.e.
if `a ∈ A i` and `m ∈ M j`, then `a • b` must be in `M (i + j)`-/
class ghas_smul [has_add ι] :=
(smul {i j} : A i → M j → M (i + j))

/-- A graded version of `has_mul.to_has_smul` -/
instance ghas_mul.to_ghas_smul [has_add ι] [ghas_mul A] : ghas_smul A A :=
{ smul := λ _ _, ghas_mul.mul }

instance ghas_smul.to_has_smul [has_add ι] [ghas_smul A M] :
  has_smul (graded_monoid A) (graded_monoid M) :=
⟨λ (x : graded_monoid A) (y : graded_monoid M), ⟨_, ghas_smul.smul x.snd y.snd⟩⟩

lemma mk_smul_mk [has_add ι] [ghas_smul A M] {i j} (a : A i) (b : M j) :
  mk i a • mk j b = mk (i + j) (ghas_smul.smul a b) :=
rfl

/-- A graded version of `mul_action`. -/
class gmul_action [add_monoid ι] [gmonoid A] extends ghas_smul A M :=
(one_smul (b : graded_monoid M) : (1 : graded_monoid A) • b = b)
(mul_smul (a a' : graded_monoid A) (b : graded_monoid M) : (a * a') • b = a • a' • b)

/-- The graded version of `monoid.to_mul_action`. -/
instance gmonoid.to_gmul_action [add_monoid ι] [gmonoid A] :
  gmul_action A A :=
{ one_smul := gmonoid.one_mul,
  mul_smul := gmonoid.mul_assoc,
  ..ghas_mul.to_ghas_smul _ }

instance gmul_action.to_mul_action [add_monoid ι] [gmonoid A] [gmul_action A M] :
  mul_action (graded_monoid A) (graded_monoid M) :=
{ one_smul := gmul_action.one_smul,
  mul_smul := gmul_action.mul_smul }

end defs

end graded_monoid

/-! ### Shorthands for creating instance of the above typeclasses for collections of subobjects -/

section subobjects

variables {R : Type*}

/-- A version of `graded_monoid.ghas_smul` for internally graded objects. -/
class set_like.has_graded_smul {S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) : Prop :=
(smul_mem : ∀ ⦃i j : ι⦄ {ai bj}, ai ∈ A i → bj ∈ B j → ai • bj ∈ B (i + j))

instance set_like.ghas_smul {S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B] :
  graded_monoid.ghas_smul (λ i, A i) (λ i, B i) :=
{ smul := λ i j a b, ⟨(a : R) • b, set_like.has_graded_smul.smul_mem a.2 b.2⟩ }

@[simp] lemma set_like.coe_ghas_smul {S R N M : Type*} [set_like S R] [set_like N M]
  [has_smul R M] [has_add ι] (A : ι → S) (B : ι → N) [set_like.has_graded_smul A B]
  {i j : ι} (x : A i) (y : B j) :
  (@graded_monoid.ghas_smul.smul ι (λ i, A i) (λ i, B i) _ _ i j x y : M) = ((x : R) • y) :=
rfl

/-- Internally graded version of `has_mul.to_has_smul`. -/
instance set_like.has_graded_mul.to_has_graded_smul [add_monoid ι] [monoid R]
  {S : Type*} [set_like S R] (A : ι → S) [set_like.graded_monoid A] :
  set_like.has_graded_smul A A :=
{ smul_mem := λ i j ai bj hi hj, set_like.graded_monoid.mul_mem hi hj, }

end subobjects

section homogeneous_elements

variables {S R N M : Type*} [set_like S R] [set_like N M]

lemma set_like.is_homogeneous.graded_smul [has_add ι] [has_smul R M] {A : ι → S} {B : ι → N}
  [set_like.has_graded_smul A B] {a : R} {b : M} :
  set_like.is_homogeneous A a → set_like.is_homogeneous B b → set_like.is_homogeneous B (a • b)
| ⟨i, hi⟩ ⟨j, hj⟩ := ⟨i + j, set_like.has_graded_smul.smul_mem hi hj⟩

end homogeneous_elements

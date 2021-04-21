/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.dfinsupp
import data.finsupp.basic
import algebra.module.linear_map

/-!
# Conversion between `finsupp` and homogenous `dfinsupp`

This module provides an equivalence between `finsupp` and `dfinsupp`.
It is in its own file since neither `finsupp` or `dfinsupp` depend on each other.

## Main definitions

* `finsupp.to_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
* `finsupp.to_dfinsupp_add_equiv : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
* `finsupp.to_dfinsupp_linear_equiv R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`

## Theorems

We provide the fact that `finsupp.to_dfinsupp` preserves the function and support:

* `finsupp.to_dfinsupp_coe`
* `finsupp.to_dfinsupp_support`
* `finsupp.to_dfinsupp_symm_coe`
* `finsupp.to_dfinsupp_symm_support`

and therefore maps `finsupp.single` to `dfinsupp.single` and vice versa:

* `finsupp.to_dfinsupp_single`
* `finsupp.to_dfinsupp_symm_single`

For the bundled equivalences, we provide lemmas that they reduce to `finsupp.to_dfinsupp`:

* `finsupp.to_dfinsupp_add_equiv_apply`
* `finsupp.to_dfinsupp_linear_equiv_apply`
* `finsupp.to_dfinsupp_add_equiv_symm_apply`
* `finsupp.to_dfinsupp_linear_equiv_symm_apply`

and provided unapplied versions of the lemmas about `single` mentioned above:

* `to_dfinsupp_add_equiv_comp_single_add_hom`
* `to_dfinsupp_add_equiv_symm_comp_single_add_hom`

Variants of these for `finsupp.lsingle` and `dfinsupp.lsingle` are not provided to avoid importing
`linear_algebra.basic` into this file.

## Implementation notes

We provide `finsupp.to_dfinsupp` computably by adding `[decidable_eq ι]` and
`[Π m : M, decidable (m ≠ 0)]` arguments. There is little point adding these arguments to
`add_equiv` and `linear_equiv`, as they need the noncomputable additive structure on `finsupp`.

-/

variables {ι : Type*} {R : Type*} {M : Type*}

namespace finsupp

section equiv

variables [has_zero M] [decidable_eq ι] [Π m : M, decidable (m ≠ 0)]

/-- The canonical equivalence between `finsupp` and `dfinsupp`, preserving both the support and
the function. -/
def to_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M) :=
{ to_fun := λ f, ⟦⟨f, f.support.1, λ i,
    (classical.em (f i = 0)).symm.imp_left (finsupp.mem_support_iff.mpr)⟩⟧,
  inv_fun := λ f, ⟨f.support, f, λ i, by simp only [dfinsupp.mem_support_iff]⟩,
  left_inv := λ f, finsupp.coe_fn_injective rfl,
  right_inv := λ f, dfinsupp.coe_fn_injective rfl }

@[simp] lemma to_dfinsupp_coe (f : ι →₀ M) : ⇑f.to_dfinsupp = f := rfl
@[simp] lemma to_dfinsupp_support (f : ι →₀ M) : f.to_dfinsupp.support = f.support :=
by { ext, simp, }

@[simp] lemma to_dfinsupp_symm_coe (f : Π₀ i : ι, M) : ⇑(to_dfinsupp.symm f) = f := rfl
@[simp] lemma to_dfinsupp_symm_support (f : Π₀ i : ι, M) :
  (to_dfinsupp.symm f).support = f.support :=
by { ext, simp, }

@[simp] lemma to_dfinsupp_single (i : ι) (m : M) :
  (single i m).to_dfinsupp = dfinsupp.single i m :=
by { ext, simp [finsupp.single_apply, dfinsupp.single_apply] }

@[simp] lemma to_dfinsupp_symm_single (i : ι) (m : M) :
  to_dfinsupp.symm (dfinsupp.single i m) = single i m :=
by { ext, simp [finsupp.single_apply, dfinsupp.single_apply] }

end equiv

section add_equiv

open_locale classical

variables [add_zero_class M]

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
noncomputable def to_dfinsupp_add_equiv : (ι →₀ M) ≃+ (Π₀ i : ι, M) :=
{ to_fun := to_dfinsupp,
  inv_fun := to_dfinsupp.symm,
  map_add' := λ f g, dfinsupp.coe_fn_injective rfl,
  .. to_dfinsupp}

@[simp]
lemma to_dfinsupp_add_equiv_comp_single_add_hom (i : ι) :
  (to_dfinsupp_add_equiv : (ι →₀ M) ≃+ (Π₀ i : ι, M)).to_add_monoid_hom.comp (single_add_hom i) =
  dfinsupp.single_add_hom _ i :=
add_monoid_hom.ext $ to_dfinsupp_single i

@[simp]
lemma to_dfinsupp_add_equiv_symm_comp_single_add_hom (i : ι) :
  (to_dfinsupp_add_equiv : (ι →₀ M) ≃+ (Π₀ i : ι, M)).symm.to_add_monoid_hom.comp
    (dfinsupp.single_add_hom _ i) =
  single_add_hom i :=
add_monoid_hom.ext $ to_dfinsupp_symm_single i

-- we don't want `classical.dec` instances in our lemma conclusions below
variables [decidable_eq ι] [Π m : M, decidable (m ≠ 0)]

@[simp] lemma to_dfinsupp_add_equiv_apply (f : ι →₀ M) : to_dfinsupp_add_equiv f = to_dfinsupp f :=
rfl

@[simp] lemma to_dfinsupp_add_equiv_symm_apply (f : Π₀ i : ι, M) :
  (to_dfinsupp_add_equiv : (ι →₀ M) ≃+ (Π₀ i : ι, M)).symm f =
    (to_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)).symm f :=
by convert rfl  -- there are `decidable` instances to unify in the result

end add_equiv

section linear_equiv

open_locale classical

variables (R) [semiring R] [add_comm_monoid M] [semimodule R M]

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
noncomputable def to_dfinsupp_linear_equiv : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M) :=
{ to_fun := to_dfinsupp,
  inv_fun := to_dfinsupp.symm,
  map_add' := λ f g, dfinsupp.coe_fn_injective rfl,
  map_smul' := λ r f, dfinsupp.coe_fn_injective rfl,
  .. to_dfinsupp}

-- we don't want `classical.dec` instances in our lemma conclusions below
variables [decidable_eq ι] [Π m : M, decidable (m ≠ 0)]

@[simp] lemma to_dfinsupp_linear_equiv_apply (f : ι →₀ M) :
to_dfinsupp_linear_equiv R f = to_dfinsupp f := rfl

@[simp] lemma to_dfinsupp_linear_equiv_symm_apply (f : Π₀ i : ι, M) :
  (to_dfinsupp_linear_equiv R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)).symm f =
    (to_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)).symm f :=
to_dfinsupp_add_equiv_symm_apply f

end linear_equiv

end finsupp

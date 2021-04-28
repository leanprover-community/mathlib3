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

This module provides conversions between `finsupp` and `dfinsupp`.
It is in its own file since neither `finsupp` or `dfinsupp` depend on each other.

## Main definitions

* `finsupp.to_dfinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
* `dfinsupp.to_finsupp : (Π₀ i : ι, M) → (ι →₀ M)`
* Bundled equiv versions of the above:
  * `finsupp_equiv_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
  * `finsupp_add_equiv_dfinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
  * `finsupp_lequiv_dfinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `finsupp.to_dfinsupp_coe`
* `finsupp.to_dfinsupp_support`
* `dfinsupp.to_finsupp_coe`
* `dfinsupp.to_finsupp_support`

and therefore map `finsupp.single` to `dfinsupp.single` and vice versa:

* `finsupp.to_dfinsupp_single`
* `dfinsupp.to_finsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `finsupp.to_dfinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `dfinsupp.to_finsupp` and `finsupp_equiv_dfinsupp` computably by adding
`[decidable_eq ι]` and `[Π m : M, decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/

variables {ι : Type*} {R : Type*} {M : Type*}


/-! ### Basic definitions and lemmas -/
section defs

/-- Interpret a `finsupp` as a homogenous `dfinsupp`. -/
def finsupp.to_dfinsupp [has_zero M] (f : ι →₀ M) : Π₀ i : ι, M :=
⟦⟨f, f.support.1, λ i, (classical.em (f i = 0)).symm.imp_left (finsupp.mem_support_iff.mpr)⟩⟧

@[simp] lemma finsupp.to_dfinsupp_coe [has_zero M] (f : ι →₀ M) : ⇑f.to_dfinsupp = f := rfl

section
variables [decidable_eq ι] [has_zero M]

@[simp] lemma finsupp.to_dfinsupp_single (i : ι) (m : M) :
  (finsupp.single i m).to_dfinsupp = dfinsupp.single i m :=
by { ext, simp [finsupp.single_apply, dfinsupp.single_apply] }

variables [Π m : M, decidable (m ≠ 0)]

@[simp] lemma to_dfinsupp_support (f : ι →₀ M) : f.to_dfinsupp.support = f.support :=
by { ext, simp, }

/-- Interpret a homogenous `dfinsupp` as a `finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often necessary to
write `(dfinsupp.to_finsupp f : ι →₀ M)` instead of `f.to_finsupp`, as for some unknown reason
using dot notation or omitting the type ascription prevents the type being resolved correctly. -/
def dfinsupp.to_finsupp (f : Π₀ i : ι, M) : ι →₀ M :=
⟨f.support, f, λ i, by simp only [dfinsupp.mem_support_iff]⟩

@[simp] lemma dfinsupp.to_finsupp_coe (f : Π₀ i : ι, M) : ⇑f.to_finsupp = f := rfl
@[simp] lemma dfinsupp.to_finsupp_support (f : Π₀ i : ι, M) : f.to_finsupp.support = f.support :=
by { ext, simp, }

@[simp] lemma dfinsupp.to_finsupp_single (i : ι) (m : M) :
  (dfinsupp.single i m : Π₀ i : ι, M).to_finsupp = finsupp.single i m :=
by { ext, simp [finsupp.single_apply, dfinsupp.single_apply] }

@[simp] lemma finsupp.to_dfinsupp_to_finsupp (f : ι →₀ M) : f.to_dfinsupp.to_finsupp = f :=
finsupp.coe_fn_injective rfl

@[simp] lemma dfinsupp.to_finsupp_to_dfinsupp (f : Π₀ i : ι, M) : f.to_finsupp.to_dfinsupp = f :=
dfinsupp.coe_fn_injective rfl

end

end defs

/-! ### Lemmas about arithmetic operations -/
section lemmas

namespace finsupp

@[simp] lemma to_dfinsupp_zero [has_zero M] :
  (0 : ι →₀ M).to_dfinsupp = 0 := dfinsupp.coe_fn_injective rfl

@[simp] lemma to_dfinsupp_add [add_zero_class M] (f g : ι →₀ M) :
  (f + g).to_dfinsupp = f.to_dfinsupp + g.to_dfinsupp := dfinsupp.coe_fn_injective rfl

@[simp] lemma to_dfinsupp_neg [add_group M] (f : ι →₀ M) :
  (-f).to_dfinsupp = -f.to_dfinsupp := dfinsupp.coe_fn_injective rfl

@[simp] lemma to_dfinsupp_sub [add_group M] (f g : ι →₀ M) :
  (f - g).to_dfinsupp = f.to_dfinsupp - g.to_dfinsupp :=
dfinsupp.coe_fn_injective (sub_eq_add_neg _ _)

@[simp] lemma to_dfinsupp_smul [semiring R] [add_comm_monoid M] [semimodule R M]
  (r : R) (f : ι →₀ M) : (r • f).to_dfinsupp = r • f.to_dfinsupp :=
dfinsupp.coe_fn_injective rfl

end finsupp

namespace dfinsupp
variables [decidable_eq ι]

@[simp] lemma to_finsupp_zero [has_zero M] [Π m : M, decidable (m ≠ 0)] :
  to_finsupp 0 = (0 : ι →₀ M) := finsupp.coe_fn_injective rfl

@[simp] lemma to_finsupp_add [add_zero_class M] [Π m : M, decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
  (to_finsupp (f + g) : ι →₀ M) = (to_finsupp f + to_finsupp g) :=
finsupp.coe_fn_injective $ dfinsupp.coe_add _ _

@[simp] lemma to_finsupp_neg [add_group M] [Π m : M, decidable (m ≠ 0)] (f : Π₀ i : ι, M) :
  (to_finsupp (-f) : ι →₀ M) = -to_finsupp f :=
finsupp.coe_fn_injective $ dfinsupp.coe_neg _

@[simp] lemma to_finsupp_sub [add_group M] [Π m : M, decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
  (to_finsupp (f - g) : ι →₀ M) = to_finsupp f - to_finsupp g :=
finsupp.coe_fn_injective $ dfinsupp.coe_sub _ _

@[simp] lemma to_finsupp_smul [semiring R] [add_comm_monoid M] [semimodule R M]
  [Π m : M, decidable (m ≠ 0)]
  (r : R) (f : Π₀ i : ι, M) : (to_finsupp (r • f) : ι →₀ M) = r • to_finsupp f :=
finsupp.coe_fn_injective $ dfinsupp.coe_smul _ _

end dfinsupp

end lemmas

/-! ### Bundled `equiv`s -/

section equivs

/-- `finsupp.to_dfinsupp` and `dfinsupp.to_finsupp` together form an equiv. -/
@[simps {fully_applied := ff}]
def finsupp_equiv_dfinsupp [decidable_eq ι] [has_zero M] [Π m : M, decidable (m ≠ 0)] :
  (ι →₀ M) ≃ (Π₀ i : ι, M) :=
{ to_fun := finsupp.to_dfinsupp, inv_fun := dfinsupp.to_finsupp,
  left_inv := finsupp.to_dfinsupp_to_finsupp, right_inv := dfinsupp.to_finsupp_to_dfinsupp }

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps {fully_applied := ff}]
noncomputable def finsupp_add_equiv_dfinsupp
  [decidable_eq ι] [add_zero_class M] [Π m : M, decidable (m ≠ 0)] :
  (ι →₀ M) ≃+ (Π₀ i : ι, M) :=
{ to_fun := finsupp.to_dfinsupp, inv_fun := dfinsupp.to_finsupp,
  map_add' := finsupp.to_dfinsupp_add,
  .. finsupp_equiv_dfinsupp}

variables (R)

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps {fully_applied := ff}]
noncomputable def finsupp_lequiv_dfinsupp
  [decidable_eq ι] [semiring R] [add_comm_monoid M] [Π m : M, decidable (m ≠ 0)] [semimodule R M] :
  (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M) :=
{ to_fun := finsupp.to_dfinsupp, inv_fun := dfinsupp.to_finsupp,
  map_smul' := finsupp.to_dfinsupp_smul,
  map_add' := finsupp.to_dfinsupp_add,
  .. finsupp_equiv_dfinsupp}

end equivs

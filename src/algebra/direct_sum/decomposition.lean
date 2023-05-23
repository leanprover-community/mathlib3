/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Jujian Zhang
-/
import algebra.direct_sum.module
import algebra.module.submodule.basic

/-!
# Decompositions of additive monoids, groups, and modules into direct sums

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

* `direct_sum.decomposition ℳ`: A typeclass to provide a constructive decomposition from
  an additive monoid `M` into a family of additive submonoids `ℳ`
* `direct_sum.decompose ℳ`: The canonical equivalence provided by the above typeclass


## Main statements

* `direct_sum.decomposition.is_internal`: The link to `direct_sum.is_internal`.

## Implementation details

As we want to talk about different types of decomposition (additive monoids, modules, rings, ...),
we choose to avoid heavily bundling `direct_sum.decompose`, instead making copies for the
`add_equiv`, `linear_equiv`, etc. This means we have to repeat statements that follow from these
bundled homs, but means we don't have to repeat statements for different types of decomposition.
-/


variables {ι R M σ : Type*}
open_locale direct_sum big_operators
namespace direct_sum

section add_comm_monoid
variables [decidable_eq ι] [add_comm_monoid M]
variables [set_like σ M] [add_submonoid_class σ M] (ℳ : ι → σ)

/-- A decomposition is an equivalence between an additive monoid `M` and a direct sum of additive
submonoids `ℳ i` of that `M`, such that the "recomposition" is canonical. This definition also
works for additive groups and modules.

This is a version of `direct_sum.is_internal` which comes with a constructive inverse to the
canonical "recomposition" rather than just a proof that the "recomposition" is bijective. -/
class decomposition :=
(decompose' : M → ⨁ i, ℳ i)
(left_inv : function.left_inverse (direct_sum.coe_add_monoid_hom ℳ) decompose' )
(right_inv : function.right_inverse (direct_sum.coe_add_monoid_hom ℳ) decompose')

include M

/-- `direct_sum.decomposition` instances, while carrying data, are always equal. -/
instance : subsingleton (decomposition ℳ) :=
⟨λ x y, begin
  cases x with x xl xr,
  cases y with y yl yr,
  congr',
  exact function.left_inverse.eq_right_inverse xr yl,
end⟩

variables [decomposition ℳ]

protected lemma decomposition.is_internal : direct_sum.is_internal ℳ :=
⟨decomposition.right_inv.injective, decomposition.left_inv.surjective⟩

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
to a direct sum of components. This is the canonical spelling of the `decompose'` field. -/
def decompose : M ≃ ⨁ i, ℳ i :=
{ to_fun := decomposition.decompose',
  inv_fun := direct_sum.coe_add_monoid_hom ℳ,
  left_inv := decomposition.left_inv,
  right_inv := decomposition.right_inv }

protected lemma decomposition.induction_on {p : M → Prop}
  (h_zero : p 0) (h_homogeneous : ∀ {i} (m : ℳ i), p (m : M))
  (h_add : ∀ (m m' : M), p m → p m' → p (m + m')) : ∀ m, p m :=
begin
  let ℳ' : ι → add_submonoid M :=
    λ i, (⟨ℳ i, λ _ _, add_mem_class.add_mem, zero_mem_class.zero_mem _⟩ : add_submonoid M),
  haveI t : direct_sum.decomposition ℳ' :=
  { decompose' := direct_sum.decompose ℳ,
    left_inv := λ _, (decompose ℳ).left_inv _,
    right_inv := λ _, (decompose ℳ).right_inv _, },
  have mem : ∀ m, m ∈ supr ℳ' :=
    λ m, (direct_sum.is_internal.add_submonoid_supr_eq_top ℳ'
      (decomposition.is_internal ℳ')).symm ▸ trivial,
  exact λ m, add_submonoid.supr_induction ℳ' (mem m) (λ i m h, h_homogeneous ⟨m, h⟩) h_zero h_add,
end

@[simp] lemma decomposition.decompose'_eq : decomposition.decompose' = decompose ℳ := rfl

@[simp] lemma decompose_symm_of {i : ι} (x : ℳ i) :
  (decompose ℳ).symm (direct_sum.of _ i x) = x :=
direct_sum.coe_add_monoid_hom_of ℳ _ _

@[simp] lemma decompose_coe {i : ι} (x : ℳ i) :
  decompose ℳ (x : M) = direct_sum.of _ i x :=
by rw [←decompose_symm_of, equiv.apply_symm_apply]

lemma decompose_of_mem {x : M} {i : ι} (hx : x ∈ ℳ i) :
  decompose ℳ x = direct_sum.of (λ i, ℳ i) i ⟨x, hx⟩ :=
decompose_coe _ ⟨x, hx⟩

lemma decompose_of_mem_same {x : M} {i : ι} (hx : x ∈ ℳ i) :
  (decompose ℳ x i : M) = x :=
by rw [decompose_of_mem _ hx, direct_sum.of_eq_same, subtype.coe_mk]

lemma decompose_of_mem_ne {x : M} {i j : ι} (hx : x ∈ ℳ i) (hij : i ≠ j):
  (decompose ℳ x j : M) = 0 :=
by rw [decompose_of_mem _ hx, direct_sum.of_eq_of_ne _ _ _ _ hij,
  zero_mem_class.coe_zero]

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
an additive monoid to a direct sum of components. -/
@[simps {fully_applied := ff}]
def decompose_add_equiv : M ≃+ ⨁ i, ℳ i := add_equiv.symm
{ map_add' := map_add (direct_sum.coe_add_monoid_hom ℳ),
  ..(decompose ℳ).symm }

@[simp] lemma decompose_zero : decompose ℳ (0 : M) = 0 := map_zero (decompose_add_equiv ℳ)
@[simp] lemma decompose_symm_zero : (decompose ℳ).symm 0 = (0 : M) :=
map_zero (decompose_add_equiv ℳ).symm

@[simp] lemma decompose_add (x y : M) : decompose ℳ (x + y) = decompose ℳ x + decompose ℳ y :=
map_add (decompose_add_equiv ℳ) x y
@[simp] lemma decompose_symm_add (x y : ⨁ i, ℳ i) :
  (decompose ℳ).symm (x + y) = (decompose ℳ).symm x + (decompose ℳ).symm y :=
map_add (decompose_add_equiv ℳ).symm x y

@[simp] lemma decompose_sum {ι'} (s : finset ι') (f : ι' → M) :
  decompose ℳ (∑ i in s, f i) = ∑ i in s, decompose ℳ (f i) :=
map_sum (decompose_add_equiv ℳ) f s
@[simp] lemma decompose_symm_sum {ι'} (s : finset ι') (f : ι' → ⨁ i, ℳ i) :
  (decompose ℳ).symm (∑ i in s, f i) = ∑ i in s, (decompose ℳ).symm (f i) :=
map_sum (decompose_add_equiv ℳ).symm f s

lemma sum_support_decompose [Π i (x : ℳ i), decidable (x ≠ 0)] (r : M) :
  ∑ i in (decompose ℳ r).support, (decompose ℳ r i : M) = r :=
begin
  conv_rhs { rw [←(decompose ℳ).symm_apply_apply r,
    ←sum_support_of (λ i, (ℳ i)) (decompose ℳ r)] },
  rw [decompose_symm_sum],
  simp_rw decompose_symm_of,
end

end add_comm_monoid

/-- The `-` in the statements below doesn't resolve without this line.

This seems to a be a problem of synthesized vs inferred typeclasses disagreeing. If we replace
the statement of `decompose_neg` with `@eq (⨁ i, ℳ i) (decompose ℳ (-x)) (-decompose ℳ x)`
instead of `decompose ℳ (-x) = -decompose ℳ x`, which forces the typeclasses needed by `⨁ i, ℳ i` to
be found by unification rather than synthesis, then everything works fine without this instance. -/
instance add_comm_group_set_like [add_comm_group M] [set_like σ M] [add_subgroup_class σ M]
  (ℳ : ι → σ) : add_comm_group (⨁ i, ℳ i) := by apply_instance

section add_comm_group
variables [decidable_eq ι] [add_comm_group M]
variables [set_like σ M] [add_subgroup_class σ M] (ℳ : ι → σ)
variables [decomposition ℳ]
include M

@[simp] lemma decompose_neg (x : M) : decompose ℳ (-x) = -decompose ℳ x :=
map_neg (decompose_add_equiv ℳ) x
@[simp] lemma decompose_symm_neg (x : ⨁ i, ℳ i) :
  (decompose ℳ).symm (-x) = -(decompose ℳ).symm x :=
map_neg (decompose_add_equiv ℳ).symm x

@[simp] lemma decompose_sub (x y : M) : decompose ℳ (x - y) = decompose ℳ x - decompose ℳ y :=
map_sub (decompose_add_equiv ℳ) x y
@[simp] lemma decompose_symm_sub (x y : ⨁ i, ℳ i) :
  (decompose ℳ).symm (x - y) = (decompose ℳ).symm x - (decompose ℳ).symm y :=
map_sub (decompose_add_equiv ℳ).symm x y

end add_comm_group

section module
variables [decidable_eq ι] [semiring R] [add_comm_monoid M] [module R M]
variables (ℳ : ι → submodule R M)
variables [decomposition ℳ]
include M

/-- If `M` is graded by `ι` with degree `i` component `ℳ i`, then it is isomorphic as
a module to a direct sum of components. -/
@[simps {fully_applied := ff}]
def decompose_linear_equiv : M ≃ₗ[R] ⨁ i, ℳ i := linear_equiv.symm
{ map_smul' := map_smul (direct_sum.coe_linear_map ℳ),
  ..(decompose_add_equiv ℳ).symm }

@[simp] lemma decompose_smul (r : R) (x : M) : decompose ℳ (r • x) = r • decompose ℳ x :=
map_smul (decompose_linear_equiv ℳ) r x

end module

end direct_sum

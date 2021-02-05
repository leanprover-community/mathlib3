/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum
import algebra.algebra.basic
import group_theory.subgroup

/-!
# Additively-graded multiplicative structures on `⨁ i, A i`

This module provides a set of heterogenous typeclasses for defining a multiplicative structure
over `⨁ i, A i` such that `(*) : A i → A j → A (i + j)`; that is to say, `A` forms an
additively-graded ring. The typeclasses are:

* `direct_sum.ghas_one A`
* `direct_sum.ghas_mul A`
* `direct_sum.gmonoid A`
* `direct_sum.gcomm_monoid A`

Respectively, these imbue the direct sum `⨁ i, A i` with:

* `has_one`
* `mul_zero_class`, `distrib`
* `semiring`, `ring`
* `comm_semiring`, `comm_ring`

Additionally, this module provides helper functions to construct `gmonoid` and `gcomm_monoid`
instances for:

* `A : ι → submonoid S`: `direct_sum.ghas_one.of_submonoids`, `direct_sum.ghas_mul.of_submonoids`,
  `direct_sum.gmonoid.of_submonoids`, `direct_sum.gcomm_monoid.of_submonoids`
* `A : ι → subgroup S`: `direct_sum.ghas_one.of_subgroups`, `direct_sum.ghas_mul.of_subgroups`,
  `direct_sum.gmonoid.of_subgroups`, `direct_sum.gcomm_monoid.of_subgroups`
* `A : ι → submodule S`: `direct_sum.ghas_one.of_submodules`, `direct_sum.ghas_mul.of_submodules`,
  `direct_sum.gmonoid.of_submodules`, `direct_sum.gcomm_monoid.of_submodules`

If the `A i` are disjoint, these provide a gradation of `⨆ i, A i`, and the mapping
`⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

graded ring, filtered ring, direct sum, add_submonoid
-/

variables {ι : Type*} (A : ι → Type*) [decidable_eq ι]

namespace direct_sum

open_locale direct_sum

/-! ### Typeclasses -/
section defs

/-- A graded version of `has_one`, which must be of grade 0. -/
class ghas_one [has_zero ι] :=
(one : A 0)

/-- A graded version of `has_one` that also subsumes `distrib` and `mul_zero_class` by requiring
the multiplication be an `add_monoid_hom`. Multiplication combines grades additively, like
`add_monoid_algebra`. -/
class ghas_mul [add_monoid ι] [∀ i, add_comm_monoid (A i)] :=
(mul {i j} : A i →+ A j →+ A (i + j))

end defs

local notation `ᵍ1` := ghas_one.one
local infix `ᵍ*`:70 := ghas_mul.mul

section defs

/-- A graded version of `monoid`. -/
class gmonoid [add_monoid ι] [∀ i, add_comm_monoid (A i)] extends ghas_mul A, ghas_one A :=
(one_mul {i} (a : A i) : (⟨_, ᵍ1 ᵍ* a⟩ : Σ i, A i) = ⟨i, a⟩)
(mul_one {i} (a : A i) : (⟨_, a ᵍ* ᵍ1⟩ : Σ i, A i) = ⟨i, a⟩)
(mul_assoc {i j k} (a : A i) (b : A j) (c : A k) :
  (⟨_, a ᵍ* b ᵍ* c⟩ : Σ i, A i) = ⟨_, a ᵍ* (b ᵍ* c)⟩)

/-- A graded version of `comm_monoid`. -/
class gcomm_monoid [add_comm_monoid ι] [∀ i, add_comm_monoid (A i)] extends gmonoid A :=
(mul_comm {i j} (a : A i) (b : A j) : (⟨_, a ᵍ* b⟩ : Σ i, A i) = ⟨_, b ᵍ* a⟩)

end defs

/-! ### Shorthands for creating the above typeclasses -/

section shorthands

/-- Build a `ghas_one` instance for a collection of `add_submonoids`. -/
def ghas_one.of_submonoids {R : Type*} [semiring R] [add_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
{ one := ⟨1, one_mem⟩ }

/-- Build a `ghas_one` instance for a collection of `add_submonoid`s. -/
def ghas_one.of_subgroups {R : Type*} [ring R] [add_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0) :
  ghas_one (λ i, carriers i) :=
ghas_one.of_submonoids (λ i, (carriers i).to_add_submonoid) one_mem

/-- Build a `ghas_one` instance for a collection of `add_submonoids`. -/
def ghas_mul.of_submonoids {R : Type*} [semiring R] [add_monoid ι]
  (carriers : ι → add_submonoid R)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
{ mul := λ i j,
  { to_fun := λ a,
    { to_fun := λ b, ⟨(a * b : R), mul_mem a b⟩,
      map_add' := λ _ _, subtype.ext (mul_add _ _ _),
      map_zero' := subtype.ext (mul_zero _), },
    map_add' := λ _ _, add_monoid_hom.ext $ λ _, subtype.ext (add_mul _ _ _),
    map_zero' := add_monoid_hom.ext $ λ _, subtype.ext (zero_mul _) }, }

/-- Build a `ghas_one` instance for a collection of `add_submonoid`s. -/
def ghas_mul.of_subgroups {R : Type*} [ring R] [add_monoid ι]
  (carriers : ι → add_subgroup R)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  ghas_mul (λ i, carriers i) :=
ghas_mul.of_submonoids (λ i, (carriers i).to_add_submonoid) mul_mem

/-- Build a `gmonoid` instance for a collection of `add_submonoids`. -/
def gmonoid.of_submonoids {R : Type*} [semiring R] [add_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
{ one_mul := λ i a,
  begin
    have h := zero_add i,
    congr,
    exact h,
    rw subtype.heq_iff_coe_eq,
    { exact one_mul _ },
    { exact λ x, h.symm ▸ iff.rfl, }
  end,
  mul_one := λ i a,
  begin
    have h := add_zero i,
    congr,
    exact h,
    rw subtype.heq_iff_coe_eq,
    exact mul_one _,
    exact λ x, h.symm ▸ iff.rfl,
  end,
  mul_assoc := λ i j k a b c, begin
    have h := add_assoc i j k,
    congr,
    exact h,
    rw subtype.heq_iff_coe_eq,
    exact mul_assoc _ _ _,
    exact λ x, h.symm ▸ iff.rfl,
  end,
  ..ghas_one.of_submonoids carriers one_mem,
  ..ghas_mul.of_submonoids carriers mul_mem }

/-- Build a `gmonoid` instance for a collection of `add_submonoid`s. -/
def gmonoid.of_subgroups {R : Type*} [ring R] [add_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
gmonoid.of_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_monoid` instance for a collection of `submodules`s. -/
def gmonoid.of_submodules {R A : Type*}
  [comm_semiring R] [semiring A] [algebra R A] [add_comm_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gmonoid (λ i, carriers i) :=
gmonoid.of_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_monoid` instance for a collection of `add_submonoid`s. -/
def gcomm_monoid.of_submonoids {R : Type*} [comm_semiring R] [add_comm_monoid ι]
  (carriers : ι → add_submonoid R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
{ mul_comm := λ i j a b,
  begin
    have h := add_comm i j,
    congr,
    exact h,
    rw subtype.heq_iff_coe_eq,
    exact mul_comm _ _,
    exact λ x, h.symm ▸ iff.rfl,
  end,
  ..gmonoid.of_submonoids carriers one_mem mul_mem}

/-- Build a `gcomm_monoid` instance for a collection of `add_subgroup`s. -/
def gcomm_monoid.of_subgroups {R : Type*} [comm_ring R] [add_comm_monoid ι]
  (carriers : ι → add_subgroup R)
  (one_mem : (1 : R) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : R) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
gcomm_monoid.of_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

/-- Build a `gcomm_monoid` instance for a collection of `submodules`s. -/
def gcomm_monoid.of_submodules {R A : Type*}
  [comm_semiring R] [comm_semiring A] [algebra R A] [add_comm_monoid ι]
  (carriers : ι → submodule R A)
  (one_mem : (1 : A) ∈ carriers 0)
  (mul_mem : ∀ ⦃i j⦄ (gi : carriers i) (gj : carriers j), (gi * gj : A) ∈ carriers (i + j)) :
  gcomm_monoid (λ i, carriers i) :=
gcomm_monoid.of_submonoids (λ i, (carriers i).to_add_submonoid) one_mem mul_mem

end shorthands

/-! ### Instances for `⨁ i, A i` -/

section one
variables [has_zero ι] [ghas_one A] [∀ i, add_comm_monoid (A i)]

instance : has_one (⨁ i, A i) :=
{ one := direct_sum.of (λ i, A i) 0 ᵍ1}

end one

section mul
variables [add_monoid ι] [∀ i, add_comm_monoid (A i)] [ghas_mul A]

instance : has_mul (⨁ i, A i) :=
{ mul := λ a b, begin
    -- the elaborator struggles here, so use tactics to assemble the expression
    refine direct_sum.to_add_monoid (λ j,
      direct_sum.to_add_monoid (λ i,
        (add_monoid_hom.comp_hom (direct_sum.of A $ i + j)).comp _
      ) a
    ) b,
    exact (ᵍ*),
  end }

instance : mul_zero_class (⨁ i, A i) :=
{ mul := (*),
  zero := 0,
  zero_mul := by { unfold has_mul.mul, simp [direct_sum.to_add_monoid, direct_sum.of] },
  mul_zero := by { unfold has_mul.mul, simp [direct_sum.to_add_monoid, direct_sum.of] } }

instance : distrib (⨁ i, A i) :=
{ mul := (*),
  add := (+),
  left_distrib := by { unfold has_mul.mul, simp, },
  right_distrib := by { unfold has_mul.mul, simp [direct_sum.to_add_monoid, direct_sum.of], } }

end mul

/-! The various semiring fields are proved separately because the proofs are slow. -/

section semiring
variables [∀ i, add_comm_monoid (A i)] [add_monoid ι] [gmonoid A]

private lemma one_mul (x : ⨁ i, A i) : 1 * x = x :=
begin
  unfold has_one.one has_mul.mul,
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  convert add_monoid_hom.congr_fun (dfinsupp.sum_add_hom_single_add_hom) x,
  ext1 i, ext1 xi,
  exact dfinsupp.single_eq_of_sigma_eq (gmonoid.one_mul xi),
end

private lemma mul_one (x : ⨁ i, A i) : x * 1 = x :=
begin
  unfold has_one.one has_mul.mul,
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  rw add_monoid_hom.dfinsupp_sum_add_hom_apply x _,
  convert add_monoid_hom.congr_fun (dfinsupp.sum_add_hom_single_add_hom ) x,
  ext1 i, ext1 xi,
  simp [dfinsupp.single_eq_of_sigma_eq (gmonoid.mul_one xi)],
end

private lemma mul_assoc (a b c : ⨁ i, A i) : a * b * c = a * (b * c) :=
begin
  unfold has_one.one has_mul.mul,
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  simp only [←add_monoid_hom.comp_apply],
  simp only [dfinsupp.comp_sum_add_hom],

  -- unpack `c`
  refine add_monoid_hom.congr_fun _ c,
  congr' 1, ext1 ci, ext1 cx,

  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  rw add_monoid_hom.comp_apply,
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  rw ←add_monoid_hom.comp_apply,
  erw dfinsupp.comp_sum_add_hom,

  -- unpack `b`
  refine add_monoid_hom.congr_fun _ b,
  congr' 1, ext1 bi, ext1 bx,

  simp only [add_monoid_hom.comp_apply, add_monoid_hom.eval_apply, add_monoid_hom.coe_mk],
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  simp only [add_monoid_hom.map_dfinsupp_sum_add_hom, dfinsupp.single_add_hom_apply,
    dfinsupp.sum_add_hom_single, add_monoid_hom.comp_hom_apply_apply, add_monoid_hom.comp_apply],
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,

  -- unpack `a`
  refine add_monoid_hom.congr_fun _ a,
  congr' 1, ext1 ai, ext1 ax,

  simp [dfinsupp.single_eq_of_sigma_eq (gmonoid.mul_assoc ax bx cx)],
end

/-- The `semiring` structure derived from `gmonoid A`. -/
instance semiring : semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  one_mul := one_mul A,
  mul_one := mul_one A,
  mul_assoc := mul_assoc A,
  ..direct_sum.mul_zero_class A,
  ..direct_sum.distrib A,
  ..direct_sum.add_comm_monoid _ _, }

end semiring

section comm_semiring

variables [∀ i, add_comm_monoid (A i)] [add_comm_monoid ι] [gcomm_monoid A]

private lemma sum_add_hom_comm {ι₁ ι₂ : Sort*} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} {γ : Type*}
  [decidable_eq ι₁] [decidable_eq ι₂] [Π i, add_monoid (β₁ i)] [Π i, add_monoid (β₂ i)]
  [add_comm_monoid γ]
  (f₁ : Π₀ i, β₁ i) (f₂ : Π₀ i, β₂ i) (h : Π i j, β₁ i →+ β₂ j →+ γ) :
  dfinsupp.sum_add_hom (λ i₂, dfinsupp.sum_add_hom (λ i₁, h i₁ i₂) f₁) f₂ =
  dfinsupp.sum_add_hom (λ i₁, dfinsupp.sum_add_hom (λ i₂, (h i₁ i₂).flip) f₂) f₁ :=
quotient.induction_on f₁ $ λ x₁,
quotient.induction_on f₂ $ λ x₂,
begin
  simp only [dfinsupp.sum_add_hom, add_monoid_hom.finset_sum_apply, quotient.lift_on_mk,
    add_monoid_hom.coe_mk, add_monoid_hom.flip_apply],
  exact finset.sum_comm,
end

private lemma mul_comm (a b : ⨁ i, A i) : a * b = b * a :=
begin
  unfold has_one.one has_mul.mul,
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  rw sum_add_hom_comm,
  refine add_monoid_hom.congr_fun _ a,
  congr' 1, ext1 ai, ext1 ax,
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  erw add_monoid_hom.dfinsupp_sum_add_hom_apply,
  refine add_monoid_hom.congr_fun _ b,
  congr' 1, ext1 bi, ext1 bx,
  simp [dfinsupp.single_eq_of_sigma_eq (gcomm_monoid.mul_comm ax bx)],
end

/-- The `comm_semiring` structure derived from `gcomm_monoid A`. -/
instance comm_semiring : comm_semiring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  mul_comm := mul_comm A,
  ..direct_sum.semiring _, }

end comm_semiring

section ring
variables [∀ i, add_comm_group (A i)] [add_comm_monoid ι] [gmonoid A]

/-- The `ring` derived from `gmonoid A`. -/
instance ring : ring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.semiring _),
  ..(direct_sum.add_comm_group _), }


end ring

section comm_ring
variables [∀ i, add_comm_group (A i)] [add_comm_monoid ι] [gcomm_monoid A]

/-- The `comm_ring` derived from `gcomm_monoid A`. -/
instance comm_ring : ring (⨁ i, A i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  neg := has_neg.neg,
  ..(direct_sum.ring _),
  ..(direct_sum.comm_semiring _), }

end comm_ring

end direct_sum

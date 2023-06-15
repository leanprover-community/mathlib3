/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang
-/

import algebra.algebra.operations
import algebra.algebra.subalgebra.basic
import algebra.direct_sum.algebra

/-!
# Internally graded rings and algebras

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module provides `gsemiring` and `gcomm_semiring` instances for a collection of subobjects `A`
when a `set_like.graded_monoid` instance is available:

* `set_like.gnon_unital_non_assoc_semiring`
* `set_like.gsemiring`
* `set_like.gcomm_semiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `direct_sum.coe_ring_hom` (a `ring_hom` version of `direct_sum.coe_add_monoid_hom`)
* `direct_sum.coe_alg_hom` (an `alg_hom` version of `direct_sum.submodule_coe`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : direct_sum.is_internal A) [set_like.graded_monoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`direct_sum.is_internal` for providing an explicit decomposition function.

When `complete_lattice.independent (set.range A)` (a weaker condition than
`direct_sum.is_internal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`direct_sum.to_monoid (λ i, add_submonoid.inclusion $ le_supr A i)`.

## tags

internally graded ring
-/

open_locale direct_sum big_operators

variables {ι : Type*} {σ S R : Type*}

instance add_comm_monoid.of_submonoid_on_semiring [semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) : ∀ i, add_comm_monoid (A i) :=
λ i, by apply_instance

instance add_comm_group.of_subgroup_on_ring [ring R] [set_like σ R]
  [add_subgroup_class σ R] (A : ι → σ) : ∀ i, add_comm_group (A i) :=
λ i, by apply_instance

lemma set_like.algebra_map_mem_graded [has_zero ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.has_graded_one A] (s : S) : algebra_map S R s ∈ A 0 :=
begin
  rw algebra.algebra_map_eq_smul_one,
  exact ((A 0).smul_mem s $ set_like.one_mem_graded _),
end

lemma set_like.nat_cast_mem_graded [has_zero ι] [add_monoid_with_one R]
  [set_like σ R] [add_submonoid_class σ R] (A : ι → σ) [set_like.has_graded_one A] (n : ℕ) :
  (n : R) ∈ A 0 :=
begin
  induction n,
  { rw nat.cast_zero,
    exact zero_mem (A 0), },
  { rw nat.cast_succ,
    exact add_mem n_ih (set_like.one_mem_graded _), },
end

lemma set_like.int_cast_mem_graded [has_zero ι] [add_group_with_one R]
  [set_like σ R] [add_subgroup_class σ R] (A : ι → σ) [set_like.has_graded_one A] (z : ℤ) :
  (z : R) ∈ A 0:=
begin
  induction z,
  { rw int.cast_of_nat,
    exact set_like.nat_cast_mem_graded _ _, },
  { rw int.cast_neg_succ_of_nat,
    exact neg_mem (set_like.nat_cast_mem_graded _ _), },
end

section direct_sum
variables [decidable_eq ι]

/-! #### From `add_submonoid`s and `add_subgroup`s -/

namespace set_like

/-- Build a `gnon_unital_non_assoc_semiring` instance for a collection of additive submonoids. -/
instance gnon_unital_non_assoc_semiring [has_add ι] [non_unital_non_assoc_semiring R]
  [set_like σ R] [add_submonoid_class σ R]
  (A : ι → σ) [set_like.has_graded_mul A] :
  direct_sum.gnon_unital_non_assoc_semiring (λ i, A i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  ..set_like.ghas_mul A }

/-- Build a `gsemiring` instance for a collection of additive submonoids. -/
instance gsemiring [add_monoid ι] [semiring R] [set_like σ R] [add_submonoid_class σ R]
  (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gsemiring (λ i, A i) :=
{ mul_zero := λ i j _, subtype.ext (mul_zero _),
  zero_mul := λ i j _, subtype.ext (zero_mul _),
  mul_add := λ i j _ _ _, subtype.ext (mul_add _ _ _),
  add_mul := λ i j _ _ _, subtype.ext (add_mul _ _ _),
  nat_cast := λ n, ⟨n, set_like.nat_cast_mem_graded _ _⟩,
  nat_cast_zero := subtype.ext nat.cast_zero,
  nat_cast_succ := λ n, subtype.ext (nat.cast_succ n),
  ..set_like.gmonoid A }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcomm_semiring [add_comm_monoid ι] [comm_semiring R] [set_like σ R]
  [add_submonoid_class σ R] (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gcomm_semiring (λ i, A i) :=
{ ..set_like.gcomm_monoid A,
  ..set_like.gsemiring A, }

/-- Build a `gring` instance for a collection of additive subgroups. -/
instance gring [add_monoid ι] [ring R] [set_like σ R] [add_subgroup_class σ R]
  (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gring (λ i, A i) :=
{ int_cast := λ z, ⟨z, set_like.int_cast_mem_graded _ _⟩,
  int_cast_of_nat := λ n, subtype.ext $ int.cast_of_nat _,
  int_cast_neg_succ_of_nat := λ n, subtype.ext $ int.cast_neg_succ_of_nat n,
  ..set_like.gsemiring A }

/-- Build a `gcomm_semiring` instance for a collection of additive submonoids. -/
instance gcomm_ring [add_comm_monoid ι] [comm_ring R] [set_like σ R]
  [add_subgroup_class σ R] (A : ι → σ) [set_like.graded_monoid A] :
  direct_sum.gcomm_ring (λ i, A i) :=
{ ..set_like.gcomm_monoid A,
  ..set_like.gring A, }

end set_like

namespace direct_sum

section coe

variables [semiring R] [set_like σ R] [add_submonoid_class σ R] (A : ι → σ)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
def coe_ring_hom [add_monoid ι] [set_like.graded_monoid A] : (⨁ i, A i) →+* R :=
direct_sum.to_semiring (λ i, add_submonoid_class.subtype (A i)) rfl (λ _ _ _ _, rfl)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R`-/
@[simp] lemma coe_ring_hom_of [add_monoid ι] [set_like.graded_monoid A] (i : ι)
  (x : A i) : (coe_ring_hom A : _ →+* R) (of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ _ _ _ _

lemma coe_mul_apply [add_monoid ι] [set_like.graded_monoid A]
  [Π (i : ι) (x : A i), decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
  ((r * r') n : R) =
    ∑ ij in (r.support ×ˢ r'.support).filter (λ ij : ι × ι, ij.1 + ij.2 = n), r ij.1 * r' ij.2 :=
begin
  rw [mul_eq_sum_support_ghas_mul, dfinsupp.finset_sum_apply, add_submonoid_class.coe_finset_sum],
  simp_rw [coe_of_apply, ←finset.sum_filter, set_like.coe_ghas_mul],
end

lemma coe_mul_apply_eq_dfinsupp_sum [add_monoid ι] [set_like.graded_monoid A]
  [Π (i : ι) (x : A i), decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
  ((r * r') n : R) = r.sum (λ i ri, r'.sum (λ j rj, if i + j = n then ri * rj else 0)) :=
begin
  simp only [mul_eq_dfinsupp_sum, dfinsupp.sum_apply],
  iterate 2 { rw [dfinsupp.sum, add_submonoid_class.coe_finset_sum], congr, ext },
  dsimp only, split_ifs,
  { subst h, rw of_eq_same, refl },
  { rw of_eq_of_ne _ _ _ _ h, refl },
end

lemma coe_of_mul_apply_aux [add_monoid ι] [set_like.graded_monoid A] {i : ι}
  (r : A i) (r' : ⨁ i, A i) {j n : ι} (H : ∀ (x : ι), i + x = n ↔ x = j) :
  ((of _ i r * r') n : R) = r * r' j :=
begin
  classical,
  rw coe_mul_apply_eq_dfinsupp_sum,
  apply (dfinsupp.sum_single_index _).trans, swap,
  { simp_rw [zero_mem_class.coe_zero, zero_mul, if_t_t], exact dfinsupp.sum_zero },
  simp_rw [dfinsupp.sum, H, finset.sum_ite_eq'],
  split_ifs, refl,
  rw [dfinsupp.not_mem_support_iff.mp h, zero_mem_class.coe_zero, mul_zero],
end

lemma coe_mul_of_apply_aux [add_monoid ι] [set_like.graded_monoid A]
  (r : ⨁ i, A i) {i : ι} (r' : A i) {j n : ι} (H : ∀ (x : ι), x + i = n ↔ x = j) :
  ((r * of _ i r') n : R) = r j * r' :=
begin
  classical,
  rw [coe_mul_apply_eq_dfinsupp_sum, dfinsupp.sum_comm],
  apply (dfinsupp.sum_single_index _).trans, swap,
  { simp_rw [zero_mem_class.coe_zero, mul_zero, if_t_t], exact dfinsupp.sum_zero },
  simp_rw [dfinsupp.sum, H, finset.sum_ite_eq'],
  split_ifs, refl,
  rw [dfinsupp.not_mem_support_iff.mp h, zero_mem_class.coe_zero, zero_mul],
end

lemma coe_of_mul_apply_add [add_left_cancel_monoid ι] [set_like.graded_monoid A]
  {i : ι} (r : A i) (r' : ⨁ i, A i) (j : ι) :
  ((of _ i r * r') (i + j) : R) = r * r' j :=
coe_of_mul_apply_aux _ _ _ (λ x, ⟨λ h, add_left_cancel h, λ h, h ▸ rfl⟩)

lemma coe_mul_of_apply_add [add_right_cancel_monoid ι] [set_like.graded_monoid A]
  (r : ⨁ i, A i) {i : ι} (r' : A i) (j : ι) :
  ((r * of _ i r') (j + i) : R) = r j * r' :=
coe_mul_of_apply_aux _ _ _ (λ x, ⟨λ h, add_right_cancel h, λ h, h ▸ rfl⟩)

end coe

section canonically_ordered_add_monoid

variables [semiring R] [set_like σ R] [add_submonoid_class σ R] (A : ι → σ)
variables [canonically_ordered_add_monoid ι] [set_like.graded_monoid A]

lemma coe_of_mul_apply_of_not_le
  {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι)
  (h : ¬ i ≤ n) : ((of _ i r * r') n : R) = 0 :=
begin
  classical,
  rw coe_mul_apply_eq_dfinsupp_sum,
  apply (dfinsupp.sum_single_index _).trans, swap,
  { simp_rw [zero_mem_class.coe_zero, zero_mul, if_t_t], exact dfinsupp.sum_zero },
  { rw [dfinsupp.sum, finset.sum_ite_of_false _ _ (λ x _ H, _), finset.sum_const_zero],
    exact h ((self_le_add_right i x).trans_eq H) },
end

lemma coe_mul_of_apply_of_not_le
  (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι)
  (h : ¬ i ≤ n) : ((r * of _ i r') n : R) = 0 :=
begin
  classical,
  rw [coe_mul_apply_eq_dfinsupp_sum, dfinsupp.sum_comm],
  apply (dfinsupp.sum_single_index _).trans, swap,
  { simp_rw [zero_mem_class.coe_zero, mul_zero, if_t_t], exact dfinsupp.sum_zero },
  { rw [dfinsupp.sum, finset.sum_ite_of_false _ _ (λ x _ H, _), finset.sum_const_zero],
    exact h ((self_le_add_left i x).trans_eq H) },
end

variables [has_sub ι] [has_ordered_sub ι] [contravariant_class ι ι (+) (≤)]

/- The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
  state them for `canonically_ordered_add_monoid` + the above three typeclasses for convenience. -/

lemma coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι)
  (h : i ≤ n) : ((r * of _ i r') n : R) = r (n - i) * r' :=
coe_mul_of_apply_aux _ _ _ (λ x, (eq_tsub_iff_add_eq_of_le h).symm)

lemma coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι)
  (h : i ≤ n) : ((of _ i r * r') n : R) = r * r' (n - i) :=
coe_of_mul_apply_aux _ _ _ (λ x, by rw [eq_tsub_iff_add_eq_of_le h, add_comm])

lemma coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [decidable (i ≤ n)] :
  ((r * of _ i r') n : R) = if i ≤ n then r (n - i) * r' else 0 :=
by { split_ifs, exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h] }

lemma coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [decidable (i ≤ n)] :
  ((of _ i r * r') n : R) = if i ≤ n then r * r' (n - i) else 0 :=
by { split_ifs, exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h] }

end canonically_ordered_add_monoid

end direct_sum

/-! #### From `submodule`s -/

namespace submodule

/-- Build a `galgebra` instance for a collection of `submodule`s. -/
instance galgebra [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] :
  direct_sum.galgebra S (λ i, A i) :=
{ to_fun := ((algebra.linear_map S R).cod_restrict (A 0) $
    set_like.algebra_map_mem_graded A).to_add_monoid_hom,
  map_one := subtype.ext $ by exact (algebra_map S R).map_one,
  map_mul := λ x y, sigma.subtype_ext (add_zero 0).symm $ (algebra_map S R).map_mul _ _,
  commutes := λ r ⟨i, xi⟩,
    sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) $ algebra.commutes _ _,
  smul_def := λ r ⟨i, xi⟩, sigma.subtype_ext (zero_add i).symm $ algebra.smul_def _ _ }

@[simp] lemma set_like.coe_galgebra_to_fun [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] (s : S) :
    ↑(@direct_sum.galgebra.to_fun _ S (λ i, A i) _ _ _ _ _ _ _ s) = (algebra_map S R s : R) := rfl

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
instance nat_power_graded_monoid
  [comm_semiring S] [semiring R] [algebra S R] (p : submodule S R) :
  set_like.graded_monoid (λ i : ℕ, p ^ i) :=
{ one_mem := by { rw [←one_le, pow_zero], exact le_rfl },
  mul_mem := λ i j p q hp hq, by { rw pow_add, exact submodule.mul_mem_mul hp hq } }

end submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
def direct_sum.coe_alg_hom [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] : (⨁ i, A i) →ₐ[S] R :=
direct_sum.to_algebra S _ (λ i, (A i).subtype) rfl (λ _ _ _ _, rfl) (λ _, rfl)

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`direct_sum.coe_alg_hom`. -/
lemma submodule.supr_eq_to_submodule_range [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R] (A : ι → submodule S R) [set_like.graded_monoid A] :
  (⨆ i, A i) = (direct_sum.coe_alg_hom A).range.to_submodule :=
(submodule.supr_eq_range_dfinsupp_lsum A).trans $ set_like.coe_injective rfl

@[simp] lemma direct_sum.coe_alg_hom_of [add_monoid ι]
  [comm_semiring S] [semiring R] [algebra S R]
  (A : ι → submodule S R) [set_like.graded_monoid A] (i : ι) (x : A i) :
  direct_sum.coe_alg_hom A (direct_sum.of (λ i, A i) i x) = x :=
direct_sum.to_semiring_of _ rfl (λ _ _ _ _, rfl) _ _

end direct_sum

section homogeneous_element

lemma set_like.is_homogeneous_zero_submodule [has_zero ι]
  [semiring S] [add_comm_monoid R] [module S R]
  (A : ι → submodule S R) : set_like.is_homogeneous A (0 : R) :=
⟨0, submodule.zero_mem _⟩

lemma set_like.is_homogeneous.smul [comm_semiring S] [semiring R] [algebra S R]
  {A : ι → submodule S R} {s : S}
  {r : R} (hr : set_like.is_homogeneous A r) : set_like.is_homogeneous A (s • r) :=
let ⟨i, hi⟩ := hr in ⟨i, submodule.smul_mem _ _ hi⟩

end homogeneous_element

/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.direct_sum
import ring_theory.subsemiring

/-!
# The semiring structure on `⨁ i, M i` when `M i : submonoid S`

This module provides a typeclass `semiring_add_gradation M` that shows `M : ι → submonoid S` is an
additive gradation of `S`, such that:

* `1 ∈ M 0`
* `x ∈ M i → y ∈ M j → (x * y) ∈ M (i + j)`

When this typeclass is present, it imbues a `semiring` structure over `⨁ i, M i`.begin

If the `M i` are disjoint, this is a gradation of `⨆ i, M i : subsemiring S`. If
`i ≤ j → M i ≤ M j`, then this is filtration of `⨆ i, M i : subsemiring S`.

## tags

graded ring, filtered ring, direct sum, submonoid
-/

variables {S : Type*} [semiring S] {ι : Type*} [add_monoid ι] [decidable_eq ι]

namespace direct_sum

/-- A type class to indicate that multiplication is closed within `carriers` under addition of the
indices. -/
class semiring_add_gradation (carriers : ι → add_submonoid S) :=
(one_mem : (1 : S) ∈ carriers 0)
(mul_mem : ∀ {i j} (gi : carriers i) (gj : carriers j), (gi * gj : S) ∈ carriers (i + j))

variables (carriers : ι → add_submonoid S) [semiring_add_gradation carriers]

open_locale direct_sum

/-! The following lemmas begin with `h` to indicate that they are the heterogenous operators -/

/-! Multiplication is defined on the underlying semiring. -/
private def hmul {i j} : carriers i →+ carriers j →+ carriers (i + j) :=
{ to_fun := λ a,
  { to_fun := λ b, ⟨(a * b : S), semiring_add_gradation.mul_mem a b⟩,
    map_add' := λ _ _, subtype.ext (mul_add _ _ _),
    map_zero' := subtype.ext (mul_zero _), },
  map_add' := λ _ _, add_monoid_hom.ext $ λ _, subtype.ext (add_mul _ _ _),
  map_zero' := add_monoid_hom.ext $ λ _, subtype.ext (zero_mul _) }

/-! One is defined on the underlying semiring. -/
private def hone : carriers 0 := ⟨1, semiring_add_gradation.one_mem⟩

/-! We write the equalities as equalities of sigma types, as these contain more information than
`heq`; `(xi : carriers i) == (xj : carriers j)` does not tell us that `i = j`. -/

private lemma hone_hmul {i} (a : carriers i) :
  (⟨_, hmul carriers (hone carriers) a⟩ : Σ i, carriers i) = ⟨i, a⟩ :=
begin
  have h := zero_add i,
  congr,
  exact h,
  rw subtype.heq_iff_coe_eq,
  { exact one_mul _ },
  { exact λ x, h.symm ▸ iff.rfl, }
end

private lemma hmul_hone {i} (a : carriers i) :
  (⟨_, hmul carriers a (hone carriers)⟩ : Σ i, carriers i) = ⟨_, a⟩ :=
begin
  have h := add_zero i,
  congr,
  exact h,
  rw subtype.heq_iff_coe_eq,
  exact mul_one _,
  exact λ x, h.symm ▸ iff.rfl,
end

private lemma hmul_assoc {i j k} (a : carriers i) (b : carriers j) (c : carriers k) :
  (⟨_, hmul carriers (hmul carriers a b) c⟩ : Σ i, carriers i) =
  ⟨_, hmul carriers a (hmul carriers b c)⟩ :=
begin
  have h := add_assoc i j k,
  congr,
  exact h,
  rw subtype.heq_iff_coe_eq,
  exact mul_assoc _ _ _,
  exact λ x, h.symm ▸ iff.rfl,
end

/-! Embed the heterogenous definitions above into `direct_sum`  -/

instance : has_one (⨁ i, carriers i) :=
{ one := direct_sum.of (λ i, carriers i) 0 (hone carriers)}

instance : has_mul (⨁ i, carriers i) :=
{ mul := λ a b, begin
    -- the elaborator struggles here, so use tactics to assemble the expression
    refine direct_sum.to_add_monoid (λ j,
      direct_sum.to_add_monoid (λ i,
        (add_monoid_hom.comp_hom (direct_sum.of (λ k, carriers k) $ i + j)).comp _
      ) a
    ) b,
    exact hmul carriers,
  end }

/-! The various semiring fields are proved separately because the proofs are slow. -/

private lemma one_mul (x : ⨁ i, carriers i) : 1 * x = x :=
begin
  unfold has_one.one has_mul.mul,
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  convert add_monoid_hom.congr_fun (dfinsupp.sum_add_hom_single_add_hom) x,
  ext1 i, ext1 xi,
  exact dfinsupp.single_eq_of_sigma_eq (hone_hmul _ xi),
end

private lemma mul_one (x : ⨁ i, carriers i) : x * 1 = x :=
begin
  unfold has_one.one has_mul.mul,
  simp only [add_monoid_hom.coe_mk, to_add_monoid_of, add_monoid_hom.comp_hom_apply_apply],
  simp only [direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply, direct_sum.of],
  rw add_monoid_hom.dfinsupp_sum_add_hom_apply x _,
  convert add_monoid_hom.congr_fun (dfinsupp.sum_add_hom_single_add_hom ) x,
  ext1 i, ext1 xi,
  simp [dfinsupp.single_eq_of_sigma_eq (hmul_hone _ xi)],
end

private lemma mul_assoc (a b c : ⨁ i, carriers i) : a * b * c = a * (b * c) :=
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

  simp [dfinsupp.single_eq_of_sigma_eq (hmul_assoc _ ax bx cx)],
end

private lemma zero_mul (x : ⨁ i, carriers i) : 0 * x = 0 :=
by { unfold has_mul.mul, simp [direct_sum.to_add_monoid, direct_sum.of], }

private lemma mul_zero (x : ⨁ i, carriers i) : x * 0 = 0 :=
by { unfold has_mul.mul, simp, }

private lemma left_distrib (a b c : ⨁ i, carriers i) : a * (b + c) = a * b + a * c :=
by { unfold has_mul.mul, simp, }

private lemma right_distrib (a b c : ⨁ i, carriers i) : (a + b) * c = a * c + b * c :=
by { unfold has_mul.mul, simp [direct_sum.to_add_monoid, direct_sum.of], }

/-- The ring structure on `⨁ i, carriers i` in the presence of `semiring_add_gradation carriers`.
-/
instance : semiring (⨁ i, carriers i) := {
  one := 1,
  mul := (*),
  zero := 0,
  add := (+),
  one_mul := one_mul carriers,
  mul_one := mul_one carriers,
  mul_assoc := mul_assoc carriers,
  zero_mul := zero_mul carriers,
  mul_zero := mul_zero carriers,
  left_distrib := left_distrib carriers,
  right_distrib := right_distrib carriers,
  ..direct_sum.add_comm_monoid _ _, }

end direct_sum

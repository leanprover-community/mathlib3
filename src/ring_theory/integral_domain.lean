/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/

import data.polynomial.ring_division
import group_theory.specific_groups.cyclic
import algebra.geom_sum

/-!
# Integral domains

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Assorted theorems about integral domains.

## Main theorems

* `is_cyclic_of_subgroup_is_domain`: A finite subgroup of the units of an integral domain is cyclic.
* `fintype.field_of_domain`: A finite integral domain is a field.

## TODO

Prove Wedderburn's little theorem, which shows that all finite division rings are actually fields.

## Tags

integral domain, finite integral domain, finite field
-/

section

open finset polynomial function
open_locale big_operators nat

section cancel_monoid_with_zero
-- There doesn't seem to be a better home for these right now
variables {M : Type*} [cancel_monoid_with_zero M] [finite M]

lemma mul_right_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : bijective (λ b, a * b) :=
finite.injective_iff_bijective.1 $ mul_right_injective₀ ha

lemma mul_left_bijective_of_finite₀ {a : M} (ha : a ≠ 0) : bijective (λ b, b * a) :=
finite.injective_iff_bijective.1 $ mul_left_injective₀ ha

/-- Every finite nontrivial cancel_monoid_with_zero is a group_with_zero. -/
def fintype.group_with_zero_of_cancel (M : Type*) [cancel_monoid_with_zero M] [decidable_eq M]
  [fintype M] [nontrivial M] : group_with_zero M :=
{ inv := λ a, if h : a = 0 then 0 else fintype.bij_inv (mul_right_bijective_of_finite₀ h) 1,
  mul_inv_cancel := λ a ha,
    by { simp [has_inv.inv, dif_neg ha], exact fintype.right_inverse_bij_inv _ _ },
  inv_zero := by { simp [has_inv.inv, dif_pos rfl] },
  ..‹nontrivial M›,
  ..‹cancel_monoid_with_zero M› }

lemma exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [comm_semiring R] [is_domain R]
  [gcd_monoid R] [unique Rˣ] {a b c : R} {n : ℕ} (cp : is_coprime a b) (h : a * b = c ^ n) :
  ∃ d : R, a = d ^ n :=
begin
  refine exists_eq_pow_of_mul_eq_pow (is_unit_of_dvd_one _ _) h,
  obtain ⟨x, y, hxy⟩ := cp,
  rw [← hxy],
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)
end

lemma finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [comm_semiring R] [is_domain R]
  [gcd_monoid R] [unique Rˣ] {n : ℕ} {c : R} {s : finset ι} {f : ι → R}
  (h : ∀ i j ∈ s, i ≠ j → is_coprime (f i) (f j))
  (hprod : ∏ i in s, f i = c ^ n) : ∀ i ∈ s, ∃ d : R, f i = d ^ n :=
begin
  classical,
  intros i hi,
  rw [← insert_erase hi, prod_insert (not_mem_erase i s)] at hprod,
  refine exists_eq_pow_of_mul_eq_pow_of_coprime
    (is_coprime.prod_right (λ j hj, h i hi j (erase_subset i s hj) (λ hij, _))) hprod,
  rw [hij] at hj,
  exact (s.not_mem_erase _) hj
end

end cancel_monoid_with_zero

variables {R : Type*} {G : Type*}

section ring

variables [ring R] [is_domain R] [fintype R]

/-- Every finite domain is a division ring.

TODO: Prove Wedderburn's little theorem,
which shows a finite domain is in fact commutative, hence a field. -/
def fintype.division_ring_of_is_domain (R : Type*) [ring R] [is_domain R] [decidable_eq R]
  [fintype R] : division_ring R :=
{ ..show group_with_zero R, from fintype.group_with_zero_of_cancel R,
  ..‹ring R› }

/-- Every finite commutative domain is a field.

TODO: Prove Wedderburn's little theorem, which shows a finite domain is automatically commutative,
dropping one assumption from this theorem. -/
def fintype.field_of_domain (R) [comm_ring R] [is_domain R] [decidable_eq R] [fintype R] :
  field R :=
{ .. fintype.group_with_zero_of_cancel R,
  .. ‹comm_ring R› }

lemma finite.is_field_of_domain (R) [comm_ring R] [is_domain R] [finite R] : is_field R :=
by { casesI nonempty_fintype R,
  exact @field.to_is_field R (@@fintype.field_of_domain R _ _ (classical.dec_eq R) _) }

end ring

variables [comm_ring R] [is_domain R] [group G]

lemma card_nth_roots_subgroup_units [fintype G] (f : G →* R) (hf : injective f) {n : ℕ} (hn : 0 < n)
  (g₀ : G) :
  ({g ∈ univ | g ^ n = g₀} : finset G).card ≤ (nth_roots n (f g₀)).card :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  refine le_trans _ (nth_roots n (f g₀)).to_finset_card_le,
  apply card_le_card_of_inj_on f,
  { intros g hg,
    rw [sep_def, mem_filter] at hg,
    rw [multiset.mem_to_finset, mem_nth_roots hn, ← f.map_pow, hg.2] },
  { intros, apply hf, assumption }
end

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
lemma is_cyclic_of_subgroup_is_domain [finite G] (f : G →* R) (hf : injective f) : is_cyclic G :=
begin
  classical,
  casesI nonempty_fintype G,
  apply is_cyclic_of_card_pow_eq_one_le,
  intros n hn,
  convert (le_trans (card_nth_roots_subgroup_units f hf hn 1) (card_nth_roots n (f 1)))
end

/-- The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this requires only
`finite Rˣ` rather than deducing it from `finite R`. -/
instance [finite Rˣ] : is_cyclic Rˣ :=
is_cyclic_of_subgroup_is_domain (units.coe_hom R) $ units.ext

section

variables (S : subgroup Rˣ) [finite S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
instance subgroup_units_cyclic : is_cyclic S :=
begin
  refine is_cyclic_of_subgroup_is_domain ⟨(coe : S → R), _, _⟩
    (units.ext.comp subtype.val_injective),
  { simp },
  { intros, simp },
end

end

section euclidean_division

namespace polynomial

open_locale polynomial

variables (K : Type) [field K] [algebra R[X] K] [is_fraction_ring R[X] K]

lemma div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.monic) :
  ∃ q r : R[X], r.degree < g.degree ∧ (↑f : K) / ↑g = ↑q + ↑r / ↑g :=
begin
  refine ⟨f /ₘ g, f %ₘ g, _, _⟩,
  { exact degree_mod_by_monic_lt _ hg },
  { have hg' : (↑g : K) ≠ 0 := by exact_mod_cast (monic.ne_zero hg),
    field_simp [hg'],
    norm_cast,
    rw [add_comm, mul_comm, mod_by_monic_add_div f hg] },
end

end polynomial

end euclidean_division

variables [fintype G]

lemma card_fiber_eq_of_mem_range {H : Type*} [group H] [decidable_eq H]
  (f : G →* H) {x y : H} (hx : x ∈ set.range f) (hy : y ∈ set.range f) :
  (univ.filter $ λ g, f g = x).card = (univ.filter $ λ g, f g = y).card :=
begin
  rcases hx with ⟨x, rfl⟩,
  rcases hy with ⟨y, rfl⟩,
  refine card_congr (λ g _, g * x⁻¹ * y) _ _ (λ g hg, ⟨g * y⁻¹ * x, _⟩),
  { simp only [mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, monoid_hom.map_mul_inv, and_self, forall_true_iff] {contextual := tt} },
  { simp only [mul_left_inj, imp_self, forall_2_true_iff], },
  { simp only [true_and, mem_filter, mem_univ] at hg,
    simp only [hg, mem_filter, one_mul, monoid_hom.map_mul, mem_univ, mul_right_inv,
      eq_self_iff_true, exists_prop_of_true, monoid_hom.map_mul_inv, and_self,
      mul_inv_cancel_right, inv_mul_cancel_right], }
end

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
lemma sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 :=
begin
  classical,
  obtain ⟨x, hx⟩ : ∃ x : monoid_hom.range f.to_hom_units,
    ∀ y : monoid_hom.range f.to_hom_units, y ∈ submonoid.powers x,
    from is_cyclic.exists_monoid_generator,
  have hx1 : x ≠ 1,
  { rintro rfl,
    apply hf,
    ext g,
    rw [monoid_hom.one_apply],
    cases hx ⟨f.to_hom_units g, g, rfl⟩ with n hn,
    rwa [subtype.ext_iff, units.ext_iff, subtype.coe_mk, monoid_hom.coe_to_hom_units,
      one_pow, eq_comm] at hn, },
  replace hx1 : (x : R) - 1 ≠ 0,
    from λ h, hx1 (subtype.eq (units.ext (sub_eq_zero.1 h))),
  let c := (univ.filter (λ g, f.to_hom_units g = 1)).card,
  calc ∑ g : G, f g
      = ∑ g : G, f.to_hom_units g : rfl
  ... = ∑ u : Rˣ in univ.image f.to_hom_units,
    (univ.filter (λ g, f.to_hom_units g = u)).card • u : sum_comp (coe : Rˣ → R) f.to_hom_units
  ... = ∑ u : Rˣ in univ.image f.to_hom_units, c • u :
    sum_congr rfl (λ u hu, congr_arg2 _ _ rfl) -- remaining goal 1, proven below
  ... = ∑ b : monoid_hom.range f.to_hom_units, c • ↑b : finset.sum_subtype _
      (by simp ) _
  ... = c • ∑ b : monoid_hom.range f.to_hom_units, (b : R) : smul_sum.symm
  ... = c • 0 : congr_arg2 _ rfl _            -- remaining goal 2, proven below
  ... = 0 : smul_zero _,
  { -- remaining goal 1
    show (univ.filter (λ (g : G), f.to_hom_units g = u)).card = c,
    apply card_fiber_eq_of_mem_range f.to_hom_units,
    { simpa only [mem_image, mem_univ, exists_prop_of_true, set.mem_range] using hu, },
    { exact ⟨1, f.to_hom_units.map_one⟩ } },
  -- remaining goal 2
  show ∑ b : monoid_hom.range f.to_hom_units, (b : R) = 0,
  calc ∑ b : monoid_hom.range f.to_hom_units, (b : R)
      = ∑ n in range (order_of x), x ^ n :
    eq.symm $ sum_bij (λ n _, x ^ n)
      (by simp only [mem_univ, forall_true_iff])
      (by simp only [implies_true_iff, eq_self_iff_true, subgroup.coe_pow, units.coe_pow, coe_coe])
      (λ m n hm hn, pow_injective_of_lt_order_of _
        (by simpa only [mem_range] using hm)
        (by simpa only [mem_range] using hn))
      (λ b hb, let ⟨n, hn⟩ := hx b in ⟨n % order_of x, mem_range.2 (nat.mod_lt _ (order_of_pos _)),
        by rw [← pow_eq_mod_order_of, hn]⟩)
  ... = 0 : _,
  rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul, coe_coe],
  norm_cast,
  simp [pow_order_of_eq_one],
end

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
lemma sum_hom_units (f : G →* R) [decidable (f = 1)] :
  ∑ g : G, f g = if f = 1 then fintype.card G else 0 :=
begin
  split_ifs with h h,
  { simp [h, card_univ] },
  { exact sum_hom_units_eq_zero f h }
end

end

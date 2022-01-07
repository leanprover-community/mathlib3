/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import ring_theory.hahn_series
import ring_theory.localization

/-!
# Laurent Series

## Main Definitions
* Defines `laurent_series` as an abbreviation for `hahn_series ℤ`.
* Provides a coercion `power_series R` into `laurent_series R` given by
  `hahn_series.of_power_series`.
* Defines `laurent_series.power_series_part`
* Defines the localization map `laurent_series.of_power_series_localization` which evaluates to
  `hahn_series.of_power_series`.

-/

open hahn_series
open_locale big_operators classical
noncomputable theory

universe u

/-- A `laurent_series` is implemented as a `hahn_series` with value group `ℤ`. -/
abbreviation laurent_series (R : Type*) [has_zero R] := hahn_series ℤ R

variables {R : Type u}

namespace laurent_series

section semiring
variable [semiring R]

instance : has_coe (power_series R) (laurent_series R) :=
⟨hahn_series.of_power_series ℤ R⟩

lemma coe_power_series (x : power_series R) : (x : laurent_series R) =
  hahn_series.of_power_series ℤ R x := rfl

@[simp] lemma coeff_coe_power_series (x : power_series R) (n : ℕ) :
  hahn_series.coeff (x : laurent_series R) n = power_series.coeff R n x :=
by rw [← int.nat_cast_eq_coe_nat, coe_power_series, of_power_series_apply_coeff]

/-- This is a power series that can be multiplied by an integer power of `X` to give our
  Laurent series. If the Laurent series is nonzero, `power_series_part` has a nonzero
  constant term.  -/
def power_series_part (x : laurent_series R) : power_series R :=
power_series.mk (λ n, x.coeff (x.order + n))

@[simp] lemma power_series_part_coeff (x : laurent_series R) (n : ℕ) :
  power_series.coeff R n x.power_series_part = x.coeff (x.order + n) :=
power_series.coeff_mk _ _

@[simp] lemma power_series_part_zero : power_series_part (0 : laurent_series R) = 0 :=
by { ext, simp }

@[simp] lemma power_series_part_eq_zero (x : laurent_series R) :
  x.power_series_part = 0 ↔ x = 0 :=
begin
  split,
  { contrapose!,
    intro h,
    rw [power_series.ext_iff, not_forall],
    refine ⟨0, _⟩,
    simp [coeff_order_ne_zero h] },
  { rintro rfl,
    simp }
end

@[simp] lemma single_order_mul_power_series_part (x : laurent_series R) :
  (single x.order 1 : laurent_series R) * x.power_series_part = x :=
begin
  ext n,
  rw [← sub_add_cancel n x.order, single_mul_coeff_add, sub_add_cancel, one_mul],
  by_cases h : x.order ≤ n,
  { rw [int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h), coeff_coe_power_series,
      power_series_part_coeff, ← int.eq_nat_abs_of_zero_le (sub_nonneg_of_le h),
      add_sub_cancel'_right] },
  { rw [coe_power_series, of_power_series_apply, emb_domain_notin_range],
    { contrapose! h,
      exact order_le_of_coeff_ne_zero h.symm },
    { contrapose! h,
      simp only [set.mem_range, rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk,
        int.nat_cast_eq_coe_nat] at h,
      obtain ⟨m, hm⟩ := h,
      rw [← sub_nonneg, ← hm],
      exact int.zero_le_of_nat _ } }
end

lemma of_power_series_power_series_part (x : laurent_series R) :
  of_power_series ℤ R x.power_series_part = single (-x.order) 1 * x :=
begin
  refine eq.trans _ (congr rfl x.single_order_mul_power_series_part),
  rw [← mul_assoc, single_mul_single, neg_add_self, mul_one, ← C_apply, C_one, one_mul,
    coe_power_series],
end

end semiring

instance [comm_semiring R] : algebra (power_series R) (laurent_series R) :=
(hahn_series.of_power_series ℤ R).to_algebra

@[simp] lemma coe_algebra_map [comm_semiring R] :
  ⇑(algebra_map (power_series R) (laurent_series R)) = hahn_series.of_power_series ℤ R :=
rfl

/-- The localization map from power series to Laurent series. -/
@[simps] instance of_power_series_localization [comm_ring R] :
  is_localization (submonoid.powers (power_series.X : power_series R)) (laurent_series R) :=
{ map_units := (begin rintro ⟨_, n, rfl⟩,
    refine ⟨⟨single (n : ℤ) 1, single (-n : ℤ) 1, _, _⟩, _⟩,
    { simp only [single_mul_single, mul_one, add_right_neg],
      refl },
    { simp only [single_mul_single, mul_one, add_left_neg],
      refl },
    { simp } end),
 surj := (begin intro z,
    by_cases h : 0 ≤ z.order,
    { refine ⟨⟨power_series.X ^ (int.nat_abs z.order) * power_series_part z, 1⟩, _⟩,
      simp only [ring_hom.map_one, mul_one, ring_hom.map_mul, coe_algebra_map,
        of_power_series_X_pow, submonoid.coe_one, int.nat_cast_eq_coe_nat],
      rw [int.nat_abs_of_nonneg h, ← coe_power_series, single_order_mul_power_series_part] },
    { refine ⟨⟨power_series_part z, power_series.X ^ (int.nat_abs z.order), ⟨_, rfl⟩⟩, _⟩,
      simp only [coe_algebra_map, of_power_series_power_series_part],
      rw [mul_comm _ z],
      refine congr rfl _,
      rw [subtype.coe_mk, of_power_series_X_pow,
          int.nat_cast_eq_coe_nat, int.of_nat_nat_abs_of_nonpos],
      exact le_of_not_ge h } end),
  eq_iff_exists := (begin intros x y,
    rw [coe_algebra_map, of_power_series_injective.eq_iff],
    split,
    { rintro rfl,
      exact ⟨1, rfl⟩ },
    { rintro ⟨⟨_, n, rfl⟩, hc⟩,
      rw [← sub_eq_zero, ← sub_mul, power_series.ext_iff] at hc,
      rw [← sub_eq_zero, power_series.ext_iff],
      intro m,
      have h := hc (m + n),
      rw [linear_map.map_zero, subtype.coe_mk, power_series.X_pow_eq, power_series.monomial,
        power_series.coeff, finsupp.single_add, mv_power_series.coeff_add_mul_monomial,
        mul_one] at h,
      exact h } end) }

instance {K : Type u} [field K] : is_fraction_ring (power_series K) (laurent_series K) :=
is_localization.of_le (submonoid.powers (power_series.X : power_series K)) _
  (powers_le_non_zero_divisors_of_no_zero_divisors power_series.X_ne_zero)
  (λ f hf, is_unit_of_mem_non_zero_divisors $ ring_hom.map_mem_non_zero_divisors _
    hahn_series.of_power_series_injective hf)

end laurent_series

namespace polynomial

section laurent_series

variables [comm_semiring R] (p q : polynomial R)

open laurent_series hahn_series

lemma coe_laurent : (p : laurent_series R) = of_power_series ℤ R p := rfl

@[norm_cast] lemma coe_coe : ((p : power_series R) : laurent_series R) = p := rfl

@[simp] lemma coe_laurent_zero : ((0 : polynomial R) : laurent_series R) = 0 :=
by rw [coe_laurent, ←coe_to_power_series.ring_hom_apply, ←ring_hom.comp_apply, _root_.map_zero]

@[simp] lemma coe_laurent_one : ((1 : polynomial R) : laurent_series R) = 1 :=
by rw [coe_laurent, ←coe_to_power_series.ring_hom_apply, ←ring_hom.comp_apply, _root_.map_one]

@[simp, norm_cast] lemma coe_laurent_add : ((p + q : polynomial R) : laurent_series R) = p + q :=
by simp_rw [coe_laurent, ←coe_to_power_series.ring_hom_apply, ←ring_hom.comp_apply, _root_.map_add]

@[simp, norm_cast] lemma coe_laurent_mul : ((p * q : polynomial R) : laurent_series R) = p * q :=
by simp_rw [coe_laurent, ←coe_to_power_series.ring_hom_apply, ←ring_hom.comp_apply, _root_.map_mul]

@[norm_cast] lemma coeff_coe_laurent_coe (i : ℕ) :
  ((p : polynomial R) : laurent_series R).coeff i = p.coeff i :=
by rw [←coe_coe, coeff_coe_power_series, coeff_coe]

lemma coeff_coe_laurent (i : ℤ) :
  ((p : polynomial R) : laurent_series R).coeff i = if i < 0 then 0 else p.coeff i.nat_abs :=
begin
  cases i,
  { rw [int.nat_abs_of_nat_core, int.of_nat_eq_coe, coeff_coe_laurent_coe,
        if_neg (int.coe_nat_nonneg _).not_lt] },
  { rw [coe_laurent, of_power_series_apply, emb_domain_notin_image_support,
        if_pos (int.neg_succ_lt_zero _)],
    simp only [not_exists, rel_embedding.coe_fn_mk, set.mem_image, not_and, coeff_coe,
               function.embedding.coe_fn_mk, ne.def, to_power_series_symm_apply_coeff, mem_support,
               int.nat_cast_eq_coe_nat, int.coe_nat_eq, implies_true_iff, not_false_iff] }
end

@[simp] lemma coe_laurent_C (r : R) : ((C r : polynomial R) : laurent_series R) = hahn_series.C r :=
by rw [coe_laurent, coe_C, of_power_series_C]

@[simp] lemma coe_laurent_X : ((X : polynomial R) : laurent_series R) = single 1 1 :=
by rw [coe_laurent, coe_X, of_power_series_X]

@[simp, norm_cast] lemma coe_laurent_smul (r : R) :
  ((r • p : polynomial R) : laurent_series R) = r • p :=
by rw [smul_eq_C_mul, coe_laurent_mul, coe_laurent_C, C_mul_eq_smul]

end laurent_series

end polynomial

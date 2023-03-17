/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.algebra.basic
import algebra.indicator_function
import data.rat.nnrat.defs

/-!
# Algebraic structures on the nonnegative rationals

This file provides additional results about `nnrat` that could not

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/

open function
open_locale nnrat

namespace nnrat
variables {α : Type*} {p q : ℚ≥0}

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ := rfl
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl

@[simp] lemma to_nnrat_coe (q : ℚ≥0) : to_nnrat q = q := ext $ max_eq_left q.2

@[simp] lemma to_nnrat_coe_nat (n : ℕ) : to_nnrat n = n := ext $ by simp [rat.coe_to_nnrat]

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : algebra ℚ≥0 ℚ := coe_hom.to_algebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [mul_action ℚ α] : mul_action ℚ≥0 α := mul_action.comp_hom α coe_hom.to_monoid_hom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [add_comm_monoid α] [distrib_mul_action ℚ α] : distrib_mul_action ℚ≥0 α :=
distrib_mul_action.comp_hom α coe_hom.to_monoid_hom

-- /-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
-- instance [add_comm_monoid α] [module ℚ α] : module ℚ≥0 α := module.comp_hom α coe_hom

-- @[simp, norm_cast] lemma coe_indicator (s : set α) (f : α → ℚ≥0) (a : α) :
--   ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (λ x, f x) a :=
-- (coe_hom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = q ^ n := coe_hom.map_pow _ _

@[norm_cast] lemma coe_list_sum (l : list ℚ≥0) : (l.sum : ℚ) = (l.map coe).sum :=
coe_hom.map_list_sum _

@[norm_cast] lemma coe_list_prod (l : list ℚ≥0) : (l.prod : ℚ) = (l.map coe).prod :=
coe_hom.map_list_prod _

@[norm_cast] lemma coe_multiset_sum (s : multiset ℚ≥0) : (s.sum : ℚ) = (s.map coe).sum :=
coe_hom.map_multiset_sum _

@[norm_cast] lemma coe_multiset_prod (s : multiset ℚ≥0) : (s.prod : ℚ) = (s.map coe).prod :=
coe_hom.map_multiset_prod _

-- @[norm_cast] lemma coe_sum {s : finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
-- coe_hom.map_sum _ _

-- lemma to_nnrat_sum_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
--   (∑ a in s, f a).to_nnrat = ∑ a in s, (f a).to_nnrat :=
-- begin
--   rw [←coe_inj, coe_sum, rat.coe_to_nnrat _ (finset.sum_nonneg hf)],
--   exact finset.sum_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
-- end

-- @[norm_cast] lemma coe_prod {s : finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
-- coe_hom.map_prod _ _

-- lemma to_nnrat_prod_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
--   (∏ a in s, f a).to_nnrat = ∏ a in s, (f a).to_nnrat :=
-- begin
--   rw [←coe_inj, coe_prod, rat.coe_to_nnrat _ (finset.prod_nonneg hf)],
--   exact finset.prod_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
-- end

-- @[norm_cast] lemma nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
-- coe_hom.to_add_monoid_hom.map_nsmul _ _

lemma bdd_above_coe {s : set ℚ≥0} : bdd_above (coe '' s : set ℚ) ↔ bdd_above s :=
⟨λ ⟨b, hb⟩, ⟨to_nnrat b, λ ⟨y, hy⟩ hys, show y ≤ max b 0, from
    (hb $ set.mem_image_of_mem _ hys).trans $ le_max_left _ _⟩,
  λ ⟨b, hb⟩, ⟨b, λ y ⟨x, hx, eq⟩, eq ▸ hb hx⟩⟩

lemma bdd_below_coe (s : set ℚ≥0) : bdd_below ((coe : ℚ≥0 → ℚ) '' s) := ⟨0, λ r ⟨q, _, h⟩, h ▸ q.2⟩

lemma sub_def (p q : ℚ≥0) : p - q = to_nnrat (p - q) := rfl

@[simp] lemma abs_coe (q : ℚ≥0) : |(q : ℚ)| = q := abs_of_nonneg q.2

end nnrat

open nnrat

namespace rat
variables {p q : ℚ}

@[simp] lemma to_nnrat_zero : to_nnrat 0 = 0 := by simp [to_nnrat]; refl
@[simp] lemma to_nnrat_one : to_nnrat 1 = 1 := by simp [to_nnrat, max_eq_left zero_le_one]

@[simp] lemma to_nnrat_pos : 0 < to_nnrat q ↔ 0 < q := by simp [to_nnrat, ←coe_lt_coe]

@[simp] lemma to_nnrat_eq_zero : to_nnrat q = 0 ↔ q ≤ 0 :=
by simpa [-to_nnrat_pos] using (@to_nnrat_pos q).not

alias to_nnrat_eq_zero ↔ _ to_nnrat_of_nonpos

@[simp] lemma to_nnrat_le_to_nnrat_iff (hp : 0 ≤ p) : to_nnrat q ≤ to_nnrat p ↔ q ≤ p :=
by simp [←coe_le_coe, to_nnrat, hp]

@[simp] lemma to_nnrat_lt_to_nnrat_iff' : to_nnrat q < to_nnrat p ↔ q < p ∧ 0 < p :=
by { simp [←coe_lt_coe, to_nnrat, lt_irrefl], exact lt_trans' }

lemma to_nnrat_lt_to_nnrat_iff (h : 0 < p) : to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans (and_iff_left h)

lemma to_nnrat_lt_to_nnrat_iff_of_nonneg (hq : 0 ≤ q) : to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans ⟨and.left, λ h, ⟨h, hq.trans_lt h⟩⟩

@[simp] lemma to_nnrat_add (hq : 0 ≤ q) (hp : 0 ≤ p) : to_nnrat (q + p) = to_nnrat q + to_nnrat p :=
nnrat.ext $ by simp [to_nnrat, hq, hp, add_nonneg]

lemma to_nnrat_add_le : to_nnrat (q + p) ≤ to_nnrat q + to_nnrat p :=
coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) $ coe_nonneg _

lemma to_nnrat_le_iff_le_coe {p : ℚ≥0} : to_nnrat q ≤ p ↔ q ≤ ↑p := nnrat.gi.gc q p

lemma le_to_nnrat_iff_coe_le {q : ℚ≥0} (hp : 0 ≤ p) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
by rw [←coe_le_coe, rat.coe_to_nnrat p hp]

-- lemma le_to_nnrat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
-- (le_or_lt 0 p).elim le_to_nnrat_iff_coe_le $ λ hp,
--   by simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]

lemma to_nnrat_lt_iff_lt_coe {p : ℚ≥0} (hq : 0 ≤ q) : to_nnrat q < p ↔ q < ↑p :=
by rw [←coe_lt_coe, rat.coe_to_nnrat q hq]

lemma lt_to_nnrat_iff_coe_lt {q : ℚ≥0} : q < to_nnrat p ↔ ↑q < p := nnrat.gi.gc.lt_iff_lt

@[simp] lemma to_nnrat_bit0 (hq : 0 ≤ q) : to_nnrat (bit0 q) = bit0 (to_nnrat q) :=
to_nnrat_add hq hq

@[simp] lemma to_nnrat_bit1 (hq : 0 ≤ q) : to_nnrat (bit1 q) = bit1 (to_nnrat q) :=
(to_nnrat_add (by simp [hq]) zero_le_one).trans $ by simp [to_nnrat_one, bit1, hq]

lemma to_nnrat_mul (hp : 0 ≤ p) : to_nnrat (p * q) = to_nnrat p * to_nnrat q :=
begin
  cases le_total 0 q with hq hq,
  { ext; simp [to_nnrat, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, mul_zero] }
end

lemma to_nnrat_inv (q : ℚ) : to_nnrat q⁻¹ = (to_nnrat q)⁻¹ :=
begin
  obtain hq | hq := le_total q 0,
  { rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)] },
  { nth_rewrite 0 ←rat.coe_to_nnrat q hq,
    rw [←coe_inv, to_nnrat_coe] }
end

-- lemma to_nnrat_div (hp : 0 ≤ p) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
-- by rw [div_eq_mul_inv, div_eq_mul_inv, ←to_nnrat_inv, ←to_nnrat_mul hp]

-- lemma to_nnrat_div' (hq : 0 ≤ q) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
-- by rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]

end rat

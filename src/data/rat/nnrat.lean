/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.algebra.basic
import algebra.order.nonneg.field

/-!
# Nonnegative rationals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the nonnegative rationals as a subtype of `rat` and provides its algebraic order
structure.

We also define an instance `can_lift ℚ ℚ≥0`. This instance can be used by the `lift` tactic to
replace `x : ℚ` and `hx : 0 ≤ x` in the proof context with `x : ℚ≥0` while replacing all occurences
of `x` with `↑x`. This tactic also works for a function `f : α → ℚ` with a hypothesis
`hf : ∀ x, 0 ≤ f x`.

## Notation

`ℚ≥0` is notation for `nnrat` in locale `nnrat`.
-/

open function
open_locale big_operators

/-- Nonnegative rational numbers. -/
@[derive [canonically_ordered_comm_semiring, canonically_linear_ordered_semifield,
  linear_ordered_comm_group_with_zero, has_sub, has_ordered_sub,
  densely_ordered, archimedean, inhabited]]
def nnrat := {q : ℚ // 0 ≤ q}

localized "notation (name := nnrat) `ℚ≥0` := nnrat" in nnrat

namespace nnrat
variables {α : Type*} {p q : ℚ≥0}

instance : has_coe ℚ≥0 ℚ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (q : ℚ≥0) : q.val = q := rfl

instance can_lift : can_lift ℚ ℚ≥0 coe (λ q, 0 ≤ q) :=
{ prf := λ q hq, ⟨⟨q, hq⟩, rfl⟩ }

@[ext] lemma ext : (p : ℚ) = (q : ℚ) → p = q := subtype.ext

protected lemma coe_injective : injective (coe : ℚ≥0 → ℚ) := subtype.coe_injective

@[simp, norm_cast] lemma coe_inj : (p : ℚ) = q ↔ p = q := subtype.coe_inj

lemma ext_iff : p = q ↔ (p : ℚ) = q := subtype.ext_iff

lemma ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y := nnrat.coe_inj.not

@[norm_cast] lemma coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q := rfl

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.rat.to_nnrat (q : ℚ) : ℚ≥0 := ⟨max q 0, le_max_right _ _⟩

lemma _root_.rat.coe_to_nnrat (q : ℚ) (hq : 0 ≤ q) : (q.to_nnrat : ℚ) = q := max_eq_left hq

lemma _root_.rat.le_coe_to_nnrat (q : ℚ) : q ≤ q.to_nnrat := le_max_left _ _

open _root_.rat (to_nnrat)

@[simp] lemma coe_nonneg (q : ℚ≥0) : (0 : ℚ) ≤ q := q.2

@[simp, norm_cast] lemma coe_zero : ((0 : ℚ≥0) : ℚ) = 0 := rfl
@[simp, norm_cast] lemma coe_one  : ((1 : ℚ≥0) : ℚ) = 1 := rfl
@[simp, norm_cast] lemma coe_add (p q : ℚ≥0) : ((p + q : ℚ≥0) : ℚ) = p + q := rfl
@[simp, norm_cast] lemma coe_mul (p q : ℚ≥0) : ((p * q : ℚ≥0) : ℚ) = p * q := rfl
@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ := rfl
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl
@[simp, norm_cast] lemma coe_bit0 (q : ℚ≥0) : ((bit0 q : ℚ≥0) : ℚ) = bit0 q := rfl
@[simp, norm_cast] lemma coe_bit1 (q : ℚ≥0) : ((bit1 q : ℚ≥0) : ℚ) = bit1 q := rfl
@[simp, norm_cast] lemma coe_sub (h : q ≤ p) : ((p - q : ℚ≥0) : ℚ) = p - q :=
max_eq_left $ le_sub_comm.2 $ by simp [show (q : ℚ) ≤ p, from h]

@[simp] lemma coe_eq_zero : (q : ℚ) = 0 ↔ q = 0 := by norm_cast
lemma coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 := coe_eq_zero.not

@[simp, norm_cast] lemma coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q := iff.rfl
@[simp, norm_cast] lemma coe_lt_coe : (p : ℚ) < q ↔ p < q := iff.rfl
@[simp, norm_cast] lemma coe_pos : (0 : ℚ) < q ↔ 0 < q := iff.rfl

lemma coe_mono : monotone (coe : ℚ≥0 → ℚ) := λ _ _, coe_le_coe.2

lemma to_nnrat_mono : monotone to_nnrat := λ x y h, max_le_max h le_rfl

@[simp] lemma to_nnrat_coe (q : ℚ≥0) : to_nnrat q = q := ext $ max_eq_left q.2

@[simp] lemma to_nnrat_coe_nat (n : ℕ) : to_nnrat n = n :=
ext $ by simp [rat.coe_to_nnrat]

/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : galois_insertion to_nnrat coe :=
galois_insertion.monotone_intro coe_mono to_nnrat_mono rat.le_coe_to_nnrat to_nnrat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def coe_hom : ℚ≥0 →+* ℚ := ⟨coe, coe_one, coe_mul, coe_zero, coe_add⟩

@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n := map_nat_cast coe_hom n

@[simp] lemma mk_coe_nat (n : ℕ) : @eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
ext (coe_nat_cast n).symm

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : algebra ℚ≥0 ℚ := coe_hom.to_algebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [mul_action ℚ α] : mul_action ℚ≥0 α := mul_action.comp_hom α coe_hom.to_monoid_hom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [add_comm_monoid α] [distrib_mul_action ℚ α] : distrib_mul_action ℚ≥0 α :=
distrib_mul_action.comp_hom α coe_hom.to_monoid_hom

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [add_comm_monoid α] [module ℚ α] : module ℚ≥0 α := module.comp_hom α coe_hom

@[simp] lemma coe_coe_hom : ⇑coe_hom = coe := rfl

@[simp, norm_cast] lemma coe_indicator (s : set α) (f : α → ℚ≥0) (a : α) :
  ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (λ x, f x) a :=
(coe_hom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : (↑(q ^ n) : ℚ) = q ^ n := coe_hom.map_pow _ _

@[norm_cast] lemma coe_list_sum (l : list ℚ≥0) : (l.sum : ℚ) = (l.map coe).sum :=
coe_hom.map_list_sum _

@[norm_cast] lemma coe_list_prod (l : list ℚ≥0) : (l.prod : ℚ) = (l.map coe).prod :=
coe_hom.map_list_prod _

@[norm_cast] lemma coe_multiset_sum (s : multiset ℚ≥0) : (s.sum : ℚ) = (s.map coe).sum :=
coe_hom.map_multiset_sum _

@[norm_cast] lemma coe_multiset_prod (s : multiset ℚ≥0) : (s.prod : ℚ) = (s.map coe).prod :=
coe_hom.map_multiset_prod _

@[norm_cast] lemma coe_sum {s : finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
coe_hom.map_sum _ _

lemma to_nnrat_sum_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  (∑ a in s, f a).to_nnrat = ∑ a in s, (f a).to_nnrat :=
begin
  rw [←coe_inj, coe_sum, rat.coe_to_nnrat _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {s : finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
coe_hom.map_prod _ _

lemma to_nnrat_prod_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
  (∏ a in s, f a).to_nnrat = ∏ a in s, (f a).to_nnrat :=
begin
  rw [←coe_inj, coe_prod, rat.coe_to_nnrat _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

@[norm_cast] lemma nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
coe_hom.to_add_monoid_hom.map_nsmul _ _

lemma bdd_above_coe {s : set ℚ≥0} : bdd_above (coe '' s : set ℚ) ↔ bdd_above s :=
⟨λ ⟨b, hb⟩, ⟨to_nnrat b, λ ⟨y, hy⟩ hys, show y ≤ max b 0, from
    (hb $ set.mem_image_of_mem _ hys).trans $ le_max_left _ _⟩,
  λ ⟨b, hb⟩, ⟨b, λ y ⟨x, hx, eq⟩, eq ▸ hb hx⟩⟩

lemma bdd_below_coe (s : set ℚ≥0) : bdd_below ((coe : ℚ≥0 → ℚ) '' s) := ⟨0, λ r ⟨q, _, h⟩, h ▸ q.2⟩

@[simp, norm_cast] lemma coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
coe_mono.map_max

@[simp, norm_cast] lemma coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
coe_mono.map_min

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

lemma le_to_nnrat_iff_coe_le' {q : ℚ≥0} (hq : 0 < q) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
(le_or_lt 0 p).elim le_to_nnrat_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hq.not_le]

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

lemma to_nnrat_div (hp : 0 ≤ p) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←to_nnrat_inv, ←to_nnrat_mul hp]

lemma to_nnrat_div' (hq : 0 ≤ q) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
by rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]

end rat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot] def rat.nnabs (x : ℚ) : ℚ≥0 := ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp] lemma rat.coe_nnabs (x : ℚ) : (rat.nnabs x : ℚ) = abs x := by simp [rat.nnabs]

/-! ### Numerator and denominator -/

namespace nnrat
variables {p q : ℚ≥0}

/-- The numerator of a nonnegative rational. -/
def num (q : ℚ≥0) : ℕ := (q : ℚ).num.nat_abs

/-- The denominator of a nonnegative rational. -/
def denom (q : ℚ≥0) : ℕ := (q : ℚ).denom

@[simp] lemma nat_abs_num_coe : (q : ℚ).num.nat_abs = q.num := rfl
@[simp] lemma denom_coe : (q : ℚ).denom = q.denom := rfl

lemma ext_num_denom (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
ext $ rat.ext ((int.nat_abs_inj_of_nonneg_of_nonneg
  (rat.num_nonneg_iff_zero_le.2 p.2) $ rat.num_nonneg_iff_zero_le.2 q.2).1 hn) hd

lemma ext_num_denom_iff : p = q ↔ p.num = q.num ∧ p.denom = q.denom :=
⟨by { rintro rfl, exact ⟨rfl, rfl⟩ }, λ h, ext_num_denom h.1 h.2⟩

@[simp] lemma num_div_denom (q : ℚ≥0) : (q.num : ℚ≥0) / q.denom = q :=
begin
  ext1,
  rw [coe_div, coe_nat_cast, coe_nat_cast, num, ←int.cast_coe_nat,
    int.nat_abs_of_nonneg (rat.num_nonneg_iff_zero_le.2 q.prop)],
  exact rat.num_div_denom q,
end

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*} (h : Π m n : ℕ, α (m / n)) (q : ℚ≥0) : α q :=
(num_div_denom _).rec (h _ _)

end nnrat

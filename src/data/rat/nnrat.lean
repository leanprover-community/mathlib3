/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.algebra.basic
import algebra.big_operators.order
import algebra.indicator_function
import algebra.order.nonneg

/-!
# Nonnegative rationals
-/

section
variables {α : Type*} [canonically_ordered_add_monoid α] {a b c : α}

lemma le_of_add_le_left : a + b ≤ c → a ≤ c := le_self_add.trans
lemma le_of_add_le_right : a + b ≤ c → b ≤ c := le_add_self.trans

end

open function
open_locale big_operators

/-- Nonnegative rational numbers. -/
@[derive [canonically_ordered_comm_semiring, canonically_linear_ordered_add_monoid,
  linear_ordered_comm_group_with_zero, linear_ordered_semiring, has_sub, has_ordered_sub,
  densely_ordered, archimedean, inhabited]]
def nnrat := {q : ℚ // 0 ≤ q}

localized "notation ` ℚ≥0 ` := nnrat" in nnrat

variables {α : Type*} {p q : ℚ≥0}

namespace nnrat

instance : has_coe ℚ≥0 ℚ := ⟨subtype.val⟩

/- Simp lemma to put back `n.val` into the normal form given by the coercion. -/
@[simp] lemma val_eq_coe (q : ℚ≥0) : q.val = q := rfl

instance : can_lift ℚ ℚ≥0 :=
{ coe := coe,
  cond := λ q, 0 ≤ q,
  prf := λ q hq, ⟨⟨q, hq⟩, rfl⟩ }

@[ext] lemma ext : (p : ℚ) = (q : ℚ) → p = q := subtype.ext

protected lemma coe_injective : injective (coe : ℚ≥0 → ℚ) := subtype.coe_injective

@[simp, norm_cast] lemma coe_inj : (p : ℚ) = q ↔ p = q := subtype.coe_inj

lemma ext_iff : p = q ↔ (p : ℚ) = q := subtype.ext_iff

lemma ne_iff {x y : ℚ≥0} : (x : ℚ) ≠ (y : ℚ) ↔ x ≠ y := nnrat.coe_inj.not

@[norm_cast] lemma coe_mk (q : ℚ) (hq) : ((⟨q, hq⟩ : ℚ≥0) : ℚ) = q := rfl

/-- Reinterpret a rational number `q` as a non-negative rational number. Returns `0` if `q ≤ 0`. -/
def _root_.rat.to_nnrat (q : ℚ) : ℚ≥0 := ⟨max q 0, le_max_right _ _⟩

lemma _root_.rat.coe_to_nnrat (q : ℚ) (hr : 0 ≤ q) : (q.to_nnrat : ℚ) = q := max_eq_left hr

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
max_eq_left $ le_sub.2 $ by simp [show (q : ℚ) ≤ p, from h]

-- TODO: setup semifield!
@[simp] lemma coe_eq_zero (q : ℚ≥0) : ↑q = (0 : ℚ) ↔ q = 0 := by norm_cast
lemma coe_ne_zero : (q : ℚ) ≠ 0 ↔ q ≠ 0 := (coe_eq_zero _).not

@[simp, norm_cast] lemma coe_le_coe : (p : ℚ) ≤ q ↔ p ≤ q := iff.rfl
@[simp, norm_cast] lemma coe_lt_coe : (p : ℚ) < q ↔ p < q := iff.rfl
@[simp, norm_cast] lemma coe_pos : (0 : ℚ) < q ↔ 0 < q := iff.rfl

lemma coe_mono : monotone (coe : ℚ≥0 → ℚ) := λ _ _, nnrat.coe_le_coe.2

lemma to_nnrat_mono : monotone to_nnrat := λ x y h, max_le_max h le_rfl

@[simp] lemma to_nnrat_coe (q : ℚ≥0) : to_nnrat q = q := ext $ max_eq_left q.2

@[simp] lemma to_nnrat_coe_nat (n : ℕ) : to_nnrat n = n :=
ext $ by simp [rat.coe_to_nnrat]

/-- `to_nnrat` and `coe : ℚ≥0 → ℚ` form a Galois insertion. -/
protected def gi : galois_insertion to_nnrat coe :=
galois_insertion.monotone_intro nnrat.coe_mono to_nnrat_mono rat.le_coe_to_nnrat to_nnrat_coe

/-- Coercion `ℚ≥0 → ℚ` as a `ring_hom`. -/
def to_rat_hom : ℚ≥0 →+* ℚ :=
⟨coe, nnrat.coe_one, nnrat.coe_mul, nnrat.coe_zero, nnrat.coe_add⟩

@[simp, norm_cast] lemma coe_nat_cast (n : ℕ) : (↑(↑n : ℚ≥0) : ℚ) = n := map_nat_cast to_rat_hom n

@[simp] lemma mk_coe_nat (n : ℕ) : @eq ℚ≥0 (⟨(n : ℚ), n.cast_nonneg⟩ : ℚ≥0) n :=
ext (coe_nat_cast n).symm

/-- The rational numbers are an algebra over the non-negative rationals. -/
instance : algebra ℚ≥0 ℚ := to_rat_hom.to_algebra

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [mul_action ℚ α] : mul_action ℚ≥0 α := mul_action.comp_hom α to_rat_hom.to_monoid_hom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [add_comm_monoid α] [distrib_mul_action ℚ α] : distrib_mul_action ℚ≥0 α :=
distrib_mul_action.comp_hom α to_rat_hom.to_monoid_hom

/-- A `module` over `ℚ` restricts to a `module` over `ℚ≥0`. -/
instance [add_comm_monoid α] [module ℚ α] : module ℚ≥0 α := module.comp_hom α to_rat_hom

@[simp] lemma coe_to_rat_hom : ⇑to_rat_hom = coe := rfl

@[simp, norm_cast] lemma coe_indicator (s : set α) (f : α → ℚ≥0) (a : α) :
  ((s.indicator f a : ℚ≥0) : ℚ) = s.indicator (λ x, f x) a :=
(to_rat_hom : ℚ≥0 →+ ℚ).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (q : ℚ≥0) (n : ℕ) : ((q^n : ℚ≥0) : ℚ) = q^n :=
to_rat_hom.map_pow _ _

@[norm_cast] lemma coe_list_sum (l : list ℚ≥0) : ((l.sum : ℚ≥0) : ℚ) = (l.map coe).sum :=
to_rat_hom.map_list_sum l

@[norm_cast] lemma coe_list_prod (l : list ℚ≥0) : ((l.prod : ℚ≥0) : ℚ) = (l.map coe).prod :=
to_rat_hom.map_list_prod l

@[norm_cast] lemma coe_multiset_sum (s : multiset ℚ≥0) : ((s.sum : ℚ≥0) : ℚ) = (s.map coe).sum :=
to_rat_hom.map_multiset_sum s

@[norm_cast] lemma coe_multiset_prod (s : multiset ℚ≥0) : ((s.prod : ℚ≥0) : ℚ) = (s.map coe).prod :=
to_rat_hom.map_multiset_prod s

@[norm_cast] lemma coe_sum {s : finset α} {f : α → ℚ≥0} : ↑(∑ a in s, f a) = ∑ a in s, (f a : ℚ) :=
to_rat_hom.map_sum _ _

lemma to_nnrat_sum_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a, a ∈ s → 0 ≤ f a) :
  (∑ a in s, f a).to_nnrat = ∑ a in s, (f a).to_nnrat :=
begin
  rw [←nnrat.coe_inj, nnrat.coe_sum, rat.coe_to_nnrat _ (finset.sum_nonneg hf)],
  exact finset.sum_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

@[norm_cast] lemma coe_prod {s : finset α} {f : α → ℚ≥0} : ↑(∏ a in s, f a) = ∏ a in s, (f a : ℚ) :=
to_rat_hom.map_prod _ _

lemma to_nnrat_prod_of_nonneg {s : finset α} {f : α → ℚ} (hf : ∀ a ∈ s, 0 ≤ f a) :
  (∏ a in s, f a).to_nnrat = ∏ a in s, (f a).to_nnrat :=
begin
  rw [←nnrat.coe_inj, nnrat.coe_prod, rat.coe_to_nnrat _ (finset.prod_nonneg hf)],
  exact finset.prod_congr rfl (λ x hxs, by rw rat.coe_to_nnrat _ (hf x hxs)),
end

@[norm_cast] lemma nsmul_coe (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
to_rat_hom.to_add_monoid_hom.map_nsmul _ _

-- TODO: why are these three instances necessary? why aren't they inferred? (same for `ℝ≥0`)
instance covariant_add : covariant_class ℚ≥0 ℚ≥0 (+) (≤) :=
ordered_add_comm_monoid.to_covariant_class_left ℚ≥0

instance contravariant_add : contravariant_class ℚ≥0 ℚ≥0 (+) (<) :=
ordered_cancel_add_comm_monoid.to_contravariant_class_left ℚ≥0

instance covariant_mul : covariant_class ℚ≥0 ℚ≥0 (*) (≤) :=
ordered_comm_monoid.to_covariant_class_left ℚ≥0

lemma bdd_above_coe {s : set ℚ≥0} : bdd_above ((coe : ℚ≥0 → ℚ) '' s) ↔ bdd_above s :=
iff.intro
  (λ ⟨b, hb⟩, ⟨to_nnrat b, λ ⟨y, hy⟩ hys, show y ≤ max b 0, from
    le_trans (hb $ set.mem_image_of_mem _ hys) (le_max_left _ _)⟩)
  (λ ⟨b, hb⟩, ⟨b, λ y ⟨x, hx, eq⟩, eq ▸ hb hx⟩)

lemma bdd_below_coe (s : set ℚ≥0) : bdd_below ((coe : ℚ≥0 → ℚ) '' s) :=
⟨0, λ r ⟨q, _, eq⟩, eq ▸ q.2⟩

lemma le_of_forall_pos_le_add {a b : ℚ≥0} (h : ∀ε, 0 < ε → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ λ x hxb,
begin
  rcases le_iff_exists_add.1 (le_of_lt hxb) with ⟨ε, rfl⟩,
  exact h _ ((lt_add_iff_pos_right b).1 hxb)
end

lemma mul_sup (a b c : ℚ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) := mul_max_of_nonneg _ _ (zero_le _)

lemma mul_finset_sup {f : α → ℚ≥0} {s : finset α} (r : ℚ≥0) : r * s.sup f = s.sup (λ a, r * f a) :=
begin
  classical,
  refine s.induction_on _ _,
  { simp [bot_eq_zero] },
  { exact λ a s has ih, by simp [has, ih, mul_sup] }
end

@[simp, norm_cast] lemma coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
nnrat.coe_mono.map_max

@[simp, norm_cast] lemma coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
nnrat.coe_mono.map_min

section to_nnrat

@[simp] lemma to_nnrat_zero : to_nnrat 0 = 0 := by simp [to_nnrat]; refl

@[simp] lemma to_nnrat_one : to_nnrat 1 = 1 :=
by { simp [to_nnrat, max_eq_left (zero_le_one : (0 :ℚ) ≤ 1)]; refl }

@[simp] lemma to_nnrat_pos {q : ℚ} : 0 < to_nnrat q ↔ 0 < q :=
by simp [to_nnrat, coe_lt_coe.symm, lt_irrefl]

@[simp] lemma to_nnrat_eq_zero {q : ℚ} : to_nnrat q = 0 ↔ q ≤ 0 :=
by simpa [-to_nnrat_pos] using (not_iff_not.2 (@to_nnrat_pos q))

lemma to_nnrat_of_nonpos {q : ℚ} : q ≤ 0 → to_nnrat q = 0 :=
to_nnrat_eq_zero.2

@[simp] lemma to_nnrat_le_to_nnrat_iff {q p : ℚ} (hp : 0 ≤ p) :
  to_nnrat q ≤ to_nnrat p ↔ q ≤ p :=
by simp [nnrat.coe_le_coe.symm, to_nnrat, hp]

@[simp] lemma to_nnrat_lt_to_nnrat_iff' {q p : ℚ} :
  to_nnrat q < to_nnrat p ↔ q < p ∧ 0 < p :=
by { simp [coe_lt_coe.symm, to_nnrat, lt_irrefl], intros h0p hr0, exact hr0.trans h0p }

lemma to_nnrat_lt_to_nnrat_iff {q p : ℚ} (h : 0 < p) :
  to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans (and_iff_left h)

lemma to_nnrat_lt_to_nnrat_iff_of_nonneg {q p : ℚ} (hr : 0 ≤ q) :
  to_nnrat q < to_nnrat p ↔ q < p :=
to_nnrat_lt_to_nnrat_iff'.trans ⟨and.left, λ h, ⟨h, lt_of_le_of_lt hr h⟩⟩

@[simp] lemma to_nnrat_add {q p : ℚ} (hr : 0 ≤ q) (hp : 0 ≤ p) :
  to_nnrat (q + p) = to_nnrat q + to_nnrat p :=
ext $ by simp [to_nnrat, hr, hp, add_nonneg]

lemma to_nnrat_add_le {q p : ℚ} : to_nnrat (q + p) ≤ to_nnrat q + to_nnrat p :=
coe_le_coe.1 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) $ coe_nonneg _

lemma to_nnrat_le_iff_le_coe {q : ℚ} : to_nnrat q ≤ p ↔ q ≤ ↑p := nnrat.gi.gc q p

lemma le_to_nnrat_iff_coe_le {p : ℚ} (hp : 0 ≤ p) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
by rw [←nnrat.coe_le_coe, rat.coe_to_nnrat p hp]

lemma le_to_nnrat_iff_coe_le' {p : ℚ} (hr : 0 < q) : q ≤ to_nnrat p ↔ ↑q ≤ p :=
(le_or_lt 0 p).elim le_to_nnrat_iff_coe_le $ λ hp,
  by simp only [(hp.trans_le q.coe_nonneg).not_le, to_nnrat_eq_zero.2 hp.le, hr.not_le]

lemma to_nnrat_lt_iff_lt_coe {q : ℚ} (ha : 0 ≤ q) : to_nnrat q < p ↔ q < ↑p :=
by rw [←coe_lt_coe, rat.coe_to_nnrat q ha]

lemma lt_to_nnrat_iff_coe_lt {p : ℚ} : q < to_nnrat p ↔ ↑q < p := nnrat.gi.gc.lt_iff_lt

@[simp] lemma to_nnrat_bit0 {q : ℚ} (hr : 0 ≤ q) : to_nnrat (bit0 q) = bit0 (to_nnrat q) :=
to_nnrat_add hr hr

@[simp] lemma to_nnrat_bit1 {q : ℚ} (hr : 0 ≤ q) : to_nnrat (bit1 q) = bit1 (to_nnrat q) :=
(to_nnrat_add (by simp [hr]) zero_le_one).trans (by simp [to_nnrat_one, bit1, hr])

end to_nnrat

section mul

lemma to_nnrat_mul {p q : ℚ} (hp : 0 ≤ p) : to_nnrat (p * q) = to_nnrat p * to_nnrat q :=
begin
  cases le_total 0 q with hq hq,
  { apply ext,
    simp [to_nnrat, hp, hq, max_eq_left, mul_nonneg] },
  { have hpq := mul_nonpos_of_nonneg_of_nonpos hp hq,
    rw [to_nnrat_eq_zero.2 hq, to_nnrat_eq_zero.2 hpq, mul_zero] }
end

end mul

lemma sub_def (p q : ℚ≥0) : p - q = to_nnrat (p - q) := rfl

section inv

lemma sum_div {ι} (s : finset ι) (f : ι → ℚ≥0) (b : ℚ≥0) :
  (∑ i in s, f i) / b = ∑ i in s, f i / b :=
by simp only [div_eq_mul_inv, finset.sum_mul]

@[simp] lemma inv_pos {r : ℚ≥0} : 0 < r⁻¹ ↔ 0 < r := by simp [pos_iff_ne_zero]

lemma div_pos {r p : ℚ≥0} (hr : 0 < r) (hp : 0 < p) : 0 < r / p :=
by simpa only [div_eq_mul_inv] using mul_pos hr (inv_pos.2 hp)

protected lemma mul_inv {r p : ℚ≥0} : (r * p)⁻¹ = p⁻¹ * r⁻¹ := ext $ mul_inv_rev _ _

lemma div_self_le (r : ℚ≥0) : r / r ≤ 1 :=
if h : r = 0 then by simp [h] else by rw [div_self h]

@[simp] lemma inv_le {r p : ℚ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [←mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℚ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℚ≥0} (h : p ≠ 0) : r ≤ p⁻¹ ↔ r * p ≤ 1 :=
by rw [←mul_le_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℚ≥0} (h : p ≠ 0) : r < p⁻¹ ↔ r * p < 1 :=
by rw [←mul_lt_mul_left (pos_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

lemma mul_le_iff_le_inv {a b r : ℚ≥0} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [←@mul_le_mul_left _ _ a _ r this, ←mul_assoc, mul_inv_cancel hr, one_mul]

lemma le_div_iff_mul_le {a b r : ℚ≥0} (hr : r ≠ 0) : a ≤ b / r ↔ a * r ≤ b :=
by rw [div_eq_inv_mul, ←mul_le_iff_le_inv hr, mul_comm]

lemma div_le_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a / r ≤ b ↔ a ≤ b * r :=
@div_le_iff ℚ _ a r b $ pos_iff_ne_zero.2 hr

lemma lt_div_iff {a b r : ℚ≥0} (hr : r ≠ 0) : a < b / r ↔ a * r < b :=
lt_iff_lt_of_le_iff_le (div_le_iff hr)

lemma mul_lt_of_lt_div {a b r : ℚ≥0} (h : a < b / r) : a * r < b :=
begin
  refine (lt_div_iff $ λ hr, false.elim _).1 h,
  subst r,
  simpa using h
end

lemma le_of_forall_lt_one_mul_le {x y : ℚ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ λ a ha,
  have hx : x ≠ 0 := pos_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [←lt_inv_iff_mul_lt hx', inv_inv],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma div_add_div_same (a b c : ℚ≥0) : a / c + b / c = (a + b) / c := (right_distrib a b (c⁻¹)).symm

lemma half_pos {a : ℚ≥0} (h : 0 < a) : 0 < a / 2 := div_pos h zero_lt_two

lemma add_halves (a : ℚ≥0) : a / 2 + a / 2 = a := ext (add_halves a)

lemma half_lt_self {a : ℚ≥0} (h : a ≠ 0) : a / 2 < a :=
by rw [←coe_lt_coe, nnrat.coe_div]; exact half_lt_self (bot_lt_iff_ne_bot.2 h)

lemma two_inv_lt_one : (2⁻¹:ℚ≥0) < 1 := by simpa using half_lt_self zero_ne_one.symm

lemma div_lt_iff {a b c : ℚ≥0} (hc : c ≠ 0) : b / c < a ↔ b < a * c :=
lt_iff_lt_of_le_iff_le $ nnrat.le_div_iff_mul_le hc

lemma div_lt_one_of_lt {a b : ℚ≥0} (h : a < b) : a / b < 1 :=
begin
  rwa [div_lt_iff, one_mul],
  exact ne_of_gt (lt_of_le_of_lt (zero_le _) h)
end

@[field_simps] lemma div_add_div (a : ℚ≥0) {b : ℚ≥0} (c : ℚ≥0) {d : ℚ≥0} (hb : b ≠ 0) (hd : d ≠ 0) :
  a / b + c / d = (a * d + b * c) / (b * d) :=
begin
  ext1,
  simp only [nnrat.coe_add, nnrat.coe_div, nnrat.coe_mul],
  exact div_add_div _ _ (coe_ne_zero.2 hb) (coe_ne_zero.2 hd)
end

@[field_simps] lemma add_div' (a b c : ℚ≥0) (hc : c ≠ 0) : b + a / c = (b * c + a) / c :=
by simpa using div_add_div b a one_ne_zero hc

@[field_simps] lemma div_add' (a b c : ℚ≥0) (hc : c ≠ 0) : a / c + b = (a + b * c) / c :=
by rwa [add_comm, add_div', add_comm]

lemma to_nnrat_inv (q : ℚ) : to_nnrat q⁻¹ = (to_nnrat q)⁻¹ :=
begin
  obtain hq | hq := le_total q 0,
  { rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)] },
  { nth_rewrite 0 ←rat.coe_to_nnrat q hq,
    rw [←nnrat.coe_inv, to_nnrat_coe] }
end

lemma to_nnrat_div {x y : ℚ} (hx : 0 ≤ x) : to_nnrat (x / y) = to_nnrat x / to_nnrat y :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←to_nnrat_inv, ←to_nnrat_mul hx]

lemma to_nnrat_div' {x y : ℚ} (hy : 0 ≤ y) : to_nnrat (x / y) = to_nnrat x / to_nnrat y :=
by rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hy), to_nnrat_inv]

end inv

@[simp] lemma abs_coe (q : ℚ≥0) : |(q : ℚ)| = q := abs_of_nonneg q.2

end nnrat

/-- The absolute value on `ℚ` as a map to `ℚ≥0`. -/
@[pp_nodot] def rat.nnabs (x : ℚ) : ℚ≥0 := ⟨abs x, abs_nonneg x⟩

@[norm_cast, simp] lemma rat.coe_nnabs (x : ℚ) : (rat.nnabs x : ℚ) = abs x := by simp [rat.nnabs]

/-! ### Numerator and denominator -/

namespace nnrat

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

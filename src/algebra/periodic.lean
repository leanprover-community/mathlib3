/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson
-/
import algebra.big_operators.basic
import algebra.field.opposite
import algebra.module.basic
import algebra.order.archimedean
import data.int.parity
import group_theory.coset
import group_theory.subgroup.zpowers
import group_theory.submonoid.membership

/-!
# Periodicity

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define and then prove facts about periodic and antiperiodic functions.

## Main definitions

* `function.periodic`: A function `f` is *periodic* if `∀ x, f (x + c) = f x`.
  `f` is referred to as periodic with period `c` or `c`-periodic.

* `function.antiperiodic`: A function `f` is *antiperiodic* if `∀ x, f (x + c) = -f x`.
  `f` is referred to as antiperiodic with antiperiod `c` or `c`-antiperiodic.

Note that any `c`-antiperiodic function will necessarily also be `2*c`-periodic.

## Tags

period, periodic, periodicity, antiperiodic
-/

variables {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

open_locale big_operators

namespace function

/-! ### Periodicity -/

/-- A function `f` is said to be `periodic` with period `c` if for all `x`, `f (x + c) = f x`. -/
@[simp] def periodic [has_add α] (f : α → β) (c : α) : Prop :=
∀ x : α, f (x + c) = f x

protected lemma periodic.funext [has_add α] (h : periodic f c) :
  (λ x, f (x + c)) = f :=
funext h

protected lemma periodic.comp [has_add α] (h : periodic f c) (g : β → γ) :
  periodic (g ∘ f) c :=
by simp * at *

lemma periodic.comp_add_hom [has_add α] [has_add γ]
  (h : periodic f c) (g : add_hom γ α) (g_inv : α → γ) (hg : right_inverse g_inv g) :
  periodic (f ∘ g) (g_inv c) :=
λ x, by simp only [hg c, h (g x), add_hom.map_add, comp_app]

@[to_additive]
protected lemma periodic.mul [has_add α] [has_mul β] (hf : periodic f c) (hg : periodic g c) :
  periodic (f * g) c :=
by simp * at *

@[to_additive]
protected lemma periodic.div [has_add α] [has_div β] (hf : periodic f c) (hg : periodic g c) :
  periodic (f / g) c :=
by simp * at *

@[to_additive]
lemma _root_.list.periodic_prod [has_add α] [monoid β]
  (l : list (α → β)) (hl : ∀ f ∈ l, periodic f c) :
  periodic l.prod c :=
begin
  induction l with g l ih hl,
  { simp, },
  { rw [list.forall_mem_cons] at hl,
    simpa only [list.prod_cons] using hl.1.mul (ih hl.2) }
end

@[to_additive]
lemma _root_.multiset.periodic_prod [has_add α] [comm_monoid β]
  (s : multiset (α → β)) (hs : ∀ f ∈ s, periodic f c) :
  periodic s.prod c :=
s.prod_to_list ▸ s.to_list.periodic_prod $ λ f hf, hs f $ multiset.mem_to_list.mp hf

@[to_additive]
lemma _root_.finset.periodic_prod [has_add α] [comm_monoid β]
  {ι : Type*} {f : ι → α → β} (s : finset ι) (hs : ∀ i ∈ s, periodic (f i) c) :
  periodic (∏ i in s, f i) c :=
s.prod_to_list f ▸ (s.to_list.map f).periodic_prod (by simpa [-periodic])

@[to_additive]
protected lemma periodic.smul [has_add α] [has_smul γ β] (h : periodic f c) (a : γ) :
  periodic (a • f) c :=
by simp * at *

protected lemma periodic.const_smul [add_monoid α] [group γ] [distrib_mul_action γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul] using h (a • x)

lemma periodic.const_smul₀ [add_comm_monoid α] [division_ring γ] [module γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a • x)) (a⁻¹ • c) :=
begin
  intro x,
  by_cases ha : a = 0, { simp only [ha, zero_smul] },
  simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x),
end

protected lemma periodic.const_mul [division_ring α] (h : periodic f c) (a : α) :
  periodic (λ x, f (a * x)) (a⁻¹ * c) :=
h.const_smul₀ a

lemma periodic.const_inv_smul [add_monoid α] [group γ] [distrib_mul_action γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul a⁻¹

lemma periodic.const_inv_smul₀ [add_comm_monoid α] [division_ring γ] [module γ α]
  (h : periodic f c) (a : γ) :
  periodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul₀ a⁻¹

lemma periodic.const_inv_mul [division_ring α] (h : periodic f c) (a : α) :
  periodic (λ x, f (a⁻¹ * x)) (a * c) :=
h.const_inv_smul₀ a

lemma periodic.mul_const [division_ring α] (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a)) (c * a⁻¹) :=
h.const_smul₀ $ mul_opposite.op a

lemma periodic.mul_const' [division_ring α]
  (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const a

lemma periodic.mul_const_inv [division_ring α] (h : periodic f c) (a : α) :
  periodic (λ x, f (x * a⁻¹)) (c * a) :=
h.const_inv_smul₀ $ mul_opposite.op a

lemma periodic.div_const [division_ring α] (h : periodic f c) (a : α) :
  periodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv a

lemma periodic.add_period [add_semigroup α] (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_eq [add_group α] (h : periodic f c) (x : α) :
  f (x - c) = f x :=
by simpa only [sub_add_cancel] using (h (x - c)).symm

lemma periodic.sub_eq' [add_comm_group α] (h : periodic f c) :
  f (c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h (-x)

protected lemma periodic.neg [add_group α] (h : periodic f c) :
  periodic f (-c) :=
by simpa only [sub_eq_add_neg, periodic] using h.sub_eq

lemma periodic.sub_period [add_group α] (h1 : periodic f c₁) (h2 : periodic f c₂) :
  periodic f (c₁ - c₂) :=
by simpa only [sub_eq_add_neg] using h1.add_period h2.neg

lemma periodic.const_add [add_semigroup α] (h : periodic f c) (a : α) :
  periodic (λ x, f (a + x)) c :=
λ x, by simpa [add_assoc] using h (a + x)

lemma periodic.add_const [add_comm_semigroup α] (h : periodic f c) (a : α) :
  periodic (λ x, f (x + a)) c :=
by simpa only [add_comm] using h.const_add a

lemma periodic.const_sub [add_comm_group α] (h : periodic f c) (a : α) :
  periodic (λ x, f (a - x)) c :=
λ x, by simp only [← sub_sub, h.sub_eq]

lemma periodic.sub_const [add_comm_group α] (h : periodic f c) (a : α) :
  periodic (λ x, f (x - a)) c :=
by simpa only [sub_eq_add_neg] using h.add_const (-a)

lemma periodic.nsmul [add_monoid α] (h : periodic f c) (n : ℕ) :
  periodic f (n • c) :=
by induction n; simp [nat.succ_eq_add_one, add_nsmul, ← add_assoc, zero_nsmul, *] at *

lemma periodic.nat_mul [semiring α] (h : periodic f c) (n : ℕ) :
  periodic f (n * c) :=
by simpa only [nsmul_eq_mul] using h.nsmul n

lemma periodic.neg_nsmul [add_group α] (h : periodic f c) (n : ℕ) :
  periodic f (-(n • c)) :=
(h.nsmul n).neg

lemma periodic.neg_nat_mul [ring α] (h : periodic f c) (n : ℕ) :
  periodic f (-(n * c)) :=
(h.nat_mul n).neg

lemma periodic.sub_nsmul_eq [add_group α] (h : periodic f c) (n : ℕ) :
  f (x - n • c) = f x :=
by simpa only [sub_eq_add_neg] using h.neg_nsmul n x

lemma periodic.sub_nat_mul_eq [ring α] (h : periodic f c) (n : ℕ) :
  f (x - n * c) = f x :=
by simpa only [nsmul_eq_mul] using h.sub_nsmul_eq n

lemma periodic.nsmul_sub_eq [add_comm_group α] (h : periodic f c) (n : ℕ) :
  f (n • c - x) = f (-x) :=
(h.nsmul n).sub_eq'

lemma periodic.nat_mul_sub_eq [ring α] (h : periodic f c) (n : ℕ) :
  f (n * c - x) = f (-x) :=
by simpa only [sub_eq_neg_add] using h.nat_mul n (-x)

protected lemma periodic.zsmul [add_group α] (h : periodic f c) (n : ℤ) :
  periodic f (n • c) :=
begin
  cases n,
  { simpa only [int.of_nat_eq_coe, coe_nat_zsmul] using h.nsmul n },
  { simpa only [zsmul_neg_succ_of_nat] using (h.nsmul n.succ).neg },
end

protected lemma periodic.int_mul [ring α] (h : periodic f c) (n : ℤ) :
  periodic f (n * c) :=
by simpa only [zsmul_eq_mul] using h.zsmul n

lemma periodic.sub_zsmul_eq [add_group α] (h : periodic f c) (n : ℤ) :
  f (x - n • c) = f x :=
(h.zsmul n).sub_eq x

lemma periodic.sub_int_mul_eq [ring α] (h : periodic f c) (n : ℤ) :
  f (x - n * c) = f x :=
(h.int_mul n).sub_eq x

lemma periodic.zsmul_sub_eq [add_comm_group α] (h : periodic f c) (n : ℤ) :
  f (n • c - x) = f (-x) :=
(h.zsmul _).sub_eq'

lemma periodic.int_mul_sub_eq [ring α] (h : periodic f c) (n : ℤ) :
  f (n * c - x) = f (-x) :=
(h.int_mul _).sub_eq'

protected lemma periodic.eq [add_zero_class α] (h : periodic f c) :
  f c = f 0 :=
by simpa only [zero_add] using h 0

protected lemma periodic.neg_eq [add_group α] (h : periodic f c) :
  f (-c) = f 0 :=
h.neg.eq

protected lemma periodic.nsmul_eq [add_monoid α] (h : periodic f c) (n : ℕ) :
  f (n • c) = f 0 :=
(h.nsmul n).eq

lemma periodic.nat_mul_eq [semiring α] (h : periodic f c) (n : ℕ) :
  f (n * c) = f 0 :=
(h.nat_mul n).eq

lemma periodic.zsmul_eq [add_group α] (h : periodic f c) (n : ℤ) :
  f (n • c) = f 0 :=
(h.zsmul n).eq

lemma periodic.int_mul_eq [ring α] (h : periodic f c) (n : ℤ) :
  f (n * c) = f 0 :=
(h.int_mul n).eq

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico 0 c` such that `f x = f y`. -/
lemma periodic.exists_mem_Ico₀ [linear_ordered_add_comm_group α] [archimedean α]
  (h : periodic f c) (hc : 0 < c) (x) :
  ∃ y ∈ set.Ico 0 c, f x = f y :=
let ⟨n, H, _⟩ := exists_unique_zsmul_near_of_pos' hc x in
⟨x - n • c, H, (h.sub_zsmul_eq n).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ico a (a + c)` such that `f x = f y`. -/
lemma periodic.exists_mem_Ico [linear_ordered_add_comm_group α] [archimedean α]
  (h : periodic f c) (hc : 0 < c) (x a) :
  ∃ y ∈ set.Ico a (a + c), f x = f y :=
let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ico hc x a in
⟨x + n • c, H, (h.zsmul n x).symm⟩

/-- If a function `f` is `periodic` with positive period `c`, then for all `x` there exists some
  `y ∈ Ioc a (a + c)` such that `f x = f y`. -/
lemma periodic.exists_mem_Ioc [linear_ordered_add_comm_group α] [archimedean α]
  (h : periodic f c) (hc : 0 < c) (x a) :
  ∃ y ∈ set.Ioc a (a + c), f x = f y :=
let ⟨n, H, _⟩ := exists_unique_add_zsmul_mem_Ioc hc x a in
⟨x + n • c, H, (h.zsmul n x).symm⟩

lemma periodic.image_Ioc [linear_ordered_add_comm_group α] [archimedean α]
  (h : periodic f c) (hc : 0 < c) (a : α) :
  f '' set.Ioc a (a + c) = set.range f :=
(set.image_subset_range _ _).antisymm $ set.range_subset_iff.2 $ λ x,
  let ⟨y, hy, hyx⟩ := h.exists_mem_Ioc hc x a in ⟨y, hy, hyx.symm⟩

lemma periodic_with_period_zero [add_zero_class α]
  (f : α → β) :
  periodic f 0 :=
λ x, by rw add_zero

lemma periodic.map_vadd_zmultiples [add_comm_group α] (hf : periodic f c)
  (a : add_subgroup.zmultiples c) (x : α) :
  f (a +ᵥ x) = f x :=
by { rcases a with ⟨_, m, rfl⟩, simp [add_subgroup.vadd_def, add_comm _ x, hf.zsmul m x] }

lemma periodic.map_vadd_multiples [add_comm_monoid α] (hf : periodic f c)
  (a : add_submonoid.multiples c) (x : α) :
  f (a +ᵥ x) = f x :=
by { rcases a with ⟨_, m, rfl⟩, simp [add_submonoid.vadd_def, add_comm _ x, hf.nsmul m x] }

/-- Lift a periodic function to a function from the quotient group. -/
def periodic.lift [add_group α] (h : periodic f c) (x : α ⧸ add_subgroup.zmultiples c) : β :=
quotient.lift_on' x f $
  λ a b h', (begin
    rw quotient_add_group.left_rel_apply at h',
    obtain ⟨k, hk⟩ := h',
    exact (h.zsmul k _).symm.trans (congr_arg f (add_eq_of_eq_neg_add hk)),
   end)

@[simp] lemma periodic.lift_coe [add_group α] (h : periodic f c) (a : α) :
  h.lift (a : α ⧸ add_subgroup.zmultiples c) = f a :=
rfl

/-! ### Antiperiodicity -/

/-- A function `f` is said to be `antiperiodic` with antiperiod `c` if for all `x`,
  `f (x + c) = -f x`. -/
@[simp] def antiperiodic [has_add α] [has_neg β] (f : α → β) (c : α) : Prop :=
∀ x : α, f (x + c) = -f x

protected lemma antiperiodic.funext [has_add α] [has_neg β] (h : antiperiodic f c) :
  (λ x, f (x + c)) = -f :=
funext h

protected lemma antiperiodic.funext' [has_add α] [has_involutive_neg β] (h : antiperiodic f c) :
  (λ x, -f (x + c)) = f :=
neg_eq_iff_eq_neg.mpr h.funext

/-- If a function is `antiperiodic` with antiperiod `c`, then it is also `periodic` with period
  `2 * c`. -/
protected lemma antiperiodic.periodic [semiring α] [has_involutive_neg β] (h : antiperiodic f c) :
  periodic f (2 * c) :=
by simp [two_mul, ← add_assoc, h _]

protected lemma antiperiodic.eq [add_zero_class α] [has_neg β] (h : antiperiodic f c) :
  f c = -f 0 :=
by simpa only [zero_add] using h 0

lemma antiperiodic.nat_even_mul_periodic [semiring α] [has_involutive_neg β]
  (h : antiperiodic f c) (n : ℕ) :
  periodic f (n * (2 * c)) :=
h.periodic.nat_mul n

lemma antiperiodic.nat_odd_mul_antiperiodic [semiring α] [has_involutive_neg β]
  (h : antiperiodic f c) (n : ℕ) :
  antiperiodic f (n * (2 * c) + c) :=
λ x, by rw [← add_assoc, h, h.periodic.nat_mul]

lemma antiperiodic.int_even_mul_periodic [ring α] [has_involutive_neg β]
  (h : antiperiodic f c) (n : ℤ) :
  periodic f (n * (2 * c)) :=
h.periodic.int_mul n

lemma antiperiodic.int_odd_mul_antiperiodic [ring α] [has_involutive_neg β]
  (h : antiperiodic f c) (n : ℤ) :
  antiperiodic f (n * (2 * c) + c) :=
λ x, by rw [← add_assoc, h, h.periodic.int_mul]

lemma antiperiodic.sub_eq [add_group α] [has_involutive_neg β]
  (h : antiperiodic f c) (x : α) :
  f (x - c) = -f x :=
by rw [← neg_eq_iff_eq_neg, ← h (x - c), sub_add_cancel]

lemma antiperiodic.sub_eq' [add_comm_group α] [has_neg β] (h : antiperiodic f c) :
  f (c - x) = -f (-x) :=
by simpa only [sub_eq_neg_add] using h (-x)

protected lemma antiperiodic.neg [add_group α] [has_involutive_neg β]
  (h : antiperiodic f c) :
  antiperiodic f (-c) :=
by simpa only [sub_eq_add_neg, antiperiodic] using h.sub_eq

lemma antiperiodic.neg_eq [add_group α] [has_involutive_neg β]
  (h : antiperiodic f c) :
  f (-c) = -f 0 :=
by simpa only [zero_add] using h.neg 0

lemma antiperiodic.nat_mul_eq_of_eq_zero [ring α] [neg_zero_class β]
  (h : antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℕ, f (n * c) = 0
| 0 := by rwa [nat.cast_zero, zero_mul]
| (n + 1) := by simp [add_mul, antiperiodic.nat_mul_eq_of_eq_zero n, h _]

lemma antiperiodic.int_mul_eq_of_eq_zero [ring α] [subtraction_monoid β]
  (h : antiperiodic f c) (hi : f 0 = 0) : ∀ n : ℤ, f (n * c) = 0
| (n : ℕ) := by rwa [int.cast_coe_nat, h.nat_mul_eq_of_eq_zero]
| -[1+n] := by rw [int.cast_neg_succ_of_nat, neg_mul, ← mul_neg, h.neg.nat_mul_eq_of_eq_zero hi]

lemma antiperiodic.const_add [add_semigroup α] [has_neg β] (h : antiperiodic f c) (a : α) :
  antiperiodic (λ x, f (a + x)) c :=
λ x, by simpa [add_assoc] using h (a + x)

lemma antiperiodic.add_const [add_comm_semigroup α] [has_neg β] (h : antiperiodic f c) (a : α) :
  antiperiodic (λ x, f (x + a)) c :=
λ x, by simpa only [add_right_comm] using h (x + a)

lemma antiperiodic.const_sub [add_comm_group α] [has_involutive_neg β] (h : antiperiodic f c)
  (a : α) : antiperiodic (λ x, f (a - x)) c :=
λ x, by simp only [← sub_sub, h.sub_eq]

lemma antiperiodic.sub_const [add_comm_group α] [has_neg β] (h : antiperiodic f c) (a : α) :
  antiperiodic (λ x, f (x - a)) c :=
by simpa only [sub_eq_add_neg] using h.add_const (-a)

protected lemma antiperiodic.smul [has_add α] [monoid γ] [add_group β] [distrib_mul_action γ β]
  (h : antiperiodic f c) (a : γ) :
  antiperiodic (a • f) c :=
by simp * at *

lemma antiperiodic.const_smul [add_monoid α] [has_neg β] [group γ] [distrib_mul_action γ α]
  (h : antiperiodic f c) (a : γ) :
  antiperiodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul] using h (a • x)

lemma antiperiodic.const_smul₀ [add_comm_monoid α] [has_neg β] [division_ring γ] [module γ α]
  (h : antiperiodic f c) {a : γ} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a • x)) (a⁻¹ • c) :=
λ x, by simpa only [smul_add, smul_inv_smul₀ ha] using h (a • x)

lemma antiperiodic.const_mul [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a * x)) (a⁻¹ * c) :=
h.const_smul₀ ha

lemma antiperiodic.const_inv_smul [add_monoid α] [has_neg β] [group γ] [distrib_mul_action γ α]
  (h : antiperiodic f c) (a : γ) :
  antiperiodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul a⁻¹

lemma antiperiodic.const_inv_smul₀ [add_comm_monoid α] [has_neg β] [division_ring γ] [module γ α]
  (h : antiperiodic f c) {a : γ} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a⁻¹ • x)) (a • c) :=
by simpa only [inv_inv] using h.const_smul₀ (inv_ne_zero ha)

lemma antiperiodic.const_inv_mul [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (a⁻¹ * x)) (a * c) :=
h.const_inv_smul₀ ha

lemma antiperiodic.mul_const [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c * a⁻¹) :=
h.const_smul₀ $ (mul_opposite.op_ne_zero_iff a).mpr ha

lemma antiperiodic.mul_const' [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a)) (c / a) :=
by simpa only [div_eq_mul_inv] using h.mul_const ha

lemma antiperiodic.mul_const_inv [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x * a⁻¹)) (c * a) :=
h.const_inv_smul₀ $ (mul_opposite.op_ne_zero_iff a).mpr ha

protected lemma antiperiodic.div_inv [division_ring α] [has_neg β]
  (h : antiperiodic f c) {a : α} (ha : a ≠ 0) :
  antiperiodic (λ x, f (x / a)) (c * a) :=
by simpa only [div_eq_mul_inv] using h.mul_const_inv ha

protected lemma antiperiodic.add [add_group α] [has_involutive_neg β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

protected lemma antiperiodic.sub [add_group α] [has_involutive_neg β]
  (h1 : antiperiodic f c₁) (h2 : antiperiodic f c₂) :
  periodic f (c₁ - c₂) :=
by simpa only [sub_eq_add_neg] using h1.add h2.neg

lemma periodic.add_antiperiod [add_group α] [has_neg β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ + c₂) :=
by simp [*, ← add_assoc] at *

lemma periodic.sub_antiperiod [add_group α] [has_involutive_neg β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  antiperiodic f (c₁ - c₂) :=
by simpa only [sub_eq_add_neg] using h1.add_antiperiod h2.neg

lemma periodic.add_antiperiod_eq [add_group α] [has_neg β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ + c₂) = -f 0 :=
(h1.add_antiperiod h2).eq

lemma periodic.sub_antiperiod_eq [add_group α] [has_involutive_neg β]
  (h1 : periodic f c₁) (h2 : antiperiodic f c₂) :
  f (c₁ - c₂) = -f 0 :=
(h1.sub_antiperiod h2).eq

protected lemma antiperiodic.mul [has_add α] [has_mul β] [has_distrib_neg β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f * g) c :=
by simp * at *

protected lemma antiperiodic.div [has_add α] [division_monoid β] [has_distrib_neg β]
  (hf : antiperiodic f c) (hg : antiperiodic g c) :
  periodic (f / g) c :=
by simp [*, neg_div_neg_eq] at *

end function

lemma int.fract_periodic (α) [linear_ordered_ring α] [floor_ring α] :
  function.periodic int.fract (1 : α) :=
by exact_mod_cast λ a, int.fract_add_int a 1

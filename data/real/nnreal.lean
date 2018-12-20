/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin

Nonnegative real numbers.
-/
import data.real.basic order.lattice

section discrete_field

@[simp] lemma inv_eq_zero {α} [discrete_field α] (a : α) : a⁻¹ = 0 ↔ a = 0 :=
classical.by_cases (assume : a = 0, by simp [*])(assume : a ≠ 0, by simp [*, inv_ne_zero])

end discrete_field


noncomputable theory
open lattice

local attribute [instance] classical.prop_decidable

def nnreal := {r : ℝ // 0 ≤ r}
local notation ` ℝ≥0 ` := nnreal

namespace nnreal

instance : has_coe ℝ≥0 ℝ := ⟨subtype.val⟩

protected lemma eq {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) → n = m := subtype.eq
protected lemma eq_iff {n m : ℝ≥0} : (n : ℝ) = (m : ℝ) ↔ n = m :=
iff.intro nnreal.eq (congr_arg coe)

protected def of_real (r : ℝ) : ℝ≥0 := ⟨max r 0, le_max_right _ _⟩

lemma coe_of_real (r : ℝ) (hr : 0 ≤ r) : (nnreal.of_real r : ℝ) = r :=
max_eq_left hr

instance : has_zero ℝ≥0  := ⟨⟨0, le_refl 0⟩⟩
instance : has_one ℝ≥0   := ⟨⟨1, zero_le_one⟩⟩
instance : has_add ℝ≥0   := ⟨λa b, ⟨a + b, add_nonneg a.2 b.2⟩⟩
instance : has_sub ℝ≥0   := ⟨λa b, nnreal.of_real (a - b)⟩
instance : has_mul ℝ≥0   := ⟨λa b, ⟨a * b, mul_nonneg a.2 b.2⟩⟩
instance : has_inv ℝ≥0   := ⟨λa, ⟨(a.1)⁻¹, inv_nonneg.2 a.2⟩⟩
instance : has_div ℝ≥0   := ⟨λa b, ⟨a.1 / b.1, div_nonneg' a.2 b.2⟩⟩
instance : has_le ℝ≥0    := ⟨λ r s, (r:ℝ) ≤ s⟩
instance : has_bot ℝ≥0   := ⟨0⟩
instance : inhabited ℝ≥0 := ⟨0⟩

@[simp] protected lemma coe_zero : ((0 : ℝ≥0) : ℝ) = 0 := rfl
@[simp] protected lemma coe_one  : ((1 : ℝ≥0) : ℝ) = 1 := rfl
@[simp] protected lemma coe_add (r₁ r₂ : ℝ≥0) : ((r₁ + r₂ : ℝ≥0) : ℝ) = r₁ + r₂ := rfl
@[simp] protected lemma coe_mul (r₁ r₂ : ℝ≥0) : ((r₁ * r₂ : ℝ≥0) : ℝ) = r₁ * r₂ := rfl
@[simp] protected lemma coe_div (r₁ r₂ : ℝ≥0) : ((r₁ / r₂ : ℝ≥0) : ℝ) = r₁ / r₂ := rfl
@[simp] protected lemma coe_inv (r : ℝ≥0) : ((r⁻¹ : ℝ≥0) : ℝ) = r⁻¹ := rfl

@[simp] protected lemma coe_sub (r₁ r₂ : ℝ≥0) (h : r₂ ≤ r₁) : ((r₁ - r₂ : ℝ≥0) : ℝ) = r₁ - r₂ :=
max_eq_left $ le_sub.2 $ by simp [show (r₂ : ℝ) ≤ r₁, from h]

-- TODO: setup semifield!
@[simp] protected lemma zero_div (r : ℝ≥0) : 0 / r = 0 := nnreal.eq (zero_div _)
@[simp] protected lemma coe_eq_zero (r : ℝ≥0) : ↑r = (0 : ℝ) ↔ r = 0 := @nnreal.eq_iff r 0

instance : comm_semiring ℝ≥0 :=
begin
  refine { zero := 0, add := (+), one := 1, mul := (*), ..};
  { intros;
    apply nnreal.eq;
    simp [mul_comm, mul_assoc, add_comm_monoid.add, left_distrib, right_distrib,
          add_comm_monoid.zero] }
end

instance : is_semiring_hom (coe : ℝ≥0 → ℝ) := by refine_struct {..}; intros; refl

lemma sum_coe {α} {s : finset α} {f : α → ℝ≥0} : ↑(s.sum f) = s.sum (λa, (f a : ℝ)) :=
eq.symm $ finset.sum_hom _

lemma prod_coe {α} {s : finset α} {f : α → ℝ≥0} : ↑(s.prod f) = s.prod (λa, (f a : ℝ)) :=
eq.symm $ finset.prod_hom _

lemma smul_coe (r : ℝ≥0) : ∀n, ↑(add_monoid.smul n r) = add_monoid.smul n (r:ℝ)
| 0       := rfl
| (n + 1) := by simp [add_monoid.add_smul, smul_coe n]

@[simp] protected lemma coe_nat_cast : ∀(n : ℕ), (↑(↑n : ℝ≥0) : ℝ) = n
| 0       := rfl
| (n + 1) := by simp [coe_nat_cast n]

instance : decidable_linear_order ℝ≥0 :=
{ le               := (≤),
  lt               := λa b, (a : ℝ) < b,
  lt_iff_le_not_le := assume a b, @lt_iff_le_not_le ℝ _ a b,
  le_refl          := assume a, le_refl (a : ℝ),
  le_trans         := assume a b c, @le_trans ℝ _ a b c,
  le_antisymm      := assume a b hab hba, nnreal.eq $ le_antisymm hab hba,
  le_total         := assume a b, le_total (a : ℝ) b,
  decidable_le     := λa b, by apply_instance }

protected lemma coe_le (r₁ r₂ : ℝ≥0) : r₁ ≤ r₂ ↔ (r₁ : ℝ) ≤ r₂ := iff.refl _
protected lemma coe_lt (r₁ r₂ : ℝ≥0) : r₁ < r₂ ↔ (r₁ : ℝ) < r₂ := iff.refl _

instance : canonically_ordered_monoid ℝ≥0 :=
{ add_le_add_left       := assume a b h c, @add_le_add_left ℝ _ a b h c,
  lt_of_add_lt_add_left := assume a b c, @lt_of_add_lt_add_left ℝ _ a b c,
  le_iff_exists_add     := assume ⟨a, ha⟩ ⟨b, hb⟩,
    iff.intro
      (assume h : a ≤ b,
        ⟨⟨b - a, le_sub_iff_add_le.2 $ by simp [h]⟩,
          nnreal.eq $ show b = a + (b - a), by rw [add_sub_cancel'_right]⟩)
      (assume ⟨⟨c, hc⟩, eq⟩, eq.symm ▸ show a ≤ a + c, from (le_add_iff_nonneg_right a).2 hc),
  ..nnreal.comm_semiring,
  ..nnreal.decidable_linear_order}

instance : order_bot ℝ≥0 :=
{ bot := ⊥, bot_le := zero_le, .. nnreal.decidable_linear_order }

instance : distrib_lattice ℝ≥0 := by apply_instance

instance : semilattice_inf_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : semilattice_sup_bot ℝ≥0 :=
{ .. nnreal.lattice.order_bot, .. nnreal.lattice.distrib_lattice }

instance : linear_ordered_semiring ℝ≥0 :=
{ add_left_cancel            := assume a b c h, nnreal.eq $ @add_left_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  add_right_cancel           := assume a b c h, nnreal.eq $ @add_right_cancel ℝ _ a b c (nnreal.eq_iff.2 h),
  le_of_add_le_add_left      := assume a b c, @le_of_add_le_add_left ℝ _ a b c,
  mul_le_mul_of_nonneg_left  := assume a b c, @mul_le_mul_of_nonneg_left ℝ _ a b c,
  mul_le_mul_of_nonneg_right := assume a b c, @mul_le_mul_of_nonneg_right ℝ _ a b c,
  mul_lt_mul_of_pos_left     := assume a b c, @mul_lt_mul_of_pos_left ℝ _ a b c,
  mul_lt_mul_of_pos_right    := assume a b c, @mul_lt_mul_of_pos_right ℝ _ a b c,
  zero_lt_one                := @zero_lt_one ℝ _,
  .. nnreal.decidable_linear_order,
  .. nnreal.canonically_ordered_monoid,
  .. nnreal.comm_semiring }

instance : canonically_ordered_comm_semiring ℝ≥0 :=
{ zero_ne_one     := assume h, @zero_ne_one ℝ _ $ congr_arg subtype.val $ h,
  mul_eq_zero_iff := assume a b, nnreal.eq_iff.symm.trans $ mul_eq_zero.trans $ by simp,
  .. nnreal.linear_ordered_semiring,
  .. nnreal.canonically_ordered_monoid,
  .. nnreal.comm_semiring }

instance : densely_ordered ℝ≥0 :=
⟨assume a b (h : (a : ℝ) < b), let ⟨c, hac, hcb⟩ := dense h in
  ⟨⟨c, le_trans a.property $ le_of_lt $ hac⟩, hac, hcb⟩⟩

instance : no_top_order ℝ≥0 :=
⟨assume a, let ⟨b, hb⟩ := no_top (a:ℝ) in ⟨⟨b, le_trans a.property $ le_of_lt $ hb⟩, hb⟩⟩

lemma bdd_above_coe {s : set ℝ≥0} : bdd_above ((coe : nnreal → ℝ) '' s) ↔ bdd_above s :=
iff.intro
  (assume ⟨b, hb⟩, ⟨nnreal.of_real b, assume ⟨y, hy⟩ hys, show y ≤ max b 0, from
    le_max_left_of_le $ hb _ $ set.mem_image_of_mem _ hys⟩)
  (assume ⟨b, hb⟩, ⟨b, assume y ⟨x, hx, eq⟩, eq ▸ hb _ $ hx⟩)

lemma bdd_below_coe (s : set ℝ≥0) : bdd_below ((coe : nnreal → ℝ) '' s) :=
⟨0, assume r ⟨q, _, eq⟩, eq ▸ q.2⟩

instance : has_Sup ℝ≥0 :=
⟨λs, ⟨Sup ((coe : nnreal → ℝ) '' s),
  begin
    by_cases h : s = ∅,
    { simp [h, set.image_empty, real.Sup_empty] },
    rcases set.ne_empty_iff_exists_mem.1 h with ⟨⟨b, hb⟩, hbs⟩,
    by_cases h' : bdd_above s,
    { exact le_cSup_of_le (bdd_above_coe.2 h') (set.mem_image_of_mem _ hbs) hb },
    { rw [real.Sup_of_not_bdd_above], rwa [bdd_above_coe] }
  end⟩⟩

instance : has_Inf ℝ≥0 :=
⟨λs, ⟨Inf ((coe : nnreal → ℝ) '' s),
  begin
    by_cases h : s = ∅,
    { simp [h, set.image_empty, real.Inf_empty] },
    exact le_cInf (by simp [h]) (assume r ⟨q, _, eq⟩, eq ▸ q.2)
  end⟩⟩

lemma coe_Sup (s : set nnreal) : (↑(Sup s) : ℝ) = Sup ((coe : nnreal → ℝ) '' s) := rfl
lemma coe_Inf (s : set nnreal) : (↑(Inf s) : ℝ) = Inf ((coe : nnreal → ℝ) '' s) := rfl

instance : conditionally_complete_linear_order_bot ℝ≥0 :=
{ Sup     := Sup,
  Inf     := Inf,
  le_cSup := assume s a hs ha, le_cSup (bdd_above_coe.2 hs) (set.mem_image_of_mem _ ha),
  cSup_le := assume s a hs h,show Sup ((coe : nnreal → ℝ) '' s) ≤ a, from
    cSup_le (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h _ hb,
  cInf_le := assume s a _ has, cInf_le (bdd_below_coe s) (set.mem_image_of_mem _ has),
  le_cInf := assume s a hs h, show (↑a : ℝ) ≤ Inf ((coe : nnreal → ℝ) '' s), from
    le_cInf (by simp [hs]) $ assume r ⟨b, hb, eq⟩, eq ▸ h _ hb,
  cSup_empty := nnreal.eq $ by simp [coe_Sup, real.Sup_empty]; refl,
  decidable_le := begin assume x y, apply classical.dec end,
  .. nnreal.linear_ordered_semiring, .. lattice.lattice_of_decidable_linear_order,
  .. nnreal.lattice.order_bot }

instance : archimedean nnreal :=
⟨ assume x y pos_y,
  let ⟨n, hr⟩ := archimedean.arch (x:ℝ) (pos_y : (0 : ℝ) < y) in
  ⟨n, show (x:ℝ) ≤ (add_monoid.smul n y : nnreal), by simp [*, smul_coe]⟩ ⟩

lemma le_of_forall_epsilon_le {a b : nnreal} (h : ∀ε, ε > 0 → a ≤ b + ε) : a ≤ b :=
le_of_forall_le_of_dense $ assume x hxb,
begin
  rcases le_iff_exists_add.1 (le_of_lt hxb) with ⟨ε, rfl⟩,
  exact h _ ((lt_add_iff_pos_right b).1 hxb)
end

lemma lt_iff_exists_rat_btwn (a b : nnreal) :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < nnreal.of_real q ∧ nnreal.of_real q < b) :=
iff.intro
  (assume (h : (↑a:ℝ) < (↑b:ℝ)),
    let ⟨q, haq, hqb⟩ := exists_rat_btwn h in
    have 0 ≤ (q : ℝ), from le_trans a.2 $ le_of_lt haq,
    ⟨q, rat.cast_nonneg.1 this, by simp [coe_of_real _ this, nnreal.coe_lt, haq, hqb]⟩)
  (assume ⟨q, _, haq, hqb⟩, lt_trans haq hqb)

lemma bot_eq_zero : (⊥ : nnreal) = 0 := rfl

lemma mul_sup (a b c : ℝ≥0) : a * (b ⊔ c) = (a * b) ⊔ (a * c) :=
begin
  cases le_total b c with h h,
  { simp [sup_eq_max, max_eq_right h, max_eq_right (mul_le_mul_of_nonneg_left h (zero_le a))] },
  { simp [sup_eq_max, max_eq_left h, max_eq_left (mul_le_mul_of_nonneg_left h (zero_le a))] },
end

lemma mul_finset_sup {α} {f : α → ℝ≥0} {s : finset α} (r : ℝ≥0) :
  r * s.sup f = s.sup (λa, r * f a) :=
begin
  refine s.induction_on _ _,
  { simp [bot_eq_zero] },
  { assume a s has ih, simp [has, ih, mul_sup], }
end

section of_real

@[simp] lemma zero_le_coe {q : nnreal} : 0 ≤ (q : ℝ) := q.2

@[simp] lemma of_real_zero : nnreal.of_real 0 = 0 :=
by simp [nnreal.of_real]; refl

@[simp] lemma zero_lt_of_real (r : ℝ) : 0 < nnreal.of_real r ↔ 0 < r :=
by simp [nnreal.of_real, nnreal.coe_lt, lt_max_iff, lt_irrefl]

@[simp] lemma of_real_eq_zero (r : ℝ) : nnreal.of_real r = 0 ↔ r ≤ 0 :=
by simpa [-zero_lt_of_real] using (not_iff_not.2 (zero_lt_of_real r))

@[simp] lemma of_real_coe {r : nnreal} : nnreal.of_real r = r :=
nnreal.eq $ by simp [nnreal.of_real, max_eq_left]

@[simp] lemma of_real_le_of_real_iff {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  nnreal.of_real r ≤ nnreal.of_real p ↔ r ≤ p :=
by simp [nnreal.coe_le, nnreal.of_real, hr, hp, max_eq_left]

@[simp] lemma of_real_add_of_real {r p : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) :
  nnreal.of_real r + nnreal.of_real p = nnreal.of_real (r + p) :=
nnreal.eq $ by simp [nnreal.of_real, hr, hp, max_eq_left, add_nonneg]

lemma of_real_of_nonpos {r : ℝ} (h : r ≤ 0) : nnreal.of_real r = 0 :=
by simp [nnreal.of_real, max_eq_right h]; refl

lemma of_real_le_of_real {r p : ℝ} (h : r ≤ p) : nnreal.of_real r ≤ nnreal.of_real p :=
(nnreal.coe_le _ _).2 $ max_le_max h $ le_refl _

lemma of_real_add_le {r p : ℝ} : nnreal.of_real (r + p) ≤ nnreal.of_real r + nnreal.of_real p :=
(nnreal.coe_le _ _).2 $ max_le (add_le_add (le_max_left _ _) (le_max_left _ _)) nnreal.zero_le_coe

end of_real

section mul

lemma mul_eq_mul_left {a b c : nnreal} (h : a ≠ 0) : (a * b = a * c ↔ b = c) :=
begin
  rw [← nnreal.eq_iff, ← nnreal.eq_iff, nnreal.coe_mul, nnreal.coe_mul], split,
  { exact eq_of_mul_eq_mul_left (mt (@nnreal.eq_iff a 0).1 h) },
  { assume h, rw [h] }
end

end mul

section sub

lemma sub_eq_zero {r p : nnreal} (h : r ≤ p) : r - p = 0 :=
nnreal.eq $ max_eq_right $ sub_le_iff_le_add.2 $ by simpa [nnreal.coe_le] using h

@[simp] lemma sub_le_iff_le_add {r p q : nnreal} : r - p ≤ q ↔ r ≤ q + p :=
match le_total p r with
| or.inl h :=
  by rw [nnreal.coe_le, nnreal.coe_le, nnreal.coe_sub _ _ h, nnreal.coe_add, sub_le_iff_le_add]
| or.inr h :=
  have r ≤ p + q, from le_add_right h,
  by simpa [nnreal.coe_le, nnreal.coe_le, sub_eq_zero h]
end

lemma add_sub_cancel {r p : nnreal} : (p + r) - r = p :=
nnreal.eq $ by rw [nnreal.coe_sub, nnreal.coe_add, add_sub_cancel]; exact le_add_left (le_refl _)

lemma add_sub_cancel' {r p : nnreal} : (r + p) - r = p :=
by rw [add_comm, add_sub_cancel]

@[simp] lemma sub_add_cancel_of_le {a b : nnreal} (h : b ≤ a) : (a - b) + b = a :=
nnreal.eq $ by rw [nnreal.coe_add, nnreal.coe_sub _ _ h, sub_add_cancel]

end sub

section inv

lemma div_def {r p : nnreal} : r / p = r * p⁻¹ := rfl

@[simp] lemma inv_zero : (0 : nnreal)⁻¹ = 0 := nnreal.eq inv_zero

@[simp] lemma inv_eq_zero {r : nnreal} : (r : nnreal)⁻¹ = 0 ↔ r = 0 :=
by rw [← nnreal.eq_iff, nnreal.coe_inv, nnreal.coe_zero, inv_eq_zero, ← nnreal.coe_zero, nnreal.eq_iff]

@[simp] lemma inv_pos {r : nnreal} : 0 < r⁻¹ ↔ 0 < r :=
by simp [zero_lt_iff_ne_zero]

@[simp] lemma inv_mul_cancel {r : ℝ≥0} (h : r ≠ 0) : r⁻¹ * r = 1 :=
nnreal.eq $ inv_mul_cancel $ mt (@nnreal.eq_iff r 0).1 h

@[simp] lemma mul_inv_cancel {r : ℝ≥0} (h : r ≠ 0) : r * r⁻¹ = 1 :=
by rw [mul_comm, inv_mul_cancel h]

@[simp] lemma inv_inv {r : ℝ≥0} : r⁻¹⁻¹ = r := nnreal.eq inv_inv'

@[simp] lemma inv_le {r p : ℝ≥0} (h : r ≠ 0) : r⁻¹ ≤ p ↔ 1 ≤ r * p :=
by rw [← mul_le_mul_left (zero_lt_iff_ne_zero.2 h), mul_inv_cancel h]

lemma inv_le_of_le_mul {r p : ℝ≥0} (h : 1 ≤ r * p) : r⁻¹ ≤ p :=
by by_cases r = 0; simp [*, inv_le]

@[simp] lemma le_inv_iff_mul_le {r p : ℝ≥0} (h : p ≠ 0) : (r ≤ p⁻¹ ↔ r * p ≤ 1) :=
by rw [← mul_le_mul_left (zero_lt_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

@[simp] lemma lt_inv_iff_mul_lt {r p : ℝ≥0} (h : p ≠ 0) : (r < p⁻¹ ↔ r * p < 1) :=
by rw [← mul_lt_mul_left (zero_lt_iff_ne_zero.2 h), mul_inv_cancel h, mul_comm]

lemma mul_le_if_le_inv {a b r : nnreal} (hr : r ≠ 0) : r * a ≤ b ↔ a ≤ r⁻¹ * b :=
have 0 < r, from lt_of_le_of_ne (zero_le r) hr.symm,
by rw [← @mul_le_mul_left _ _ a _ r this, ← mul_assoc, mul_inv_cancel hr, one_mul]

lemma le_of_forall_lt_one_mul_lt {x y : ℝ≥0} (h : ∀a<1, a * x ≤ y) : x ≤ y :=
le_of_forall_ge_of_dense $ assume a ha,
  have hx : x ≠ 0 := zero_lt_iff_ne_zero.1 (lt_of_le_of_lt (zero_le _) ha),
  have hx' : x⁻¹ ≠ 0, by rwa [(≠), inv_eq_zero],
  have a * x⁻¹ < 1, by rwa [← lt_inv_iff_mul_lt hx', inv_inv],
  have (a * x⁻¹) * x ≤ y, from h _ this,
  by rwa [mul_assoc, inv_mul_cancel hx, mul_one] at this

lemma div_add_div_same (a b c : ℝ≥0) : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma add_halves (a : nnreal) : a / 2 + a / 2 = a := nnreal.eq (add_halves a)

end inv

end nnreal

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals
-/
import order.bounds topology.real topology.infinite_sum
noncomputable theory
open classical set lattice filter
local attribute [instance] decidable_inhabited prop_decidable

universe u
-- TODO: this is necessary additionally to mul_nonneg otherwise the simplifier can not match
lemma zero_le_mul {α : Type u} [ordered_semiring α] {a b : α} : 0 ≤ a → 0 ≤ b → 0 ≤ a * b :=
mul_nonneg

lemma inv_pos {α : Type*} [linear_ordered_field α] {r : α} : 0 < r → 0 < r⁻¹ :=
by rw [inv_eq_one_div]; exact div_pos_of_pos_of_pos zero_lt_one

lemma inv_inv' {α : Type*} [discrete_field α] {r : α} : r ≠ 0 → (r⁻¹)⁻¹ = r :=
by rw [inv_eq_one_div, inv_eq_one_div, div_div_eq_mul_div]; simp [div_one]

section complete_linear_order
variables {α : Type u} [complete_linear_order α] {s : set α} {a b c : α}

lemma lt_Sup_iff : b < Sup s ↔ (∃a∈s, b < a) :=
iff.intro
  (assume : b < Sup s, classical.by_contradiction $ assume : ¬ (∃a∈s, b < a),
    have Sup s ≤ b,
      from Sup_le $ assume a ha, le_of_not_gt $ assume h, this ⟨a, ha, h⟩,
    lt_irrefl b (lt_of_lt_of_le ‹b < Sup s› ‹Sup s ≤ b›))
  (assume ⟨a, ha, h⟩, lt_of_lt_of_le h $ le_Sup ha)

lemma Sup_eq_top : Sup s = ⊤ ↔ (∀b<⊤, ∃a∈s, b < a) :=
iff.intro
  (assume (h : Sup s = ⊤) b hb, by rwa [←h, lt_Sup_iff] at hb)
  (assume h, top_unique $ le_of_not_gt $ assume h',
    let ⟨a, ha, h⟩ := h _ h' in
    lt_irrefl a $ lt_of_le_of_lt (le_Sup ha) h)

end complete_linear_order

inductive ennreal : Type
| of_nonneg_real : Πr:real, 0 ≤ r → ennreal
| infinity : ennreal

local notation `∞` := ennreal.infinity

namespace ennreal
variables {a b c d : ennreal} {r p q : ℝ}

section projections

def of_real (r : ℝ) : ennreal := of_nonneg_real (max 0 r) (le_max_left 0 r)

def of_ennreal : ennreal → ℝ
| (of_nonneg_real r _) := r
| ∞ := 0

@[simp] lemma of_ennreal_of_real (h : 0 ≤ r) : of_ennreal (of_real r) = r := max_eq_right h

lemma zero_le_of_ennreal : ∀{a}, 0 ≤ of_ennreal a
| (of_nonneg_real r hr) := hr
| ∞ := le_refl 0

@[simp] lemma of_real_of_ennreal : ∀{a}, a ≠ ∞ → of_real (of_ennreal a) = a
| (of_nonneg_real r hr) h := by simp [of_real, of_ennreal, max, hr]
| ∞ h := false.elim $ h rfl

lemma forall_ennreal {p : ennreal → Prop} : (∀a, p a) ↔ (∀r (h : 0 ≤ r), p (of_real r)) ∧ p ∞ :=
⟨assume h, ⟨assume r hr, h _, h _⟩,
  assume ⟨h₁, h₂⟩, ennreal.rec
    begin
      intros r hr,
      let h₁ := h₁ r hr,
      simp [of_real, max, hr] at h₁,
      exact h₁
    end
    h₂⟩

end projections

section semiring

instance : has_zero ennreal := ⟨of_real 0⟩
instance : has_one ennreal := ⟨of_real 1⟩
instance ennreal.inhabited : inhabited ennreal := ⟨0⟩

@[simp] lemma of_real_zero : of_real 0 = 0 := rfl
@[simp] lemma of_real_one : of_real 1 = 1 := rfl

@[simp] lemma zero_ne_infty : 0 ≠ ∞ := assume h, ennreal.no_confusion h
@[simp] lemma infty_ne_zero : ∞ ≠ 0 := assume h, ennreal.no_confusion h

@[simp] lemma of_real_ne_infty : of_real r ≠ ∞ := assume h, ennreal.no_confusion h
@[simp] lemma infty_ne_of_real : ∞ ≠ of_real r := assume h, ennreal.no_confusion h

@[simp] lemma of_real_eq_of_real_of (hr : 0 ≤ r) (hq : 0 ≤ q) : of_real r = of_real q ↔ r = q :=
by simp [of_real, max, hr, hq]; exact ⟨ennreal.of_nonneg_real.inj, by simp {contextual := tt}⟩

lemma of_real_ne_of_real_of (hr : 0 ≤ r) (hq : 0 ≤ q) : of_real r ≠ of_real q ↔ r ≠ q :=
by simp [hr, hq]

lemma of_real_of_nonpos (hr : r ≤ 0) : of_real r = 0 :=
have ∀r₁ r₂ : real, r₁ = r₂ → ∀h₁:0≤r₁, ∀h₂:0≤r₂, of_nonneg_real r₁ h₁ = of_nonneg_real r₂ h₂,
  from assume r₁ r₂ h, match r₁, r₂, h with _, _, rfl := assume _ _, rfl end,
this _ _ (by simp [hr, max_eq_left]) _ _

lemma of_real_of_not_nonneg (hr : ¬ 0 ≤ r) : of_real r = 0 :=
of_real_of_nonpos $ le_of_lt $ lt_of_not_ge hr

instance : zero_ne_one_class ennreal :=
{ zero := 0, one := 1, zero_ne_one := (of_real_ne_of_real_of (le_refl 0) zero_le_one).mpr zero_ne_one }

@[simp] lemma of_real_eq_zero_iff (hr : 0 ≤ r) : of_real r = 0 ↔ r = 0 :=
of_real_eq_of_real_of hr (le_refl 0)

@[simp] lemma zero_eq_of_real_iff (hr : 0 ≤ r) : 0 = of_real r ↔ 0 = r :=
of_real_eq_of_real_of (le_refl 0) hr

@[simp] lemma of_real_eq_one_iff : of_real r = 1 ↔ r = 1 :=
match le_total 0 r with
| or.inl h := of_real_eq_of_real_of h zero_le_one
| or.inr h :=
  have r ≠ 1, from assume h', lt_irrefl (0:ℝ) $ lt_of_lt_of_le (by rw [h']; exact zero_lt_one) h,
  by simp [of_real_of_nonpos h, this]
end

@[simp] lemma one_eq_of_real_iff : 1 = of_real r ↔ 1 = r :=
by rw [eq_comm, of_real_eq_one_iff, eq_comm]

lemma of_nonneg_real_eq_of_real (hr : 0 ≤ r) : of_nonneg_real r hr = of_real r :=
by simp [of_real, hr, max]

protected def add : ennreal → ennreal → ennreal
| (of_nonneg_real a ha) (of_nonneg_real b hb) := of_real (a + b)
| _ _ := ∞

protected def mul : ennreal → ennreal → ennreal
| (of_nonneg_real a ha) (of_nonneg_real b hb) := of_real (a * b)
| ∞ (of_nonneg_real b hb) := if b = 0 then 0 else ∞
| (of_nonneg_real a ha) ∞ := if a = 0 then 0 else ∞
| _ _ := ∞

instance : has_add ennreal := ⟨ennreal.add⟩
instance : has_mul ennreal := ⟨ennreal.mul⟩

@[simp] lemma of_real_add_of_real (hr : 0 ≤ r) (hq : 0 ≤ p) :
  of_real r + of_real p = of_real (r + p) :=
by simp [of_real, max, hr, hq]; refl

@[simp] lemma add_infty : a + ∞ = ∞ :=
by cases a; refl

@[simp] lemma infty_add : ∞ + a = ∞ :=
by cases a; refl

@[simp] lemma of_real_mul_of_real (hr : 0 ≤ r) (hq : 0 ≤ p) :
  of_real r * of_real p = of_real (r * p) :=
by simp [of_real, max, hr, hq]; refl

@[simp] lemma of_real_mul_infty (hr : 0 ≤ r) : of_real r * ∞ = (if r = 0 then 0 else ∞) :=
by simp [of_real, max, hr]; refl

@[simp] lemma infty_mul_of_real (hr : 0 ≤ r) : ∞ * of_real r = (if r = 0 then 0 else ∞) :=
by simp [of_real, max, hr]; refl

@[simp] lemma mul_infty : ∀{a}, a * ∞ = (if a = 0 then 0 else ∞) :=
forall_ennreal.mpr ⟨assume r hr, by simp [hr]; by_cases r = 0; simp [h], by simp; refl⟩

@[simp] lemma infty_mul : ∀{a}, ∞ * a = (if a = 0 then 0 else ∞) :=
forall_ennreal.mpr ⟨assume r hr, by simp [hr]; by_cases r = 0; simp [h], by simp; refl⟩

instance : add_comm_monoid ennreal :=
{ add_comm_monoid .
  zero := 0,
  add  := (+),
  add_zero := by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual:=tt},
  zero_add := by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual:=tt},
  add_comm := by simp [forall_ennreal, le_add_of_le_of_nonneg] {contextual:=tt},
  add_assoc := by simp [forall_ennreal, le_add_of_le_of_nonneg] {contextual:=tt} }

protected lemma mul_zero : ∀a:ennreal, a * 0 = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_comm : ∀a b:ennreal, a * b = b * a :=
by simp [forall_ennreal] {contextual := tt}

protected lemma zero_mul : ∀a:ennreal, 0 * a = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_assoc : ∀a b c:ennreal, a * b * c = a * (b * c) :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ra = 0 with ha', simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases rb = 0 with hb', simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases rc = 0 with hc', simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases rb = 0 with hb', simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases rc = 0 with hb';
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp [*]
end

protected lemma left_distrib : ∀a b c:ennreal, a * (b + c) = a * b + a * c :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ra = 0 with ha', simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases rb = 0 with hb', simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul, add_nonneg, left_distrib] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases rc = 0 with hc', simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases rb = 0 with hb', simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases rc = 0 with hb';
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero, add_nonneg,
          add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp [*]
end

instance : comm_semiring ennreal :=
{ ennreal.add_comm_monoid with
  one  := 1,
  mul  := (*),
  mul_zero := ennreal.mul_zero,
  zero_mul := ennreal.zero_mul,
  one_mul := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_one := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_comm := ennreal.mul_comm,
  mul_assoc := ennreal.mul_assoc,
  left_distrib := ennreal.left_distrib,
  right_distrib := assume a b c, by rw [ennreal.mul_comm, ennreal.left_distrib,
    ennreal.mul_comm, ennreal.mul_comm b c]; refl }

end semiring

section order

instance : has_le ennreal := ⟨λ a b, b = ∞ ∨ (∃r p, 0 ≤ r ∧ r ≤ p ∧ a = of_real r ∧ b = of_real p)⟩

@[simp] lemma infty_le_iff : ∞ ≤ a ↔ a = ∞ :=
by unfold has_le.le; simp

@[simp] lemma le_infty : a ≤ ∞ :=
by unfold has_le.le; simp

@[simp] lemma of_real_le_of_real_iff (hr : 0 ≤ r) (hp : 0 ≤ p) :
  of_real r ≤ of_real p ↔ r ≤ p :=
show (of_real p = ∞ ∨ _) ↔ _,
begin
  simp, constructor,
  exact assume ⟨r', q', hrq', h₁, h₂, hr'⟩,
    by simp [hr, hr', le_trans hr' hrq', hp] at h₁ h₂; simp [*],
  exact assume h, ⟨r, p, h, rfl, rfl, hr⟩
end

@[simp] lemma one_le_of_real_iff (hr : 0 ≤ r) : 1 ≤ of_real r ↔ 1 ≤ r :=
of_real_le_of_real_iff zero_le_one hr

instance : decidable_linear_order ennreal :=
{ decidable_linear_order .
  le := (≤),
  le_refl := by simp [forall_ennreal, le_refl] {contextual := tt},
  le_trans := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb c hc, le_trans,
  le_antisymm := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_antisymm,
  le_total := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_total _ _,
  decidable_le := by apply_instance }

@[simp] lemma not_infty_lt : ¬ ∞ < a :=
assume ⟨h₁, h₂⟩, h₂ le_infty

@[simp] lemma of_real_lt_infty : of_real r < ∞ :=
⟨le_infty, assume h, ennreal.no_confusion $ infty_le_iff.mp h⟩

lemma le_of_real_iff (hr : 0 ≤ r) : ∀{a}, a ≤ of_real r ↔ (∃p, 0 ≤ p ∧ p ≤ r ∧ a = of_real p) :=
have ∀p, 0 ≤ p → (of_real p ≤ of_real r ↔ ∃ (q : ℝ), 0 ≤ q ∧ q ≤ r ∧ of_real p = of_real q),
  from assume p hp, ⟨assume h, ⟨p, hp, (of_real_le_of_real_iff hp hr).mp h, rfl⟩,
    assume ⟨q, hq, hqr, heq⟩, calc of_real p = of_real q : heq
      ... ≤ _ : (of_real_le_of_real_iff hq hr).mpr hqr⟩,
forall_ennreal.mpr $ ⟨this, by simp⟩

@[simp] lemma of_real_lt_of_real_iff :
  0 ≤ r → 0 ≤ p → (of_real r < of_real p ↔ r < p) :=
by simp [lt_iff_le_not_le] {contextual:=tt}

lemma lt_iff_exists_of_real : ∀{a b}, a < b ↔ (∃p, 0 ≤ p ∧ a = of_real p ∧ of_real p < b) :=
by simp [forall_ennreal] {contextual := tt}; exact assume r hr,
  ⟨⟨r, rfl, hr⟩, assume p hp, ⟨assume h, ⟨r, by simp [*] {contextual := tt}⟩,
    assume ⟨q, h₁, h₂, h₃⟩, by simp [*] at *⟩⟩

@[simp] protected lemma zero_le : ∀{a:ennreal}, 0 ≤ a :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual:=tt}

@[simp] lemma le_zero_iff_eq : a ≤ 0 ↔ a = 0 :=
⟨assume h, le_antisymm h ennreal.zero_le, assume h, h ▸ le_refl a⟩

@[simp] lemma zero_lt_of_real_iff : 0 < of_real p ↔ 0 < p :=
by_cases
  (assume : 0 ≤ p, of_real_lt_of_real_iff (le_refl _) this)
  (by simp [lt_irrefl, not_imp_not, le_of_lt, of_real_of_not_nonneg] {contextual := tt})

@[simp] lemma not_lt_zero : ¬ a < 0 :=
assume h, lt_irrefl a $ lt_of_lt_of_le h ennreal.zero_le

protected lemma zero_lt_one : 0 < (1 : ennreal) :=
zero_lt_of_real_iff.mpr zero_lt_one

lemma of_real_lt_of_real_iff_cases : (of_real r < of_real p ↔ (0 < p ∧ r < p)) :=
begin
  by_cases 0 ≤ p with hp,
  { by_cases 0 ≤ r with hr,
    { simp [*, iff_def] {contextual := tt},
      show r < p → 0 < p, from lt_of_le_of_lt hr },
    { have h : r ≤ 0, from le_of_lt (lt_of_not_ge hr),
      simp [*, iff_def, of_real_of_not_nonneg] {contextual := tt},
      show 0 < p → r < p, from lt_of_le_of_lt h } },
  simp [*, not_le_iff, not_lt_iff, le_of_lt, of_real_of_not_nonneg] at *
end

instance : densely_ordered ennreal :=
⟨begin
  simp [forall_ennreal] {contextual := tt},
  intros r hr,
  constructor,
  { existsi of_real (r + 1), simp [hr, add_nonneg, lt_add_of_le_of_pos, zero_le_one, zero_lt_one] },
  { exact assume p hp h,
      let ⟨q, h₁, h₂⟩ := dense h in
      have 0 ≤ q, from le_trans hr $ le_of_lt h₁,
      ⟨of_real q, by simp [*]⟩ }
end⟩

lemma add_le_add : ∀{b d}, a ≤ b → c ≤ d → a + c ≤ b + d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, add_nonneg, add_le_add] {contextual := tt}, by simp⟩, by simp⟩

lemma lt_of_add_lt_add_left (h : a + b < a + c) : b < c :=
lt_of_not_ge $ assume h', lt_irrefl (a + b) (lt_of_lt_of_le h $ add_le_add (le_refl a) h')

lemma le_add_left (h : a ≤ c) : a ≤ b + c :=
calc a = 0 + a : by simp
  ... ≤ b + c : add_le_add ennreal.zero_le h

lemma le_add_right (h : a ≤ b) : a ≤ b + c :=
calc a = a + 0 : by simp
  ... ≤ b + c : add_le_add h ennreal.zero_le

protected lemma le_iff_exists_add : ∀{b a:ennreal}, a ≤ b ↔ (∃c, b = a + c) :=
begin
  simp [forall_ennreal] {contextual:=tt},
  constructor,
  exact assume r hr, ⟨∞, by simp⟩,
  exact assume r hr p hp, iff.intro
    (assume h, ⟨of_real (r - p),
      begin
        rw [of_real_add_of_real, sub_add_cancel],
        { simp [le_sub_iff_add_le, *, -sub_eq_add_neg] },
        exact hp
      end⟩)
    (assume ⟨c, hc⟩, by rw [←of_real_le_of_real_iff hp hr, hc]; exact le_add_left (le_refl _))
end

lemma mul_le_mul : ∀{b d}, a ≤ b → c ≤ d → a * c ≤ b * d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, zero_le_mul, mul_le_mul] {contextual := tt},
    by by_cases r = 0; simp [*] {contextual:=tt}⟩,
    assume d, by by_cases d = 0; simp [*] {contextual:=tt}⟩

end order

section complete_lattice

@[simp] lemma infty_mem_upper_bounds {s : set ennreal} : ∞ ∈ upper_bounds s :=
assume x hx, le_infty

lemma of_real_mem_upper_bounds {s : set real} (hs : ∀x∈s, (0:real) ≤ x) (hr : 0 ≤ r) :
  of_real r ∈ upper_bounds (of_real '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, *] {contextual := tt}

lemma is_lub_of_real {s : set real} (hs : ∀x∈s, (0:real) ≤ x) (hr : 0 ≤ r) (h : s ≠ ∅) :
  is_lub (of_real '' s) (of_real r) ↔ is_lub s r :=
let ⟨x, hx₁⟩ := exists_mem_of_ne_empty h in
have hx₂ : 0 ≤ x, from hs _ hx₁,
begin
  simp [is_lub, is_least, lower_bounds, of_real_mem_upper_bounds, hs, hr, forall_ennreal]
    {contextual := tt},
  exact (and_congr_right $ assume hrb,
    ⟨assume h p hp, h _ (le_trans hx₂ $ hp _ hx₁) hp, assume h p _ hp, h _ hp⟩)
end

protected lemma exists_is_lub (s : set ennreal) : ∃x, is_lub s x :=
by_cases (assume h : s = ∅, ⟨0, by simp [h, is_lub, is_least, lower_bounds, upper_bounds]⟩) $
  assume h : s ≠ ∅,
  let ⟨x, hx⟩ := exists_mem_of_ne_empty h in
  by_cases
    (assume : ∃r, 0 ≤ r ∧ of_real r ∈ upper_bounds s,
      let ⟨r, hr, hb⟩ := this in
      let s' := of_real ⁻¹' s ∩ {x | 0 ≤ x} in
      have s'_nn : ∀x∈s', (0:real) ≤ x, from assume x h, h.right,
      have s_eq : s = of_real '' s',
        from set.ext $ assume a, ⟨assume ha,
          let ⟨q, hq₁, hq₂, hq₃⟩ := (le_of_real_iff hr).mp (hb _ ha) in
          ⟨q, ⟨show of_real q ∈ s, from hq₃ ▸ ha, hq₁⟩, hq₃ ▸ rfl⟩,
          assume ⟨r, ⟨hr₁, hr₂⟩, hr₃⟩, hr₃ ▸ hr₁⟩,
      have x ∈ of_real '' s', from s_eq ▸ hx,
      let ⟨x', hx', hx'_eq⟩ := this in
      have ∃x, is_lub s' x, from exists_supremum_real ‹x' ∈ s'› $
        (of_real_mem_upper_bounds s'_nn hr).mp $ s_eq ▸ hb,
      let ⟨x, hx⟩ := this in
      have 0 ≤ x, from le_trans hx'.right $ hx.left _ hx',
      ⟨of_real x, by rwa [s_eq, is_lub_of_real s'_nn this]; exact ne_empty_of_mem hx'⟩)
    begin
      intro h,
      existsi ∞,
      simp [is_lub, is_least, lower_bounds, forall_ennreal, not_exists, not_and] at h ⊢,
      assumption
    end

instance : has_Sup ennreal := ⟨λs, some (ennreal.exists_is_lub s)⟩

protected lemma is_lub_Sup {s : set ennreal} : is_lub s (Sup s) :=
some_spec _

protected lemma le_Sup {s : set ennreal} : a ∈ s → a ≤ Sup s :=
ennreal.is_lub_Sup.left a

protected lemma Sup_le {s : set ennreal} : (∀b ∈ s, b ≤ a) → Sup s ≤ a :=
ennreal.is_lub_Sup.right _

instance : complete_linear_order ennreal :=
{ ennreal.decidable_linear_order with
  top := ∞,
  bot := 0,
  inf := min,
  sup := max,
  Sup := Sup,
  Inf := λs, Sup {a | ∀b ∈ s, a ≤ b},
  le_top       := assume a, le_infty,
  bot_le       := assume a, ennreal.zero_le,
  le_sup_left  := le_max_left,
  le_sup_right := le_max_right,
  sup_le       := assume a b c, max_le,
  inf_le_left  := min_le_left,
  inf_le_right := min_le_right,
  le_inf       := assume a b c, le_min,
  le_Sup       := assume s a, ennreal.le_Sup,
  Sup_le       := assume s a, ennreal.Sup_le,
  le_Inf       := assume s a h, ennreal.le_Sup h,
  Inf_le       := assume s a ha, ennreal.Sup_le $ assume b hb, hb _ ha }

protected lemma bot_eq_zero : (⊥ : ennreal) = 0 := rfl

lemma Inf_add {s : set ennreal} : Inf s + a = ⨅b∈s, b + a :=
le_antisymm
  (le_infi $ assume b, le_infi $ assume hb, ennreal.add_le_add (Inf_le hb) (le_refl a))
  (le_of_forall_ge $ assume c hc,
    match le_total a c with
    | or.inl h :=
      let ⟨d, hd⟩ := ennreal.le_iff_exists_add.mp h in
      have ∀b∈s, d ≤ b,
        from assume b hb,
        have a + d < a + b,
          from calc a + d = c : by simp [hd]
            ... < ⨅b∈s, b + a : hc
            ... ≤ a + b : infi_le_of_le b $ infi_le_of_le hb $ by simp,
        le_of_lt $ lt_of_add_lt_add_left this,
      by rw [hd, add_comm]; exact ennreal.add_le_add (le_refl a) (le_Inf this)
    | or.inr h := le_add_left h
    end)

lemma Sup_add {s : set ennreal} (hs : s ≠ ∅) : Sup s + a = ⨆b∈s, b + a :=
eq_of_le_of_forall_ge
  (supr_le $ assume b, supr_le $ assume hb, ennreal.add_le_add (le_Sup hb) (le_refl _))
  (assume b hb, match le_total a b with
  | or.inl h :=
    let ⟨c, hc⟩ := ennreal.le_iff_exists_add.mp h in
    have a + c < a + Sup s, by simp [hc] at hb; simp [hb],
    let ⟨x, hx, h⟩ := lt_Sup_iff.mp $ lt_of_add_lt_add_left this in
    le_supr_of_le x $ le_supr_of_le hx $
      by rw [hc, add_comm]; exact add_le_add (le_of_lt h) (le_refl a)
  | or.inr h := let ⟨x, hx⟩ := exists_mem_of_ne_empty hs in
    le_supr_of_le x $ le_supr_of_le hx $ le_add_left h
  end)

end complete_lattice

section topological_space

instance : topological_space ennreal :=
topological_space.generate_from {s | ∃a, s = {b | a < b} ∨ s = {b | b < a}}

instance : orderable_topology ennreal := ⟨rfl⟩
instance : t2_space ennreal := by apply_instance

lemma continuous_of_real : continuous of_real :=
have ∀x:ennreal, is_open {a : ℝ | x < of_real a},
  from forall_ennreal.mpr ⟨assume r hr,
    begin
      simp [of_real_lt_of_real_iff_cases],
      exact is_open_and
        (is_open_lt continuous_const continuous_id)
        (is_open_lt continuous_const continuous_id)
    end,
    by simp⟩,
have ∀x:ennreal, is_open {a : ℝ | of_real a < x},
  from forall_ennreal.mpr ⟨assume r hr,
    begin
      simp [of_real_lt_of_real_iff_cases],
      exact is_open_and (is_open_lt continuous_id continuous_const) is_open_const
    end,
    by simp [is_open_const]⟩,
continuous_generated_from $ begin simp [or_imp_distrib, *] {contextual := tt} end

/- TODO:
lemma nhds_of_real_eq_map_of_real_nhds {r : ℝ} (hr : 0 ≤ r) :
  nhds (of_real r) = (nhds r ⊓ principal {x | 0 ≤ x}).map of_real :=
le_antisymm
  _
  _

instance : topological_add_monoid ennreal :=
have ∀a₁ a₂ : ennreal, tendsto (λp:ennreal×ennreal, p.1 + p.2) (nhds (a₁, a₂)) (nhds (a₁ + a₂)),
  from forall_ennreal.mpr ⟨_, _⟩,
⟨continuous_iff_tendsto.mpr $
  assume ⟨a₁, a₂⟩,
  begin simp [nhds_prod_eq] end⟩
-/

end topological_space

section sub
instance : has_sub ennreal := ⟨λa b, Inf {d | a ≤ d + b}⟩

@[simp] lemma sub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
le_antisymm (Inf_le $ le_add_left h) ennreal.zero_le

@[simp] lemma sub_add_cancel_of_le (h : b ≤ a) : (a - b) + b = a :=
let ⟨c, hc⟩ := ennreal.le_iff_exists_add.mp h in
eq.trans Inf_add $ le_antisymm
  (infi_le_of_le c $ infi_le_of_le (by simp [hc]) $ by simp [hc])
  (le_infi $ assume d, le_infi $ assume hd, hd)

@[simp] lemma add_sub_cancel_of_le (h : b ≤ a) : b + (a - b) = a :=
by rwa [add_comm, sub_add_cancel_of_le]

lemma sub_add_self_eq_max : (a - b) + b = max a b :=
match le_total a b with
| or.inl h := by simp [h, max_eq_right]
| or.inr h := by simp [h, max_eq_left]
end

lemma sub_le_sub (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
Inf_le_Inf $ assume e (h : b ≤ e + d),
  calc a ≤ b : h₁
    ... ≤ e + d : h
    ... ≤ e + c : add_le_add (le_refl _) h₂

@[simp] lemma le_sub_iff_add_le : a - b ≤ c ↔ a ≤ c + b :=
iff.intro
  (assume h : a - b ≤ c,
    calc a ≤ (a - b) + b : by rw [sub_add_self_eq_max]; exact le_max_left _ _
      ... ≤ c + b : add_le_add h (le_refl _))
  (assume h : a ≤ c + b,
    calc a - b ≤ (c + b) - b : sub_le_sub h (le_refl _)
      ... ≤ c : Inf_le (le_refl (c + b)))

@[simp] lemma zero_sub : 0 - a = 0 :=
le_antisymm (Inf_le ennreal.zero_le) ennreal.zero_le

@[simp] lemma sub_infty : a - ∞ = 0 :=
le_antisymm (Inf_le le_infty) ennreal.zero_le

@[simp] lemma sub_zero : a - 0 = a :=
eq.trans (add_zero (a - 0)).symm $ by simp

end sub

section inv
instance : has_inv ennreal := ⟨λa, Inf {b | 1 ≤ a * b}⟩
instance : has_div ennreal := ⟨λa b, a * b⁻¹⟩

@[simp] lemma inv_zero : (0 : ennreal)⁻¹ = ∞ :=
show Inf {b : ennreal | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_infty : (∞ : ennreal)⁻¹ = 0 :=
bot_unique $ le_of_forall_le $ assume a (h : a > 0),
  have a ≠ 0, from ne_of_gt h,
  Inf_le $ by simp [*]

@[simp] lemma inv_of_real (hr : 0 < r) : (of_real r)⁻¹ = of_real (r⁻¹) :=
have 0 < r⁻¹, from inv_pos hr,
have r ≠ 0, from ne_of_gt hr,
have 0 ≤ r, from le_of_lt hr,
le_antisymm
  (Inf_le $ by simp [*, le_of_lt, mul_inv_cancel])
  (le_Inf $ forall_ennreal.mpr $ and.intro
    begin
      intros p hp,
      have : 0 ≤ r * p, from mul_nonneg ‹0 ≤ r› hp,
      simp [*, le_of_lt] {contextual := tt},
      rw [inv_eq_one_div, div_le_iff_le_mul_of_pos hr],
      simp
    end
    (assume h, le_top))

lemma inv_inv : ∀{a:ennreal}, (a⁻¹)⁻¹ = a :=
forall_ennreal.mpr $ and.intro
  (assume r hr, by_cases
    (assume : r = 0, by simp [this])
    (assume : r ≠ 0,
      have 0 < r, from lt_of_le_of_ne hr this.symm,
      by simp [*, inv_pos, inv_inv']))
  (by simp)

end inv

end ennreal

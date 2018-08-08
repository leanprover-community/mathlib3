/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals

TODO: base ennreal on nnreal!
-/
import data.real.basic order.bounds
noncomputable theory
open classical set lattice
local attribute [instance] prop_decidable
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
inductive ennreal : Type
| of_nonneg_real : Πr:real, 0 ≤ r → ennreal
| infinity : ennreal

local notation `∞` := ennreal.infinity

namespace ennreal
variables {a b c d : ennreal} {r p q : ℝ}

section projections

/-- `of_real r` is the nonnegative extended real number `r` if `r` is nonnegative,
  otherwise 0. -/
def of_real (r : ℝ) : ennreal := of_nonneg_real (max 0 r) (le_max_left 0 r)

/-- `of_ennreal x` returns `x` if it is real, otherwise 0. -/
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
instance : inhabited ennreal := ⟨0⟩

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

@[simp] lemma of_real_add (hr : 0 ≤ r) (hq : 0 ≤ p) :
  of_real r + of_real p = of_real (r + p) :=
by simp [of_real, max, hr, hq, add_comm]; refl

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
{ zero := 0,
  add  := (+),
  add_zero := forall_ennreal.2 ⟨λ a ha,
    by rw [← of_real_zero, of_real_add ha (le_refl _), add_zero], by simp⟩,
  zero_add := forall_ennreal.2 ⟨λ a ha,
    by rw [← of_real_zero, of_real_add (le_refl _) ha, zero_add], by simp⟩,
  add_comm := begin
    refine forall_ennreal.2 ⟨λ a ha, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ b hb, _, by simp⟩,
    rw [of_real_add ha hb, of_real_add hb ha, add_comm]
  end,
  add_assoc := begin
    refine forall_ennreal.2 ⟨λ a ha, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ b hb, _, by simp⟩,
    refine forall_ennreal.2 ⟨λ c hc, _, by simp⟩,
    rw [of_real_add ha hb, of_real_add (add_nonneg ha hb) hc,
        of_real_add hb hc, of_real_add ha (add_nonneg hb hc), add_assoc],
  end }

@[simp] lemma sum_of_real {α : Type*} {s : finset α} {f : α → ℝ} :
  (∀a∈s, 0 ≤ f a) → s.sum (λa, of_real (f a)) = of_real (s.sum f) :=
finset.induction_on s (by simp) $ assume a s has ih h,
  have 0 ≤ s.sum f, from finset.zero_le_sum $ assume a ha, h a $ finset.mem_insert_of_mem ha,
  by simp [has, *] {contextual := tt}

protected lemma mul_zero : ∀a:ennreal, a * 0 = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_comm : ∀a b:ennreal, a * b = b * a :=
by simp [forall_ennreal, mul_comm] {contextual := tt}

protected lemma zero_mul : ∀a:ennreal, 0 * a = 0 :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual := tt}

protected lemma mul_assoc : ∀a b c:ennreal, a * b * c = a * (b * c) :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ha' : ra = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul, mul_assoc] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases hc' : rc = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases hb' : rc = 0;
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp *
end

protected lemma left_distrib : ∀a b c:ennreal, a * (b + c) = a * b + a * c :=
begin
  rw [forall_ennreal], constructor,
  { intros ra ha,
    by_cases ha' : ra = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rb hrb,
      by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
      rw [forall_ennreal], constructor,
      { intros rc hrc, simp [*, zero_le_mul, add_nonneg, left_distrib] },
      simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
    rw [forall_ennreal], constructor,
      { intros rc hrc,
        by_cases hv' : rc = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
        simp [*, zero_le_mul] },
    simp [*] },
  rw [forall_ennreal], constructor,
  { intros rb hrb,
    by_cases hb' : rb = 0, simp [*, ennreal.mul_zero, ennreal.zero_mul],
    rw [forall_ennreal], constructor,
    { intros rc hrc,
      by_cases hb' : rc = 0;
        simp [*, zero_le_mul, ennreal.mul_zero, mul_eq_zero_iff_eq_zero_or_eq_zero, add_nonneg,
          add_eq_zero_iff_eq_zero_and_eq_zero_of_nonneg_of_nonneg] },
    simp [*, zero_le_mul, mul_eq_zero_iff_eq_zero_or_eq_zero] },
  intro c, by_cases c = 0; simp [*]
end

instance : comm_semiring ennreal :=
{ one  := 1,
  mul  := (*),
  mul_zero := ennreal.mul_zero,
  zero_mul := ennreal.zero_mul,
  one_mul := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_one := by simp [forall_ennreal, -of_real_one, of_real_one.symm, zero_le_one] {contextual := tt},
  mul_comm := ennreal.mul_comm,
  mul_assoc := ennreal.mul_assoc,
  left_distrib := ennreal.left_distrib,
  right_distrib := assume a b c, by rw [ennreal.mul_comm, ennreal.left_distrib,
    ennreal.mul_comm, ennreal.mul_comm b c]; refl,
  ..ennreal.add_comm_monoid }

end semiring

section order

instance : has_le ennreal := ⟨λ a b, b = ∞ ∨ (∃r p, 0 ≤ r ∧ r ≤ p ∧ a = of_real r ∧ b = of_real p)⟩

theorem le_def : a ≤ b ↔ b = ∞ ∨ (∃r p, 0 ≤ r ∧ r ≤ p ∧ a = of_real r ∧ b = of_real p) := iff.rfl

@[simp] lemma infty_le_iff : ∞ ≤ a ↔ a = ∞ :=
by simp [le_def]

@[simp] lemma le_infty : a ≤ ∞ :=
by simp [le_def]

@[simp] lemma of_real_le_of_real_iff (hr : 0 ≤ r) (hp : 0 ≤ p) :
  of_real r ≤ of_real p ↔ r ≤ p :=
by simpa [le_def] using show (∃ (r' : ℝ), 0 ≤ r' ∧ ∃ (q : ℝ), r' ≤ q ∧
  of_real r = of_real r' ∧ of_real p = of_real q) ↔ r ≤ p, from
⟨λ ⟨r', hr', q, hrq, h₁, h₂⟩,
  by simp [hr, hr', le_trans hr' hrq, hp] at h₁ h₂; simp *,
 λ h, ⟨r, hr, p, h, rfl, rfl⟩⟩

@[simp] lemma one_le_of_real_iff (hr : 0 ≤ r) : 1 ≤ of_real r ↔ 1 ≤ r :=
of_real_le_of_real_iff zero_le_one hr

instance : decidable_linear_order ennreal :=
{ le           := (≤),
  le_refl      := by simp [forall_ennreal, le_refl] {contextual := tt},
  le_trans     := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb c hc, le_trans,
  le_antisymm  := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_antisymm,
  le_total     := by simp [forall_ennreal] {contextual := tt}; exact assume a ha b hb, le_total _ _,
  decidable_le := by apply_instance }

@[simp] lemma not_infty_lt : ¬ ∞ < a :=
by simp

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
by simp [lt_iff_le_not_le, -not_le] {contextual:=tt}

lemma lt_iff_exists_of_real : ∀{a b}, a < b ↔ (∃p, 0 ≤ p ∧ a = of_real p ∧ of_real p < b) :=
by simp [forall_ennreal]; exact λ r hr,
⟨λ p hp, ⟨λ h, ⟨r, by simp *⟩, λ ⟨q, h₁, h₂, h₃⟩, by simp * at *⟩, r, hr, rfl⟩

@[simp] protected lemma zero_le : ∀{a:ennreal}, 0 ≤ a :=
by simp [forall_ennreal, -of_real_zero, of_real_zero.symm] {contextual:=tt}

@[simp] lemma le_zero_iff_eq : a ≤ 0 ↔ a = 0 :=
⟨assume h, le_antisymm h ennreal.zero_le, assume h, h ▸ le_refl a⟩

@[simp] lemma zero_lt_of_real_iff : 0 < of_real p ↔ 0 < p :=
by_cases
  (assume : 0 ≤ p, of_real_lt_of_real_iff (le_refl _) this)
  (by simp [lt_irrefl, not_imp_not, le_of_lt, of_real_of_not_nonneg] {contextual := tt})

@[simp] lemma not_lt_zero : ¬ a < 0 :=
by simp

protected lemma zero_lt_one : 0 < (1 : ennreal) :=
zero_lt_of_real_iff.mpr zero_lt_one

lemma of_real_le_of_real (h : r ≤ p) : of_real r ≤ of_real p :=
match le_total 0 r with
| or.inl hr := (of_real_le_of_real_iff hr $ le_trans hr h).mpr h
| or.inr hr := by simp [of_real_of_nonpos, hr, zero_le]
end

lemma of_real_lt_of_real_iff_cases : of_real r < of_real p ↔ 0 < p ∧ r < p :=
begin
  by_cases hp : 0 ≤ p,
  { by_cases hr : 0 ≤ r,
    { simp [*, iff_def] {contextual := tt},
      show r < p → 0 < p, from lt_of_le_of_lt hr },
    { have h : r ≤ 0, from le_of_lt (lt_of_not_ge hr),
      simp [*, of_real_of_not_nonneg, and_iff_left_of_imp (lt_of_le_of_lt h)] } },
  simp [*, not_le, not_lt, le_of_lt, of_real_of_not_nonneg, and_comm] at *
end

instance : densely_ordered ennreal :=
⟨by simp [forall_ennreal, of_real_lt_of_real_iff_cases]; exact
λ r hr, ⟨λ p _ _ h,
  let ⟨q, h₁, h₂⟩ := dense h in
  have 0 ≤ q, from le_trans hr $ le_of_lt h₁,
  ⟨of_real q, by simp *⟩,
of_real (r + 1), by simp [hr, add_nonneg, lt_add_of_le_of_pos, zero_le_one, zero_lt_one]⟩⟩

private lemma add_le_add : ∀{b d}, a ≤ b → c ≤ d → a + c ≤ b + d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, add_nonneg, add_le_add] {contextual := tt}, by simp⟩, by simp⟩

private lemma lt_of_add_lt_add_left (h : a + b < a + c) : b < c :=
lt_of_not_ge $ assume h', lt_irrefl (a + b) (lt_of_lt_of_le h $ add_le_add (le_refl a) h')

instance : ordered_comm_monoid ennreal :=
{ add_le_add_left       := assume a b h c, add_le_add (le_refl c) h,
  lt_of_add_lt_add_left := assume a b c, lt_of_add_lt_add_left,
  ..ennreal.add_comm_monoid, ..ennreal.decidable_linear_order }

lemma le_add_left (h : a ≤ c) : a ≤ b + c :=
calc a = 0 + a : by simp
  ... ≤ b + c : add_le_add ennreal.zero_le h

lemma le_add_right (h : a ≤ b) : a ≤ b + c :=
calc a = a + 0 : by simp
  ... ≤ b + c : add_le_add h ennreal.zero_le

lemma lt_add_right : ∀{a b}, a < ∞ → 0 < b → a < a + b :=
by simp [forall_ennreal, of_real_lt_of_real_iff, add_nonneg, lt_add_of_le_of_pos] {contextual := tt}

instance : canonically_ordered_monoid ennreal :=
{ le_iff_exists_add := by simp [forall_ennreal] {contextual:=tt}; exact
    λ r hr, ⟨λ p hp,
      ⟨λ h, ⟨of_real (p - r),
        by rw [of_real_add (sub_nonneg.2 h) hr, sub_add_cancel]⟩,
      λ ⟨c, hc⟩, by rw [← of_real_le_of_real_iff hr hp, hc]; exact le_add_left (le_refl _)⟩,
    ⟨∞, by simp⟩⟩,
  ..ennreal.ordered_comm_monoid }

lemma of_real_add_le : of_real (r + p) ≤ of_real r + of_real p :=
show of_nonneg_real _ _ ≤ of_real _,
by rw of_nonneg_real_eq_of_real; exact
of_real_le_of_real
  (max_le (add_nonneg (le_max_left _ _) (le_max_left _ _))
    (add_le_add (le_max_right _ _) (le_max_right _ _)))

lemma mul_le_mul : ∀{b d}, a ≤ b → c ≤ d → a * c ≤ b * d :=
forall_ennreal.mpr ⟨assume r hr, forall_ennreal.mpr ⟨assume p hp,
  by simp [le_of_real_iff, *, exists_imp_distrib, -and_imp] {contextual:=tt};
    simp [*, zero_le_mul, mul_le_mul] {contextual := tt},
    by by_cases r = 0; simp [*] {contextual:=tt}⟩,
    assume d, by by_cases d = 0; simp [*] {contextual:=tt}⟩

lemma le_of_forall_epsilon_le (h : ∀ε>0, b < ∞ → a ≤ b + of_real ε) : a ≤ b :=
suffices ∀r, 0 ≤ r → of_real r > b → a ≤ of_real r,
  from le_of_forall_le_of_dense $ forall_ennreal.mpr $ by simp; assumption,
assume r hr hrb,
let ⟨p, hp, b_eq, hpr⟩ := lt_iff_exists_of_real.mp hrb in
have p < r, by simp [hp, hr] at hpr; assumption,
have pos : 0 < r - p, from lt_sub_iff_add_lt.mpr $ by simp [this],
calc a ≤ b + of_real (r - p) : h _ pos (by simp [b_eq])
  ... = of_real r :
    by simp [-sub_eq_add_neg, le_of_lt pos, hp, hr, b_eq]; simp [sub_eq_add_neg]

protected lemma lt_iff_exists_rat_btwn :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < of_real q ∧ of_real q < b) :=
⟨λ h, by
  rcases lt_iff_exists_of_real.1 h with ⟨p, p0, rfl, _⟩;
  rcases dense h with ⟨c, pc, cb⟩;
  rcases lt_iff_exists_of_real.1 cb with ⟨r, r0, rfl, _⟩;
  rcases exists_rat_btwn ((of_real_lt_of_real_iff p0 r0).1 pc) with ⟨q, pq, qr⟩;
  have q0 := le_trans p0 (le_of_lt pq); exact
  ⟨q, rat.cast_nonneg.1 q0, (of_real_lt_of_real_iff p0 q0).2 pq,
    lt_trans ((of_real_lt_of_real_iff q0 r0).2 qr) cb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

end order

section complete_lattice

@[simp] lemma infty_mem_upper_bounds {s : set ennreal} : ∞ ∈ upper_bounds s :=
assume x hx, le_infty

lemma of_real_mem_upper_bounds {s : set real} (hs : ∀x∈s, (0:real) ≤ x) (hr : 0 ≤ r) :
  of_real r ∈ upper_bounds (of_real '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

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
      have is_lub s' (Sup s'), from real.is_lub_Sup ‹x' ∈ s'› $
        (of_real_mem_upper_bounds s'_nn hr).mp $ s_eq ▸ hb,
      have 0 ≤ Sup s', from le_trans hx'.right $ this.left _ hx',
      ⟨of_real (Sup s'), by rwa [s_eq, is_lub_of_real s'_nn this]; exact ne_empty_of_mem hx'⟩)
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
{ top := ∞,
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
  Inf_le       := assume s a ha, ennreal.Sup_le $ assume b hb, hb _ ha,
  ..ennreal.decidable_linear_order }

@[simp] protected lemma bot_eq_zero : (⊥ : ennreal) = 0 := rfl
@[simp] protected lemma top_eq_infty : (⊤ : ennreal) = ∞ := rfl

end complete_lattice

section sub
instance : has_sub ennreal := ⟨λa b, Inf {d | a ≤ d + b}⟩

@[simp] lemma sub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
le_antisymm (Inf_le $ le_add_left h) ennreal.zero_le

lemma sub_le_sub (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
Inf_le_Inf $ assume e (h : b ≤ e + d),
  calc a ≤ b : h₁
    ... ≤ e + d : h
    ... ≤ e + c : add_le_add (le_refl _) h₂

@[simp] lemma zero_sub : 0 - a = 0 :=
le_antisymm (Inf_le ennreal.zero_le) ennreal.zero_le

@[simp] lemma sub_infty : a - ∞ = 0 :=
le_antisymm (Inf_le le_infty) ennreal.zero_le

@[simp] lemma infty_sub_of_real (hr : 0 ≤ r) : ∞ - of_real r = ∞ :=
top_unique $ le_Inf $ by simp [forall_ennreal, hr] {contextual := tt}; refl

@[simp] lemma of_real_sub_of_real (hr : 0 ≤ r) : of_real p - of_real r = of_real (p - r) :=
match le_total p r with
| or.inr h :=
  have 0 ≤ p - r, from le_sub_iff_add_le.mpr $ by simp [h],
  have eq : r + (p - r) = p, by rw [add_comm, sub_add_cancel],
  le_antisymm
    (Inf_le $ by simp [-sub_eq_add_neg, this, hr, le_trans hr h, eq, le_refl])
    (le_Inf $
      by simp [forall_ennreal, hr, le_trans hr h, add_nonneg, -sub_eq_add_neg,
        this, sub_le_iff_le_add]
        {contextual := tt})
| or.inl h :=
  begin
    rw [sub_eq_zero_of_le, of_real_of_nonpos],
    { rw [sub_le_iff_le_add], simp [h] },
    { exact of_real_le_of_real h }
  end
end

@[simp] lemma add_sub_self : ∀{a b : ennreal}, b < ∞ → (a + b) - b = a :=
by simp [forall_ennreal] {contextual:=tt}

@[simp] lemma add_sub_self' (h : a < ∞) : (a + b) - a = b :=
by rw [add_comm, add_sub_self h]

lemma add_left_inj (h : a < ∞) : a + b = a + c ↔ b = c :=
⟨λ e, by simpa [h] using congr_arg (λ x, x - a) e, congr_arg _⟩

lemma add_right_inj (h : a < ∞) : b + a = c + a ↔ b = c :=
by rw [add_comm, add_comm c, add_left_inj h]

@[simp] lemma sub_add_cancel_of_le (h : b ≤ a) : (a - b) + b = a :=
begin
  revert a b,
  simp [forall_ennreal] {contextual := tt},
  intros r r0 p p0 pr,
  rw of_real_add p0, {simp},
  exact sub_nonneg.2 pr
end

@[simp] lemma add_sub_cancel_of_le (h : b ≤ a) : b + (a - b) = a :=
by rwa [add_comm, sub_add_cancel_of_le]

lemma sub_add_self_eq_max : (a - b) + b = max a b :=
match le_total a b with
| or.inl h := by simp [h, max_eq_right]
| or.inr h := by simp [h, max_eq_left]
end

@[simp] protected lemma sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b :=
iff.intro
  (assume h : a - b ≤ c,
    calc a ≤ (a - b) + b : by rw [sub_add_self_eq_max]; exact le_max_left _ _
      ... ≤ c + b : add_le_add h (le_refl _))
  (assume h : a ≤ c + b,
    calc a - b ≤ (c + b) - b : sub_le_sub h (le_refl _)
      ... ≤ c : Inf_le (le_refl (c + b)))

lemma sub_le_self (a b : ennreal) : a - b ≤ a :=
ennreal.sub_le_iff_le_add.2 $ le_add_of_nonneg_right' $ zero_le _

@[simp] lemma sub_zero : a - 0 = a :=
eq.trans (add_zero (a - 0)).symm $ by simp

lemma sub_sub_cancel (h : a < ∞) (h2 : b ≤ a) : a - (a - b) = b :=
by rw [← add_right_inj (lt_of_le_of_lt (sub_le_self _ _) h),
  sub_add_cancel_of_le (sub_le_self _ _), add_sub_cancel_of_le h2]

end sub

section inv
instance : has_inv ennreal := ⟨λa, Inf {b | 1 ≤ a * b}⟩
instance : has_div ennreal := ⟨λa b, a * b⁻¹⟩

@[simp] lemma inv_zero : (0 : ennreal)⁻¹ = ∞ :=
show Inf {b : ennreal | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_infty : (∞ : ennreal)⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h]

@[simp] lemma inv_of_real (hr : 0 < r) : (of_real r)⁻¹ = of_real (r⁻¹) :=
have 0 ≤ r⁻¹, from le_of_lt (inv_pos hr),
have r0 : 0 ≤ r, from le_of_lt hr,
le_antisymm
  (Inf_le $ by simp [*, inv_pos hr, mul_inv_cancel (ne_of_gt hr)])
  (le_Inf $ forall_ennreal.mpr ⟨λ p hp,
    by simp [*, show 0 ≤ r*p, from mul_nonneg r0 hp];
       intro; rwa [inv_eq_one_div, div_le_iff hr, mul_comm],
    λ h, le_top⟩)

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

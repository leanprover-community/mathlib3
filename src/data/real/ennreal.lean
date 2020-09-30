/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Yury Kudryashov

Extended non-negative reals
-/
import data.real.nnreal
import data.set.intervals
noncomputable theory
open classical set

open_locale classical big_operators
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
@[derive canonically_ordered_comm_semiring, derive complete_linear_order, derive densely_ordered]
def ennreal := with_top nnreal

localized "notation `∞` := (⊤ : ennreal)" in ennreal

namespace ennreal
variables {a b c d : ennreal} {r p q : nnreal}

instance : inhabited ennreal := ⟨0⟩

instance : has_coe nnreal ennreal := ⟨ option.some ⟩

instance : can_lift ennreal nnreal :=
{ coe := coe,
  cond := λ r, r ≠ ∞,
  prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }

@[simp] lemma none_eq_top : (none : ennreal) = (⊤ : ennreal) := rfl
@[simp] lemma some_eq_coe (a : nnreal) : (some a : ennreal) = (↑a : ennreal) := rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def to_nnreal : ennreal → nnreal
| (some r) := r
| none := 0

/-- `to_real x` returns `x` if it is real, `0` otherwise. -/
protected def to_real (a : ennreal) : real := coe (a.to_nnreal)

/-- `of_real x` returns `x` if it is nonnegative, `0` otherwise. -/
protected def of_real (r : real) : ennreal := coe (nnreal.of_real r)

@[simp, norm_cast] lemma to_nnreal_coe : (r : ennreal).to_nnreal = r := rfl

@[simp] lemma coe_to_nnreal : ∀{a:ennreal}, a ≠ ∞ → ↑(a.to_nnreal) = a
| (some r) h := rfl
| none     h := (h rfl).elim

@[simp] lemma of_real_to_real {a : ennreal} (h : a ≠ ∞) : ennreal.of_real (a.to_real) = a :=
by simp [ennreal.to_real, ennreal.of_real, h]

@[simp] lemma to_real_of_real {r : ℝ} (h : 0 ≤ r) : ennreal.to_real (ennreal.of_real r) = r :=
by simp [ennreal.to_real, ennreal.of_real, nnreal.coe_of_real _ h]

lemma to_real_of_real' {r : ℝ} : ennreal.to_real (ennreal.of_real r) = max r 0 := rfl

lemma coe_to_nnreal_le_self : ∀{a:ennreal}, ↑(a.to_nnreal) ≤ a
| (some r) := by rw [some_eq_coe, to_nnreal_coe]; exact le_refl _
| none     := le_top

lemma coe_nnreal_eq (r : nnreal) : (r : ennreal) = ennreal.of_real r :=
by { rw [ennreal.of_real, nnreal.of_real], cases r with r h, congr, dsimp, rw max_eq_left h }

lemma of_real_eq_coe_nnreal {x : ℝ} (h : 0 ≤ x) :
  ennreal.of_real x = @coe nnreal ennreal _ (⟨x, h⟩ : nnreal) :=
by { rw [coe_nnreal_eq], refl }

@[simp] lemma of_real_coe_nnreal : ennreal.of_real p = p := (coe_nnreal_eq p).symm

@[simp, norm_cast] lemma coe_zero : ↑(0 : nnreal) = (0 : ennreal) := rfl
@[simp, norm_cast] lemma coe_one : ↑(1 : nnreal) = (1 : ennreal) := rfl

@[simp] lemma to_real_nonneg {a : ennreal} : 0 ≤ a.to_real := by simp [ennreal.to_real]

@[simp] lemma top_to_nnreal : ∞.to_nnreal = 0 := rfl
@[simp] lemma top_to_real : ∞.to_real = 0 := rfl
@[simp] lemma one_to_real : (1 : ennreal).to_real = 1 := rfl
@[simp] lemma one_to_nnreal : (1 : ennreal).to_nnreal = 1 := rfl
@[simp] lemma coe_to_real (r : nnreal) : (r : ennreal).to_real = r := rfl
@[simp] lemma zero_to_nnreal : (0 : ennreal).to_nnreal = 0 := rfl
@[simp] lemma zero_to_real : (0 : ennreal).to_real = 0 := rfl
@[simp] lemma of_real_zero : ennreal.of_real (0 : ℝ) = 0 :=
by simp [ennreal.of_real]; refl
@[simp] lemma of_real_one : ennreal.of_real (1 : ℝ) = (1 : ennreal) :=
by simp [ennreal.of_real]

lemma of_real_to_real_le {a : ennreal} : ennreal.of_real (a.to_real) ≤ a :=
if ha : a = ∞ then ha.symm ▸ le_top else le_of_eq (of_real_to_real ha)

lemma forall_ennreal {p : ennreal → Prop} : (∀a, p a) ↔ (∀r:nnreal, p r) ∧ p ∞ :=
⟨assume h, ⟨assume r, h _, h _⟩,
  assume ⟨h₁, h₂⟩ a, match a with some r := h₁ _ | none := h₂ end⟩

lemma to_nnreal_eq_zero_iff (x : ennreal) : x.to_nnreal = 0 ↔ x = 0 ∨ x = ⊤ :=
⟨begin
  cases x,
  { simp [none_eq_top] },
  { have A : some (0:nnreal) = (0:ennreal) := rfl,
    simp [ennreal.to_nnreal, A] {contextual := tt} }
end,
by intro h; cases h; simp [h]⟩

lemma to_real_eq_zero_iff (x : ennreal) : x.to_real = 0 ↔ x = 0 ∨ x = ⊤ :=
by simp [ennreal.to_real, to_nnreal_eq_zero_iff]

@[simp] lemma coe_ne_top : (r : ennreal) ≠ ∞ := with_top.coe_ne_top
@[simp] lemma top_ne_coe : ∞ ≠ (r : ennreal) := with_top.top_ne_coe
@[simp] lemma of_real_ne_top {r : ℝ} : ennreal.of_real r ≠ ∞ := by simp [ennreal.of_real]
@[simp] lemma of_real_lt_top {r : ℝ} : ennreal.of_real r < ∞ := lt_top_iff_ne_top.2 of_real_ne_top
@[simp] lemma top_ne_of_real {r : ℝ} : ∞ ≠ ennreal.of_real r := by simp [ennreal.of_real]

@[simp] lemma zero_ne_top : 0 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_zero : ∞ ≠ 0 := top_ne_coe

@[simp] lemma one_ne_top : 1 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_one : ∞ ≠ 1 := top_ne_coe

@[simp, norm_cast] lemma coe_eq_coe : (↑r : ennreal) = ↑q ↔ r = q := with_top.coe_eq_coe
@[simp, norm_cast] lemma coe_le_coe : (↑r : ennreal) ≤ ↑q ↔ r ≤ q := with_top.coe_le_coe
@[simp, norm_cast] lemma coe_lt_coe : (↑r : ennreal) < ↑q ↔ r < q := with_top.coe_lt_coe
lemma coe_mono : monotone (coe : nnreal → ennreal) := λ _ _, coe_le_coe.2

@[simp, norm_cast] lemma coe_eq_zero : (↑r : ennreal) = 0 ↔ r = 0 := coe_eq_coe
@[simp, norm_cast] lemma zero_eq_coe : 0 = (↑r : ennreal) ↔ 0 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_eq_one : (↑r : ennreal) = 1 ↔ r = 1 := coe_eq_coe
@[simp, norm_cast] lemma one_eq_coe : 1 = (↑r : ennreal) ↔ 1 = r := coe_eq_coe
@[simp, norm_cast] lemma coe_nonneg : 0 ≤ (↑r : ennreal) ↔ 0 ≤ r := coe_le_coe
@[simp, norm_cast] lemma coe_pos : 0 < (↑r : ennreal) ↔ 0 < r := coe_lt_coe

@[simp, norm_cast] lemma coe_add : ↑(r + p) = (r + p : ennreal) := with_top.coe_add
@[simp, norm_cast] lemma coe_mul : ↑(r * p) = (r * p : ennreal) := with_top.coe_mul

@[simp, norm_cast] lemma coe_bit0 : (↑(bit0 r) : ennreal) = bit0 r := coe_add
@[simp, norm_cast] lemma coe_bit1 : (↑(bit1 r) : ennreal) = bit1 r := by simp [bit1]
lemma coe_two : ((2:nnreal) : ennreal) = 2 := by norm_cast

protected lemma zero_lt_one : 0 < (1 : ennreal) :=
  canonically_ordered_semiring.zero_lt_one

@[simp] lemma one_lt_two : (1:ennreal) < 2 := coe_one ▸ coe_two ▸ by exact_mod_cast one_lt_two
@[simp] lemma zero_lt_two : (0:ennreal) < 2 := lt_trans ennreal.zero_lt_one one_lt_two
lemma two_ne_zero : (2:ennreal) ≠ 0 := (ne_of_lt zero_lt_two).symm
lemma two_ne_top : (2:ennreal) ≠ ∞ := coe_two ▸ coe_ne_top

@[simp] lemma add_top : a + ∞ = ∞ := with_top.add_top
@[simp] lemma top_add : ∞ + a = ∞ := with_top.top_add

/-- Coercion `ℝ≥0 → ennreal` as a `ring_hom`. -/
def of_nnreal_hom : nnreal →+* ennreal :=
⟨coe, coe_one, λ _ _, coe_mul, coe_zero, λ _ _, coe_add⟩

@[simp] lemma coe_of_nnreal_hom : ⇑of_nnreal_hom = coe := rfl

@[simp, norm_cast] lemma coe_indicator {α} (s : set α) (f : α → nnreal) (a : α) :
  ((s.indicator f a : nnreal) : ennreal) = s.indicator (λ x, f x) a :=
(of_nnreal_hom : nnreal →+ ennreal).map_indicator _ _ _

@[simp, norm_cast] lemma coe_pow (n : ℕ) : (↑(r^n) : ennreal) = r^n :=
of_nnreal_hom.map_pow r n

lemma add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := with_top.add_eq_top _ _
lemma add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := with_top.add_lt_top _ _

lemma to_nnreal_add {r₁ r₂ : ennreal} (h₁ : r₁ < ⊤) (h₂ : r₂ < ⊤) :
  (r₁ + r₂).to_nnreal = r₁.to_nnreal + r₂.to_nnreal :=
begin
  rw [← coe_eq_coe, coe_add, coe_to_nnreal, coe_to_nnreal, coe_to_nnreal];
    apply @ne_top_of_lt ennreal _ _ ⊤,
  exact h₂,
  exact h₁,
  exact add_lt_top.2 ⟨h₁, h₂⟩
end

/- rw has trouble with the generic lt_top_iff_ne_top and bot_lt_iff_ne_bot
(contrary to erw). This is solved with the next lemmas -/
protected lemma lt_top_iff_ne_top : a < ∞ ↔ a ≠ ∞ := lt_top_iff_ne_top
protected lemma bot_lt_iff_ne_bot : 0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot

lemma not_lt_top {x : ennreal} : ¬ x < ∞ ↔ x = ∞ := by rw [lt_top_iff_ne_top, not_not]

lemma add_ne_top : a + b ≠ ∞ ↔ a ≠ ∞ ∧ b ≠ ∞ :=
by simpa only [lt_top_iff_ne_top] using add_lt_top

lemma mul_top : a * ∞ = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.mul_top h } end

lemma top_mul : ∞ * a = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.top_mul h } end

@[simp] lemma top_mul_top : ∞ * ∞ = ∞ := with_top.top_mul_top

lemma top_pow {n:ℕ} (h : 0 < n) : ∞^n = ∞ :=
nat.le_induction (pow_one _) (λ m hm hm', by rw [pow_succ, hm', top_mul_top])
  _ (nat.succ_le_of_lt h)

lemma mul_eq_top : a * b = ⊤ ↔ (a ≠ 0 ∧ b = ⊤) ∨ (a = ⊤ ∧ b ≠ 0) :=
with_top.mul_eq_top_iff

lemma mul_ne_top : a ≠ ∞ → b ≠ ∞ → a * b ≠ ∞ :=
by simp [(≠), mul_eq_top] {contextual := tt}

lemma mul_lt_top  : a < ⊤ → b < ⊤ → a * b < ⊤ :=
by simpa only [ennreal.lt_top_iff_ne_top] using mul_ne_top

lemma ne_top_of_mul_ne_top_left (h : a * b ≠ ⊤) (hb : b ≠ 0) : a ≠ ⊤ :=
by { simp [mul_eq_top, hb, not_or_distrib] at h ⊢, exact h.2 }

lemma ne_top_of_mul_ne_top_right (h : a * b ≠ ⊤) (ha : a ≠ 0) : b ≠ ⊤ :=
ne_top_of_mul_ne_top_left (by rwa [mul_comm]) ha

lemma lt_top_of_mul_lt_top_left (h : a * b < ⊤) (hb : b ≠ 0) : a < ⊤ :=
by { rw [ennreal.lt_top_iff_ne_top] at h ⊢, exact ne_top_of_mul_ne_top_left h hb }

lemma lt_top_of_mul_lt_top_right (h : a * b < ⊤) (ha : a ≠ 0) : b < ⊤ :=
lt_top_of_mul_lt_top_left (by rwa [mul_comm]) ha

lemma mul_lt_top_iff {a b : ennreal} : a * b < ⊤ ↔ (a < ⊤ ∧ b < ⊤) ∨ a = 0 ∨ b = 0 :=
begin
  split,
  { intro h, rw [← or_assoc, or_iff_not_imp_right, or_iff_not_imp_right], intros hb ha,
    exact ⟨lt_top_of_mul_lt_top_left h hb, lt_top_of_mul_lt_top_right h ha⟩ },
  { rintro (⟨ha, hb⟩|rfl|rfl); [exact mul_lt_top ha hb, simp, simp] }
end

@[simp] lemma mul_pos : 0 < a * b ↔ 0 < a ∧ 0 < b :=
by simp only [zero_lt_iff_ne_zero, ne.def, mul_eq_zero, not_or_distrib]

lemma pow_eq_top : ∀ n:ℕ, a^n=∞ → a=∞
| 0 := by simp
| (n+1) := λ o, (mul_eq_top.1 o).elim (λ h, pow_eq_top n h.2) and.left

lemma pow_ne_top (h : a ≠ ∞) {n:ℕ} : a^n ≠ ∞ :=
mt (pow_eq_top n) h

lemma pow_lt_top : a < ∞ → ∀ n:ℕ, a^n < ∞ :=
by simpa only [lt_top_iff_ne_top] using pow_ne_top

@[simp, norm_cast] lemma coe_finset_sum {s : finset α} {f : α → nnreal} :
  ↑(∑ a in s, f a) = (∑ a in s, f a : ennreal) :=
of_nnreal_hom.map_sum f s

@[simp, norm_cast] lemma coe_finset_prod {s : finset α} {f : α → nnreal} :
  ↑(∏ a in s, f a) = ((∏ a in s, f a) : ennreal) :=
of_nnreal_hom.map_prod f s

section order

@[simp] lemma bot_eq_zero : (⊥ : ennreal) = 0 := rfl

@[simp] lemma coe_lt_top : coe r < ∞ := with_top.coe_lt_top r
@[simp] lemma not_top_le_coe : ¬ (⊤:ennreal) ≤ ↑r := with_top.not_top_le_coe r
lemma zero_lt_coe_iff : 0 < (↑p : ennreal) ↔ 0 < p := coe_lt_coe
@[simp, norm_cast] lemma one_le_coe_iff : (1:ennreal) ≤ ↑r ↔ 1 ≤ r := coe_le_coe
@[simp, norm_cast] lemma coe_le_one_iff : ↑r ≤ (1:ennreal) ↔ r ≤ 1 := coe_le_coe
@[simp, norm_cast] lemma coe_lt_one_iff : (↑p : ennreal) < 1 ↔ p < 1 := coe_lt_coe
@[simp, norm_cast] lemma one_lt_coe_iff : 1 < (↑p : ennreal) ↔ 1 < p := coe_lt_coe
@[simp, norm_cast] lemma coe_nat (n : nat) : ((n : nnreal) : ennreal) = n := with_top.coe_nat n
@[simp] lemma nat_ne_top (n : nat) : (n : ennreal) ≠ ⊤ := with_top.nat_ne_top n
@[simp] lemma top_ne_nat (n : nat) : (⊤ : ennreal) ≠ n := with_top.top_ne_nat n
@[simp] lemma one_lt_top : 1 < ∞ := coe_lt_top

lemma le_coe_iff : a ≤ ↑r ↔ (∃p:nnreal, a = p ∧ p ≤ r) := with_top.le_coe_iff r a
lemma coe_le_iff : ↑r ≤ a ↔ (∀p:nnreal, a = p → r ≤ p) := with_top.coe_le_iff r a

lemma lt_iff_exists_coe : a < b ↔ (∃p:nnreal, a = p ∧ ↑p < b) := with_top.lt_iff_exists_coe a b

lemma pow_le_pow {n m : ℕ} (ha : 1 ≤ a) (h : n ≤ m) : a ^ n ≤ a ^ m :=
begin
  cases a,
  { cases m,
    { rw eq_bot_iff.mpr h,
      exact le_refl _ },
    { rw [none_eq_top, top_pow (nat.succ_pos m)],
      exact le_top } },
  { rw [some_eq_coe, ← coe_pow, ← coe_pow, coe_le_coe],
    exact pow_le_pow (by simpa using ha) h }
end

@[simp] lemma max_eq_zero_iff : max a b = 0 ↔ a = 0 ∧ b = 0 :=
by simp only [le_zero_iff_eq.symm, max_le_iff]

@[simp] lemma max_zero_left : max 0 a = a := max_eq_right (zero_le a)
@[simp] lemma max_zero_right : max a 0 = a := max_eq_left (zero_le a)

-- TODO: why this is not a `rfl`? There is some hidden diamond here.
@[simp] lemma sup_eq_max : a ⊔ b = max a b :=
eq_of_forall_ge_iff $ λ c, sup_le_iff.trans max_le_iff.symm

protected lemma pow_pos : 0 < a → ∀ n : ℕ, 0 < a^n :=
  canonically_ordered_semiring.pow_pos

protected lemma pow_ne_zero : a ≠ 0 → ∀ n : ℕ, a^n ≠ 0 :=
by simpa only [zero_lt_iff_ne_zero] using ennreal.pow_pos

@[simp] lemma not_lt_zero : ¬ a < 0 := by simp

lemma add_lt_add_iff_left : a < ⊤ → (a + c < a + b ↔ c < b) :=
with_top.add_lt_add_iff_left

lemma add_lt_add_iff_right : a < ⊤ → (c + a < b + a ↔ c < b) :=
with_top.add_lt_add_iff_right

lemma lt_add_right (ha : a < ⊤) (hb : 0 < b) : a < a + b :=
by rwa [← add_lt_add_iff_left ha, add_zero] at hb

lemma le_of_forall_epsilon_le : ∀{a b : ennreal}, (∀ε:nnreal, 0 < ε → b < ∞ → a ≤ b + ε) → a ≤ b
| a    none     h := le_top
| none (some a) h :=
  have (⊤:ennreal) ≤ ↑a + ↑(1:nnreal), from h 1 zero_lt_one coe_lt_top,
  by rw [← coe_add] at this; exact (not_top_le_coe this).elim
| (some a) (some b) h :=
    by simp only [none_eq_top, some_eq_coe, coe_add.symm, coe_le_coe, coe_lt_top, true_implies_iff]
      at *; exact nnreal.le_of_forall_epsilon_le h

lemma lt_iff_exists_rat_btwn :
  a < b ↔ (∃q:ℚ, 0 ≤ q ∧ a < nnreal.of_real q ∧ (nnreal.of_real q:ennreal) < b) :=
⟨λ h,
  begin
    rcases lt_iff_exists_coe.1 h with ⟨p, rfl, _⟩,
    rcases dense h with ⟨c, pc, cb⟩,
    rcases lt_iff_exists_coe.1 cb with ⟨r, rfl, _⟩,
    rcases (nnreal.lt_iff_exists_rat_btwn _ _).1 (coe_lt_coe.1 pc) with ⟨q, hq0, pq, qr⟩,
    exact ⟨q, hq0, coe_lt_coe.2 pq, lt_trans (coe_lt_coe.2 qr) cb⟩
  end,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_real_btwn :
  a < b ↔ (∃r:ℝ, 0 ≤ r ∧ a < ennreal.of_real r ∧ (ennreal.of_real r:ennreal) < b) :=
⟨λ h, let ⟨q, q0, aq, qb⟩ := ennreal.lt_iff_exists_rat_btwn.1 h in
  ⟨q, rat.cast_nonneg.2 q0, aq, qb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

lemma lt_iff_exists_nnreal_btwn :
  a < b ↔ (∃r:nnreal, a < r ∧ (r : ennreal) < b) :=
with_top.lt_iff_exists_coe_btwn

lemma lt_iff_exists_add_pos_lt : a < b ↔ (∃ r : nnreal, 0 < r ∧ a + r < b) :=
begin
  refine ⟨λ hab, _, λ ⟨r, rpos, hr⟩, lt_of_le_of_lt (le_add_right (le_refl _)) hr⟩,
  cases a, { simpa using hab },
  rcases lt_iff_exists_real_btwn.1 hab with ⟨c, c_nonneg, ac, cb⟩,
  let d : nnreal := ⟨c, c_nonneg⟩,
  have ad : a < d,
  { rw of_real_eq_coe_nnreal c_nonneg at ac,
    exact coe_lt_coe.1 ac },
  refine ⟨d-a, nnreal.sub_pos.2 ad, _⟩,
  rw [some_eq_coe, ← coe_add],
  convert cb,
  have : nnreal.of_real c = d,
    by { rw [← nnreal.coe_eq, nnreal.coe_of_real _ c_nonneg], refl },
  rw [add_comm, this],
  exact nnreal.sub_add_cancel_of_le (le_of_lt ad)
end

lemma coe_nat_lt_coe {n : ℕ} : (n : ennreal) < r ↔ ↑n < r := ennreal.coe_nat n ▸ coe_lt_coe
lemma coe_lt_coe_nat {n : ℕ} : (r : ennreal) < n ↔ r < n := ennreal.coe_nat n ▸ coe_lt_coe
@[norm_cast] lemma coe_nat_lt_coe_nat {m n : ℕ} : (m : ennreal) < n ↔ m < n :=
ennreal.coe_nat n ▸ coe_nat_lt_coe.trans nat.cast_lt
lemma coe_nat_ne_top {n : ℕ} : (n : ennreal) ≠ ∞ := ennreal.coe_nat n ▸ coe_ne_top
lemma coe_nat_mono : strict_mono (coe : ℕ → ennreal) := λ _ _, coe_nat_lt_coe_nat.2
@[norm_cast] lemma coe_nat_le_coe_nat {m n : ℕ} : (m : ennreal) ≤ n ↔ m ≤ n :=
coe_nat_mono.le_iff_le

instance : char_zero ennreal := ⟨coe_nat_mono.injective⟩

protected lemma exists_nat_gt {r : ennreal} (h : r ≠ ⊤) : ∃n:ℕ, r < n :=
begin
  lift r to nnreal using h,
  rcases exists_nat_gt r with ⟨n, hn⟩,
  exact ⟨n, coe_lt_coe_nat.2 hn⟩,
end

lemma add_lt_add (ac : a < c) (bd : b < d) : a + b < c + d :=
begin
  rcases dense ac with ⟨a', aa', a'c⟩,
  rcases lt_iff_exists_coe.1 aa' with ⟨aR, rfl, _⟩,
  rcases lt_iff_exists_coe.1 a'c with ⟨a'R, rfl, _⟩,
  rcases dense bd with ⟨b', bb', b'd⟩,
  rcases lt_iff_exists_coe.1 bb' with ⟨bR, rfl, _⟩,
  rcases lt_iff_exists_coe.1 b'd with ⟨b'R, rfl, _⟩,
  have I : ↑aR + ↑bR < ↑a'R + ↑b'R :=
  begin
    rw [← coe_add, ← coe_add, coe_lt_coe],
    apply add_lt_add (coe_lt_coe.1 aa') (coe_lt_coe.1 bb')
  end,
  have J : ↑a'R + ↑b'R ≤ c + d := add_le_add (le_of_lt a'c) (le_of_lt b'd),
  apply lt_of_lt_of_le I J
end

@[norm_cast] lemma coe_min : ((min r p:nnreal):ennreal) = min r p :=
coe_mono.map_min

@[norm_cast] lemma coe_max : ((max r p:nnreal):ennreal) = max r p :=
coe_mono.map_max

end order

section complete_lattice

lemma coe_Sup {s : set nnreal} : bdd_above s → (↑(Sup s) : ennreal) = (⨆a∈s, ↑a) := with_top.coe_Sup
lemma coe_Inf {s : set nnreal} : s.nonempty → (↑(Inf s) : ennreal) = (⨅a∈s, ↑a) := with_top.coe_Inf

@[simp] lemma top_mem_upper_bounds {s : set ennreal} : ∞ ∈ upper_bounds s :=
assume x hx, le_top

lemma coe_mem_upper_bounds {s : set nnreal} :
  ↑r ∈ upper_bounds ((coe : nnreal → ennreal) '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

lemma infi_ennreal {α : Type*} [complete_lattice α] {f : ennreal → α} :
  (⨅n, f n) = (⨅n:nnreal, f n) ⊓ f ⊤ :=
le_antisymm
  (le_inf (le_infi $ assume i, infi_le _ _) (infi_le _ _))
  (le_infi $ forall_ennreal.2 ⟨assume r, inf_le_left_of_le $ infi_le _ _, inf_le_right⟩)

end complete_lattice

section mul

lemma mul_le_mul : a ≤ b → c ≤ d → a * c ≤ b * d :=
canonically_ordered_semiring.mul_le_mul

lemma mul_left_mono : monotone ((*) a) := λ b c, mul_le_mul (le_refl a)

lemma mul_right_mono : monotone (λ x, x * a) := λ b c h, mul_le_mul h (le_refl a)

lemma max_mul : max a b * c = max (a * c) (b * c) :=
mul_right_mono.map_max

lemma mul_max : a * max b c = max (a * b) (a * c) :=
mul_left_mono.map_max

lemma mul_eq_mul_left : a ≠ 0 → a ≠ ⊤ → (a * b = a * c ↔ b = c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm,
      nnreal.mul_eq_mul_left] {contextual := tt},
end

lemma mul_eq_mul_right : c ≠ 0 → c ≠ ∞ → (a * c = b * c ↔ a = b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_eq_mul_left

lemma mul_le_mul_left : a ≠ 0 → a ≠ ⊤ → (a * b ≤ a * c ↔ b ≤ c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm] {contextual := tt},
  assume h, exact mul_le_mul_left (zero_lt_iff_ne_zero.2 h)
end

lemma mul_le_mul_right : c ≠ 0 → c ≠ ∞ → (a * c ≤ b * c ↔ a ≤ b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_le_mul_left

lemma mul_lt_mul_left : a ≠ 0 → a ≠ ⊤ → (a * b < a * c ↔ b < c) :=
λ h0 ht, by simp only [mul_le_mul_left h0 ht, lt_iff_le_not_le]

lemma mul_lt_mul_right : c ≠ 0 → c ≠ ∞ → (a * c < b * c ↔ a < b) :=
mul_comm c a ▸ mul_comm c b ▸ mul_lt_mul_left

end mul

section sub
instance : has_sub ennreal := ⟨λa b, Inf {d | a ≤ d + b}⟩

@[norm_cast] lemma coe_sub : ↑(p - r) = (↑p:ennreal) - r :=
le_antisymm
  (le_Inf $ assume b (hb : ↑p ≤ b + r), coe_le_iff.2 $
    by rintros d rfl; rwa [← coe_add, coe_le_coe, ← nnreal.sub_le_iff_le_add] at hb)
  (Inf_le $ show (↑p : ennreal) ≤ ↑(p - r) + ↑r,
    by rw [← coe_add, coe_le_coe, ← nnreal.sub_le_iff_le_add])

@[simp] lemma top_sub_coe : ∞ - ↑r = ∞ :=
top_unique $ le_Inf $ by simp [add_eq_top]

@[simp] lemma sub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
le_antisymm (Inf_le $ le_add_left h) (zero_le _)

@[simp] lemma sub_self : a - a = 0 := sub_eq_zero_of_le $ le_refl _

@[simp] lemma zero_sub : 0 - a = 0 :=
le_antisymm (Inf_le $ zero_le $ 0 + a) (zero_le _)

@[simp] lemma sub_infty : a - ∞ = 0 :=
le_antisymm (Inf_le $ by simp) (zero_le _)

lemma sub_le_sub (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
Inf_le_Inf $ assume e (h : b ≤ e + d),
  calc a ≤ b : h₁
    ... ≤ e + d : h
    ... ≤ e + c : add_le_add (le_refl _) h₂

@[simp] lemma add_sub_self : ∀{a b : ennreal}, b < ∞ → (a + b) - b = a
| a        none     := by simp [none_eq_top]
| none     (some b) := by simp [none_eq_top, some_eq_coe]
| (some a) (some b) :=
  by simp [some_eq_coe]; rw [← coe_add, ← coe_sub, coe_eq_coe, nnreal.add_sub_cancel]

@[simp] lemma add_sub_self' (h : a < ∞) : (a + b) - a = b :=
by rw [add_comm, add_sub_self h]

lemma add_right_inj (h : a < ∞) : a + b = a + c ↔ b = c :=
⟨λ e, by simpa [h] using congr_arg (λ x, x - a) e, congr_arg _⟩

lemma add_left_inj (h : a < ∞) : b + a = c + a ↔ b = c :=
by rw [add_comm, add_comm c, add_right_inj h]

@[simp] lemma sub_add_cancel_of_le : ∀{a b : ennreal}, b ≤ a → (a - b) + b = a :=
begin
  simp [forall_ennreal, le_coe_iff, -add_comm] {contextual := tt},
  rintros r p x rfl h,
  rw [← coe_sub, ← coe_add, nnreal.sub_add_cancel_of_le h]
end

@[simp] lemma add_sub_cancel_of_le (h : b ≤ a) : b + (a - b) = a :=
by rwa [add_comm, sub_add_cancel_of_le]

lemma sub_add_self_eq_max : (a - b) + b = max a b :=
match le_total a b with
| or.inl h := by simp [h, max_eq_right]
| or.inr h := by simp [h, max_eq_left]
end

lemma le_sub_add_self : a ≤ (a - b) + b :=
by { rw sub_add_self_eq_max, exact le_max_left a b }

@[simp] protected lemma sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b :=
iff.intro
  (assume h : a - b ≤ c,
    calc a ≤ (a - b) + b : le_sub_add_self
      ... ≤ c + b : add_le_add_right h _)
  (assume h : a ≤ c + b,
    calc a - b ≤ (c + b) - b : sub_le_sub h (le_refl _)
      ... ≤ c : Inf_le (le_refl (c + b)))

protected lemma sub_le_iff_le_add' : a - b ≤ c ↔ a ≤ b + c :=
add_comm c b ▸ ennreal.sub_le_iff_le_add

lemma sub_eq_of_add_eq : b ≠ ∞ → a + b = c → c - b = a :=
λ hb hc, hc ▸ add_sub_self (lt_top_iff_ne_top.2 hb)

protected lemma sub_le_of_sub_le (h : a - b ≤ c) : a - c ≤ b :=
ennreal.sub_le_iff_le_add.2 $ by { rw add_comm, exact ennreal.sub_le_iff_le_add.1 h }

protected lemma sub_lt_sub_self : a ≠ ⊤ → a ≠ 0 → 0 < b → a - b < a :=
match a, b with
| none, _ := by { have := none_eq_top, assume h, contradiction }
| (some a), none := by {intros, simp only [none_eq_top, sub_infty, zero_lt_iff_ne_zero], assumption}
| (some a), (some b) :=
  begin
    simp only [some_eq_coe, coe_sub.symm, coe_pos, coe_eq_zero, coe_lt_coe, ne.def],
    assume h₁ h₂, apply nnreal.sub_lt_self, exact zero_lt_iff_ne_zero.2 h₂
  end
end

@[simp] lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by simpa [-ennreal.sub_le_iff_le_add] using @ennreal.sub_le_iff_le_add a b 0

@[simp] lemma zero_lt_sub_iff_lt : 0 < a - b ↔ b < a :=
by simpa [ennreal.bot_lt_iff_ne_bot, -sub_eq_zero_iff_le]
  using not_iff_not.2 (@sub_eq_zero_iff_le a b)

lemma lt_sub_iff_add_lt : a < b - c ↔ a + c < b :=
begin
  cases a, { simp },
  cases c, { simp },
  cases b, { simp only [true_iff, coe_lt_top, some_eq_coe, top_sub_coe, none_eq_top, ← coe_add] },
  simp only [some_eq_coe],
  rw [← coe_add, ← coe_sub, coe_lt_coe, coe_lt_coe, nnreal.lt_sub_iff_add_lt],
end

lemma sub_le_self (a b : ennreal) : a - b ≤ a :=
ennreal.sub_le_iff_le_add.2 $ le_add_right (le_refl a)

@[simp] lemma sub_zero : a - 0 = a :=
eq.trans (add_zero (a - 0)).symm $ by simp

/-- A version of triangle inequality for difference as a "distance". -/
lemma sub_le_sub_add_sub : a - c ≤ a - b + (b - c) :=
ennreal.sub_le_iff_le_add.2 $
calc a ≤ a - b + b : le_sub_add_self
... ≤ a - b + ((b - c) + c) : add_le_add_left le_sub_add_self _
... = a - b + (b - c) + c : (add_assoc _ _ _).symm

lemma sub_sub_cancel (h : a < ∞) (h2 : b ≤ a) : a - (a - b) = b :=
by rw [← add_left_inj (lt_of_le_of_lt (sub_le_self _ _) h),
  sub_add_cancel_of_le (sub_le_self _ _), add_sub_cancel_of_le h2]

lemma sub_right_inj {a b c : ennreal} (ha : a < ⊤) (hb : b ≤ a) (hc : c ≤ a) :
  a - b = a - c ↔ b = c :=
iff.intro
  begin
    assume h, have : a - (a - b) = a - (a - c), rw h,
    rw [sub_sub_cancel ha hb, sub_sub_cancel ha hc] at this, exact this
  end
  (λ h, by rw h)

lemma sub_mul (h : 0 < b → b < a → c ≠ ∞) : (a - b) * c = a * c - b * c :=
begin
  cases le_or_lt a b with hab hab,
  { simp [hab, mul_right_mono hab] },
  symmetry,
  cases eq_or_lt_of_le (zero_le b) with hb hb,
  { subst b, simp },
  apply sub_eq_of_add_eq,
  { exact mul_ne_top (ne_top_of_lt hab) (h hb hab) },
  rw [← add_mul, sub_add_cancel_of_le (le_of_lt hab)]
end

lemma mul_sub (h : 0 < c → c < b → a ≠ ∞) :
  a * (b - c) = a * b - a * c :=
by { simp only [mul_comm a], exact sub_mul h }

lemma sub_mul_ge : a * c - b * c ≤ (a - b) * c :=
begin
  -- with `0 < b → b < a → c ≠ ∞` Lean names the first variable `a`
  by_cases h : ∀ (hb : 0 < b), b < a → c ≠ ∞,
  { rw [sub_mul h],
    exact le_refl _ },
  { push_neg at h,
    rcases h with ⟨hb, hba, hc⟩,
    subst c,
    simp only [mul_top, if_neg (ne_of_gt hb), if_neg (ne_of_gt $ lt_trans hb hba), sub_self,
      zero_le] }
end

end sub

section sum

open finset

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top {s : finset α} {f : α → ennreal} :
  (∀a∈s, f a < ⊤) → ∑ a in s, f a < ⊤ :=
with_top.sum_lt_top

/-- A sum of finite numbers is still finite -/
lemma sum_lt_top_iff {s : finset α} {f : α → ennreal} :
  ∑ a in s, f a < ⊤ ↔ (∀a∈s, f a < ⊤) :=
with_top.sum_lt_top_iff

/-- A sum of numbers is infinite iff one of them is infinite -/
lemma sum_eq_top_iff {s : finset α} {f : α → ennreal} :
  (∑ x in s, f x) = ⊤ ↔ (∃a∈s, f a = ⊤) :=
with_top.sum_eq_top_iff

/-- seeing `ennreal` as `nnreal` does not change their sum, unless one of the `ennreal` is
infinity -/
lemma to_nnreal_sum {s : finset α} {f : α → ennreal} (hf : ∀a∈s, f a < ⊤) :
  ennreal.to_nnreal (∑ a in s, f a) = ∑ a in s, ennreal.to_nnreal (f a) :=
begin
  rw [← coe_eq_coe, coe_to_nnreal, coe_finset_sum, sum_congr],
  { refl },
  { intros x hx, rw coe_to_nnreal, rw ← ennreal.lt_top_iff_ne_top, exact hf x hx },
  { rw ← ennreal.lt_top_iff_ne_top, exact sum_lt_top hf }
end

/-- seeing `ennreal` as `real` does not change their sum, unless one of the `ennreal` is infinity -/
lemma to_real_sum {s : finset α} {f : α → ennreal} (hf : ∀a∈s, f a < ⊤) :
  ennreal.to_real (∑ a in s, f a) = ∑ a in s, ennreal.to_real (f a) :=
by { rw [ennreal.to_real, to_nnreal_sum hf, nnreal.coe_sum], refl }

end sum

section interval

variables {x y z : ennreal} {ε ε₁ ε₂ : ennreal} {s : set ennreal}

protected lemma Ico_eq_Iio : (Ico 0 y) = (Iio y) :=
ext $ assume a, iff.intro
  (assume ⟨_, hx⟩, hx)
  (assume hx, ⟨zero_le _, hx⟩)

lemma mem_Iio_self_add : x ≠ ⊤ → 0 < ε → x ∈ Iio (x + ε) :=
assume xt ε0, lt_add_right (by rwa lt_top_iff_ne_top) ε0

lemma not_mem_Ioo_self_sub : x = 0 → x ∉ Ioo (x - ε) y :=
assume x0, by simp [x0]

lemma mem_Ioo_self_sub_add : x ≠ ⊤ → x ≠ 0 → 0 < ε₁ → 0 < ε₂ → x ∈ Ioo (x - ε₁) (x + ε₂) :=
assume xt x0 ε0 ε0',
  ⟨ennreal.sub_lt_sub_self xt x0 ε0, lt_add_right (by rwa [lt_top_iff_ne_top]) ε0'⟩

end interval

section bit

@[simp] lemma bit0_inj : bit0 a = bit0 b ↔ a = b :=
⟨λh, begin
  rcases (lt_trichotomy a b) with h₁| h₂| h₃,
  { exact (absurd h (ne_of_lt (add_lt_add h₁ h₁))) },
  { exact h₂ },
  { exact (absurd h.symm (ne_of_lt (add_lt_add h₃ h₃))) }
end,
λh, congr_arg _ h⟩

@[simp] lemma bit0_eq_zero_iff : bit0 a = 0 ↔ a = 0 :=
by simpa only [bit0_zero] using @bit0_inj a 0

@[simp] lemma bit0_eq_top_iff : bit0 a = ∞ ↔ a = ∞ :=
by rw [bit0, add_eq_top, or_self]

@[simp] lemma bit1_inj : bit1 a = bit1 b ↔ a = b :=
⟨λh, begin
  unfold bit1 at h,
  rwa [add_left_inj, bit0_inj] at h,
  simp [lt_top_iff_ne_top]
end,
λh, congr_arg _ h⟩

@[simp] lemma bit1_ne_zero : bit1 a ≠ 0 :=
by unfold bit1; simp

@[simp] lemma bit1_eq_one_iff : bit1 a = 1 ↔ a = 0 :=
by simpa only [bit1_zero] using @bit1_inj a 0

@[simp] lemma bit1_eq_top_iff : bit1 a = ∞ ↔ a = ∞ :=
by unfold bit1; rw add_eq_top; simp

end bit

section inv
instance : has_inv ennreal := ⟨λa, Inf {b | 1 ≤ a * b}⟩
instance : has_div ennreal := ⟨λa b, a * b⁻¹⟩

lemma div_def : a / b = a * b⁻¹ := rfl

lemma mul_div_assoc : (a * b) / c = a * (b / c) :=
mul_assoc _ _ _

@[simp] lemma inv_zero : (0 : ennreal)⁻¹ = ∞ :=
show Inf {b : ennreal | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_top : (∞ : ennreal)⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h, top_mul]

@[simp, norm_cast] lemma coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ennreal) = (↑r)⁻¹ :=
le_antisymm
  (le_Inf $ assume b (hb : 1 ≤ ↑r * b), coe_le_iff.2 $
    by rintros b rfl; rwa [← coe_mul, ← coe_one, coe_le_coe, ← nnreal.inv_le hr] at hb)
  (Inf_le $ by simp; rw [← coe_mul, nnreal.mul_inv_cancel hr]; exact le_refl 1)

lemma coe_inv_le :  (↑r⁻¹ : ennreal) ≤ (↑r)⁻¹ :=
if hr : r = 0 then by simp only [hr, nnreal.inv_zero, inv_zero, coe_zero, zero_le]
else by simp only [coe_inv hr, le_refl]

@[norm_cast] lemma coe_inv_two : ((2⁻¹:nnreal):ennreal) = 2⁻¹ :=
by rw [coe_inv (ne_of_gt _root_.zero_lt_two), coe_two]

@[simp, norm_cast] lemma coe_div (hr : r ≠ 0) : (↑(p / r) : ennreal) = p / r :=
show ↑(p * r⁻¹) = ↑p * (↑r)⁻¹, by rw [coe_mul, coe_inv hr]

@[simp] lemma inv_one : (1:ennreal)⁻¹ = 1 :=
by simpa only [coe_inv one_ne_zero, coe_one] using coe_eq_coe.2 nnreal.inv_one

@[simp] lemma div_one {a : ennreal} : a / 1 = a :=
by simp [ennreal.div_def]

protected lemma inv_pow {n : ℕ} : (a^n)⁻¹ = (a⁻¹)^n :=
begin
  by_cases a = 0; cases a; cases n; simp [*, none_eq_top, some_eq_coe,
    zero_pow, top_pow, nat.zero_lt_succ] at *,
  rw [← coe_inv h, ← coe_pow, ← coe_inv, nnreal.inv_pow, coe_pow],
  rw [← ne.def] at h,
  rw [← zero_lt_iff_ne_zero] at *,
  apply pow_pos h
end

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a :=
by by_cases a = 0; cases a; simp [*, none_eq_top, some_eq_coe,
  -coe_inv, (coe_inv _).symm] at *

lemma inv_involutive : function.involutive (λ a:ennreal, a⁻¹) :=
λ a, ennreal.inv_inv

lemma inv_bijective : function.bijective (λ a:ennreal, a⁻¹) :=
ennreal.inv_involutive.bijective

@[simp] lemma inv_eq_inv : a⁻¹ = b⁻¹ ↔ a = b := inv_bijective.1.eq_iff

@[simp] lemma inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
inv_zero ▸ inv_eq_inv

lemma inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[simp] lemma inv_lt_top {x : ennreal} : x⁻¹ < ⊤ ↔ 0 < x :=
by { simp only [lt_top_iff_ne_top, inv_ne_top, zero_lt_iff_ne_zero] }

lemma div_lt_top {x y : ennreal} (h1 : x < ⊤) (h2 : 0 < y) : x / y < ⊤ :=
mul_lt_top h1 (inv_lt_top.mpr h2)

@[simp] lemma inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
inv_top ▸ inv_eq_inv

lemma inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

@[simp] lemma inv_pos : 0 < a⁻¹ ↔ a ≠ ∞ :=
zero_lt_iff_ne_zero.trans inv_ne_zero

@[simp] lemma inv_lt_inv : a⁻¹ < b⁻¹ ↔ b < a :=
begin
  cases a; cases b; simp only [some_eq_coe, none_eq_top, inv_top],
  { simp only [lt_irrefl] },
  { exact inv_pos.trans lt_top_iff_ne_top.symm },
  { simp only [not_lt_zero, not_top_lt] },
  { cases eq_or_lt_of_le (zero_le a) with ha ha;
      cases eq_or_lt_of_le (zero_le b) with hb hb,
    { subst a, subst b, simp },
    { subst a, simp },
    { subst b, simp [zero_lt_iff_ne_zero, lt_top_iff_ne_top, inv_ne_top] },
    { rw [← coe_inv (ne_of_gt ha), ← coe_inv (ne_of_gt hb), coe_lt_coe, coe_lt_coe],
      simp only [nnreal.coe_lt_coe.symm] at *,
      exact inv_lt_inv ha hb } }
end

lemma inv_lt_iff_inv_lt : a⁻¹ < b ↔ b⁻¹ < a :=
by simpa only [inv_inv] using @inv_lt_inv a b⁻¹

lemma lt_inv_iff_lt_inv : a < b⁻¹ ↔ b < a⁻¹ :=
by simpa only [inv_inv] using @inv_lt_inv a⁻¹ b

@[simp, priority 1100] -- higher than le_inv_iff_mul_le
lemma inv_le_inv : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
by simp only [le_iff_lt_or_eq, inv_lt_inv, inv_eq_inv, eq_comm]

lemma inv_le_iff_inv_le : a⁻¹ ≤ b ↔ b⁻¹ ≤ a :=
by simpa only [inv_inv] using @inv_le_inv a b⁻¹

lemma le_inv_iff_le_inv : a ≤ b⁻¹ ↔ b ≤ a⁻¹ :=
by simpa only [inv_inv] using @inv_le_inv a⁻¹ b

@[simp] lemma inv_lt_one : a⁻¹ < 1 ↔ 1 < a :=
inv_lt_iff_inv_lt.trans $ by rw [inv_one]

@[simp] lemma div_top : a / ∞ = 0 := by simp only [div_def, inv_top, mul_zero]

@[simp] lemma top_div_coe : ∞ / p = ∞ := by simp [div_def, top_mul]

lemma top_div_of_ne_top (h : a ≠ ⊤) : ∞ / a = ∞ :=
by { lift a to nnreal using h, exact top_div_coe }

lemma top_div_of_lt_top (h : a < ⊤) : ∞ / a = ∞ :=
top_div_of_ne_top h.ne

lemma top_div : ∞ / a = if a = ∞ then 0 else ∞ :=
by by_cases a = ∞; simp [top_div_of_ne_top, *]

@[simp] lemma zero_div : 0 / a = 0 := zero_mul a⁻¹

lemma div_eq_top : a / b = ⊤ ↔ (a ≠ 0 ∧ b = 0) ∨ (a = ⊤ ∧ b ≠ ⊤) :=
by simp [ennreal.div_def, ennreal.mul_eq_top]

lemma le_div_iff_mul_le (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ⊤ ∨ c ≠ ⊤) :
  a ≤ c / b ↔ a * b ≤ c :=
begin
  cases b,
  { simp at ht,
    split,
    { assume ha, simp at ha, simp [ha] },
    { contrapose,
      assume ha,
      simp at ha,
      have : a * ⊤ = ⊤, by simp [ennreal.mul_eq_top, ha],
      simp [this, ht] } },
  by_cases hb : b ≠ 0,
  { have : (b : ennreal) ≠ 0, by simp [hb],
    rw [← ennreal.mul_le_mul_left this coe_ne_top],
    suffices : ↑b * a ≤ (↑b  * ↑b⁻¹) * c ↔ a * ↑b ≤ c,
    { simpa [some_eq_coe, div_def, hb, mul_left_comm, mul_comm, mul_assoc] },
    rw [← coe_mul, nnreal.mul_inv_cancel hb, coe_one, one_mul, mul_comm] },
  { simp at hb,
    simp [hb] at h0,
    have : c / 0 = ⊤, by simp [div_eq_top, h0],
    simp [hb, this] }
end

lemma div_le_iff_le_mul (hb0 : b ≠ 0 ∨ c ≠ ⊤) (hbt : b ≠ ⊤ ∨ c ≠ 0) : a / b ≤ c ↔ a ≤ c * b :=
begin
  suffices : a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹, by simpa [div_def],
  apply (le_div_iff_mul_le _ _).symm,
  simpa [inv_ne_zero] using hbt,
  simpa [inv_ne_zero] using hb0
end

lemma div_le_of_le_mul (h : a ≤ b * c) : a / c ≤ b :=
begin
  by_cases h0 : c = 0,
  { have : a = 0, by simpa [h0] using h, simp [*] },
  by_cases hinf : c = ⊤, by simp [hinf],
  exact (div_le_iff_le_mul (or.inl h0) (or.inl hinf)).2 h
end

protected lemma div_lt_iff (h0 : b ≠ 0 ∨ c ≠ 0) (ht : b ≠ ⊤ ∨ c ≠ ⊤) :
  c / b < a ↔ c < a * b :=
lt_iff_lt_of_le_iff_le $ le_div_iff_mul_le h0 ht

lemma mul_lt_of_lt_div (h : a < b / c) : a * c < b :=
by { contrapose! h, exact ennreal.div_le_of_le_mul h }

lemma inv_le_iff_le_mul : (b = ⊤ → a ≠ 0) → (a = ⊤ → b ≠ 0) → (a⁻¹ ≤ b ↔ 1 ≤ a * b) :=
begin
  cases a; cases b; simp [none_eq_top, some_eq_coe, mul_top, top_mul] {contextual := tt},
  by_cases a = 0; simp [*, -coe_mul, coe_mul.symm, -coe_inv, (coe_inv _).symm, nnreal.inv_le]
end

@[simp] lemma le_inv_iff_mul_le : a ≤ b⁻¹ ↔ a * b ≤ 1 :=
begin
  cases b, { by_cases a = 0; simp [*, none_eq_top, mul_top] },
  by_cases b = 0; simp [*, some_eq_coe, le_div_iff_mul_le],
  suffices : a ≤ 1 / b ↔ a * b ≤ 1, { simpa [div_def, h] },
  exact le_div_iff_mul_le (or.inl (mt coe_eq_coe.1 h)) (or.inl coe_ne_top)
end

lemma mul_inv_cancel (h0 : a ≠ 0) (ht : a ≠ ⊤) : a * a⁻¹ = 1 :=
begin
  lift a to nnreal using ht,
  norm_cast at h0,
  norm_cast,
  exact nnreal.mul_inv_cancel h0
end

lemma inv_mul_cancel (h0 : a ≠ 0) (ht : a ≠ ∞) : a⁻¹ * a = 1 :=
mul_comm a a⁻¹ ▸ mul_inv_cancel h0 ht

lemma mul_le_iff_le_inv {a b r : ennreal} (hr₀ : r ≠ 0) (hr₁ : r ≠ ⊤) : (r * a ≤ b ↔ a ≤ r⁻¹ * b) :=
by rw [← @ennreal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, mul_inv_cancel hr₀ hr₁, one_mul]

lemma le_of_forall_lt_one_mul_lt : ∀{x y : ennreal}, (∀a<1, a * x ≤ y) → x ≤ y :=
forall_ennreal.2 $ and.intro
  (assume r, forall_ennreal.2 $ and.intro
    (assume q h, coe_le_coe.2 $ nnreal.le_of_forall_lt_one_mul_lt $ assume a ha,
      begin rw [← coe_le_coe, coe_mul], exact h _ (coe_lt_coe.2 ha) end)
    (assume h, le_top))
  (assume r hr,
    have ((1 / 2 : nnreal) : ennreal) * ⊤ ≤ r :=
      hr _ (coe_lt_coe.2 ((@nnreal.coe_lt_coe (1/2) 1).1 one_half_lt_one)),
    have ne : ((1 / 2 : nnreal) : ennreal) ≠ 0,
    begin
      rw [(≠), coe_eq_zero],
      refine zero_lt_iff_ne_zero.1 _,
      show 0 < (1 / 2 : ℝ),
      linarith,
    end,
    by rwa [mul_top, if_neg ne] at this)

lemma div_add_div_same {a b c : ennreal} : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma div_self (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
mul_inv_cancel h0 hI

lemma mul_div_cancel (h0 : a ≠ 0) (hI : a ≠ ∞) : (b / a) * a = b :=
by rw [div_def, mul_assoc, inv_mul_cancel h0 hI, mul_one]

lemma mul_div_cancel' (h0 : a ≠ 0) (hI : a ≠ ∞) : a * (b / a) = b :=
by rw [mul_comm, mul_div_cancel h0 hI]

lemma inv_two_add_inv_two : (2:ennreal)⁻¹ + 2⁻¹ = 1 :=
by rw [← two_mul, ← div_def, div_self two_ne_zero two_ne_top]

lemma add_halves (a : ennreal) : a / 2 + a / 2 = a :=
by rw [div_def, ← mul_add, inv_two_add_inv_two, mul_one]

@[simp] lemma div_zero_iff : a / b = 0 ↔ a = 0 ∨ b = ⊤ :=
by simp [div_def, mul_eq_zero]

@[simp] lemma div_pos_iff : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤ :=
by simp [zero_lt_iff_ne_zero, not_or_distrib]

lemma half_pos {a : ennreal} (h : 0 < a) : 0 < a / 2 :=
by simp [ne_of_gt h]

lemma one_half_lt_one : (2⁻¹:ennreal) < 1 := inv_lt_one.2 $ one_lt_two

lemma half_lt_self {a : ennreal} (hz : a ≠ 0) (ht : a ≠ ⊤) : a / 2 < a :=
begin
  lift a to nnreal using ht,
  have h : (2 : ennreal) = ((2 : nnreal) : ennreal), from rfl,
  have h' : (2 : nnreal) ≠ 0, from _root_.two_ne_zero',
  rw [h, ← coe_div h', coe_lt_coe], -- `norm_cast` fails to apply `coe_div`
  norm_cast at hz,
  exact nnreal.half_lt_self hz
end

lemma sub_half (h : a ≠ ∞) : a - a / 2 = a / 2 :=
begin
  lift a to nnreal using h,
  exact sub_eq_of_add_eq (mul_ne_top coe_ne_top $ by simp) (add_halves a)
end

lemma one_sub_inv_two : (1:ennreal) - 2⁻¹ = 2⁻¹ :=
by simpa only [div_def, one_mul] using sub_half one_ne_top

lemma exists_inv_nat_lt {a : ennreal} (h : a ≠ 0) :
  ∃n:ℕ, (n:ennreal)⁻¹ < a :=
@inv_inv a ▸ by simp only [inv_lt_inv, ennreal.exists_nat_gt (inv_ne_top.2 h)]

lemma exists_nat_mul_gt (ha : a ≠ 0) (hb : b ≠ ⊤) :
  ∃ n : ℕ, b < n * a :=
begin
  have : b / a ≠ ⊤, from mul_ne_top hb (inv_ne_top.2 ha),
  refine (ennreal.exists_nat_gt this).imp (λ n hn, _),
  rwa [← ennreal.div_lt_iff (or.inl ha) (or.inr hb)]
end

end inv

section real

lemma to_real_add (ha : a ≠ ⊤) (hb : b ≠ ⊤) : (a+b).to_real = a.to_real + b.to_real :=
begin
  lift a to nnreal using ha,
  lift b to nnreal using hb,
  refl
end

lemma to_real_add_le : (a+b).to_real ≤ a.to_real + b.to_real :=
if ha : a = ⊤ then by simp only [ha, top_add, top_to_real, zero_add, to_real_nonneg]
else if hb : b = ⊤ then by simp only [hb, add_top, top_to_real, add_zero, to_real_nonneg]
else le_of_eq (to_real_add ha hb)

lemma of_real_add {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) :
  ennreal.of_real (p + q) = ennreal.of_real p + ennreal.of_real q :=
by rw [ennreal.of_real, ennreal.of_real, ennreal.of_real, ← coe_add,
       coe_eq_coe, nnreal.of_real_add hp hq]

lemma of_real_add_le {p q : ℝ} : ennreal.of_real (p + q) ≤ ennreal.of_real p + ennreal.of_real q :=
coe_le_coe.2 nnreal.of_real_add_le

@[simp] lemma to_real_le_to_real (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a.to_real ≤ b.to_real ↔ a ≤ b :=
begin
  lift a to nnreal using ha,
  lift b to nnreal using hb,
  norm_cast
end

@[simp] lemma to_real_lt_to_real (ha : a ≠ ⊤) (hb : b ≠ ⊤) : a.to_real < b.to_real ↔ a < b :=
begin
  lift a to nnreal using ha,
  lift b to nnreal using hb,
  norm_cast
end

lemma to_real_max (hr : a ≠ ⊤) (hp : b ≠ ⊤) :
  ennreal.to_real (max a b) = max (ennreal.to_real a) (ennreal.to_real b) :=
(le_total a b).elim
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hr hp).2 h, max_eq_right])
  (λ h, by simp only [h, (ennreal.to_real_le_to_real hp hr).2 h, max_eq_left])

lemma to_nnreal_pos_iff : 0 < a.to_nnreal ↔ (0 < a ∧ a ≠ ∞) :=
begin
  cases a,
  { simp [none_eq_top] },
  { simp [some_eq_coe] }
end

lemma to_real_pos_iff : 0 < a.to_real ↔ (0 < a ∧ a ≠ ∞):=
(nnreal.coe_pos).trans to_nnreal_pos_iff

lemma of_real_le_of_real {p q : ℝ} (h : p ≤ q) : ennreal.of_real p ≤ ennreal.of_real q :=
by simp [ennreal.of_real, nnreal.of_real_le_of_real h]

lemma of_real_le_of_le_to_real {a : ℝ} {b : ennreal} (h : a ≤ ennreal.to_real b) :
  ennreal.of_real a ≤ b :=
(of_real_le_of_real h).trans of_real_to_real_le

@[simp] lemma of_real_le_of_real_iff {p q : ℝ} (h : 0 ≤ q) :
  ennreal.of_real p ≤ ennreal.of_real q ↔ p ≤ q :=
by rw [ennreal.of_real, ennreal.of_real, coe_le_coe, nnreal.of_real_le_of_real_iff h]

@[simp] lemma of_real_lt_of_real_iff {p q : ℝ} (h : 0 < q) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, nnreal.of_real_lt_of_real_iff h]

lemma of_real_lt_of_real_iff_of_nonneg {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real p < ennreal.of_real q ↔ p < q :=
by rw [ennreal.of_real, ennreal.of_real, coe_lt_coe, nnreal.of_real_lt_of_real_iff_of_nonneg hp]

@[simp] lemma of_real_pos {p : ℝ} : 0 < ennreal.of_real p ↔ 0 < p :=
by simp [ennreal.of_real]

@[simp] lemma of_real_eq_zero {p : ℝ} : ennreal.of_real p = 0 ↔ p ≤ 0 :=
by simp [ennreal.of_real]

lemma of_real_le_iff_le_to_real {a : ℝ} {b : ennreal} (hb : b ≠ ⊤) :
  ennreal.of_real a ≤ b ↔ a ≤ ennreal.to_real b :=
begin
  lift b to nnreal using hb,
  simpa [ennreal.of_real, ennreal.to_real] using nnreal.of_real_le_iff_le_coe
end

lemma of_real_lt_iff_lt_to_real {a : ℝ} {b : ennreal} (ha : 0 ≤ a) (hb : b ≠ ⊤) :
  ennreal.of_real a < b ↔ a < ennreal.to_real b :=
begin
  lift b to nnreal using hb,
  simpa [ennreal.of_real, ennreal.to_real] using nnreal.of_real_lt_iff_lt_coe ha
end

lemma le_of_real_iff_to_real_le {a : ennreal} {b : ℝ} (ha : a ≠ ⊤) (hb : 0 ≤ b) :
  a ≤ ennreal.of_real b ↔ ennreal.to_real a ≤ b :=
begin
  lift a to nnreal using ha,
  simpa [ennreal.of_real, ennreal.to_real] using nnreal.le_of_real_iff_coe_le hb
end

lemma to_real_le_of_le_of_real {a : ennreal} {b : ℝ} (hb : 0 ≤ b) (h : a ≤ ennreal.of_real b) :
  ennreal.to_real a ≤ b :=
have ha : a ≠ ⊤, from ne_top_of_le_ne_top of_real_ne_top h,
(le_of_real_iff_to_real_le ha hb).1 h

lemma lt_of_real_iff_to_real_lt {a : ennreal} {b : ℝ} (ha : a ≠ ⊤) :
  a < ennreal.of_real b ↔ ennreal.to_real a < b :=
begin
  lift a to nnreal using ha,
  simpa [ennreal.of_real, ennreal.to_real] using nnreal.lt_of_real_iff_coe_lt
end

lemma of_real_mul {p q : ℝ} (hp : 0 ≤ p) :
  ennreal.of_real (p * q) = (ennreal.of_real p) * (ennreal.of_real q) :=
by { simp only [ennreal.of_real, coe_mul.symm, coe_eq_coe], exact nnreal.of_real_mul hp }

lemma to_real_of_real_mul (c : ℝ) (a : ennreal) (h : 0 ≤ c) :
  ennreal.to_real ((ennreal.of_real c) * a) = c * ennreal.to_real a :=
begin
  cases a,
  { simp only [none_eq_top, ennreal.to_real, top_to_nnreal, nnreal.coe_zero, mul_zero, mul_top],
    by_cases h' : c ≤ 0,
    { rw [if_pos], { simp }, { convert of_real_zero, exact le_antisymm h' h } },
    { rw [if_neg], refl, rw [of_real_eq_zero], assumption } },
  { simp only [ennreal.to_real, ennreal.to_nnreal],
    simp only [some_eq_coe, ennreal.of_real, coe_mul.symm, to_nnreal_coe, nnreal.coe_mul],
    congr, apply nnreal.coe_of_real, exact h }
end

@[simp] lemma to_real_mul_top (a : ennreal) : ennreal.to_real (a * ⊤) = 0 :=
begin
  by_cases h : a = 0,
  { rw [h, zero_mul, zero_to_real] },
  { rw [mul_top, if_neg h, top_to_real] }
end

@[simp] lemma to_real_top_mul (a : ennreal) : ennreal.to_real (⊤ * a) = 0 :=
by { rw mul_comm, exact to_real_mul_top _ }

lemma to_real_eq_to_real (ha : a < ⊤) (hb : b < ⊤) :
  ennreal.to_real a = ennreal.to_real b ↔ a = b :=
begin
  rw ennreal.lt_top_iff_ne_top at *,
  split,
  { assume h, apply le_antisymm,
      rw ← to_real_le_to_real ha hb, exact le_of_eq h,
      rw ← to_real_le_to_real hb ha, exact le_of_eq h.symm },
  { assume h, rw h }
end

lemma to_real_mul_to_real :
  (ennreal.to_real a) * (ennreal.to_real b) = ennreal.to_real (a * b) :=
begin
  by_cases ha : a = ⊤,
  { rw ha, simp },
  by_cases hb : b = ⊤,
  { rw hb, simp },
  have ha : ennreal.of_real (ennreal.to_real a) = a := of_real_to_real ha,
  have hb : ennreal.of_real (ennreal.to_real b) = b := of_real_to_real hb,
  conv_rhs { rw [← ha, ← hb, ← of_real_mul to_real_nonneg] },
  rw [to_real_of_real (mul_nonneg to_real_nonneg to_real_nonneg)]
end

end real

section infi
variables {ι : Sort*} {f g : ι → ennreal}

lemma infi_add : infi f + a = ⨅i, f i + a :=
le_antisymm
  (le_infi $ assume i, add_le_add (infi_le _ _) $ le_refl _)
  (ennreal.sub_le_iff_le_add.1 $ le_infi $ assume i, ennreal.sub_le_iff_le_add.2 $ infi_le _ _)

lemma supr_sub : (⨆i, f i) - a = (⨆i, f i - a) :=
le_antisymm
  (ennreal.sub_le_iff_le_add.2 $ supr_le $ assume i, ennreal.sub_le_iff_le_add.1 $ le_supr _ i)
  (supr_le $ assume i, ennreal.sub_le_sub (le_supr _ _) (le_refl a))

lemma sub_infi : a - (⨅i, f i) = (⨆i, a - f i) :=
begin
  refine (eq_of_forall_ge_iff $ λ c, _),
  rw [ennreal.sub_le_iff_le_add, add_comm, infi_add],
  simp [ennreal.sub_le_iff_le_add, sub_eq_add_neg, add_comm],
end

lemma Inf_add {s : set ennreal} : Inf s + a = ⨅b∈s, b + a :=
by simp [Inf_eq_infi, infi_add]

lemma add_infi {a : ennreal} : a + infi f = ⨅b, a + f b :=
by rw [add_comm, infi_add]; simp [add_comm]

lemma infi_add_infi (h : ∀i j, ∃k, f k + g k ≤ f i + g j) : infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅ a a', f a + g a') :
    le_infi $ assume a, le_infi $ assume a',
      let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... ≤ infi f + infi g :
    by simp [add_infi, infi_add, -add_comm, -le_infi_iff]; exact le_refl _

lemma infi_sum {f : ι → α → ennreal} {s : finset α} [nonempty ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, ∑ a in s, f i a) = ∑ a in s, ⨅i, f i a :=
finset.induction_on s (by simp) $ assume a s ha ih,
  have ∀ (i j : ι), ∃ (k : ι), f k a + ∑ b in s, f k b ≤ f i a + ∑ b in s, f j b,
    from assume i j,
    let ⟨k, hk⟩ := h (insert a s) i j in
    ⟨k, add_le_add (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum $
      assume a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩,
  by simp [ha, ih.symm, infi_add_infi this]


lemma infi_mul {ι} [nonempty ι] {f : ι → ennreal} {x : ennreal} (h : x ≠ ⊤) :
  infi f * x = ⨅i, f i * x :=
begin
  by_cases h2 : x = 0, simp only [h2, mul_zero, infi_const],
  refine le_antisymm
    (le_infi $ λ i, mul_right_mono $ infi_le _ _)
    ((div_le_iff_le_mul (or.inl h2) $ or.inl h).mp $ le_infi $
      λ i, (div_le_iff_le_mul (or.inl h2) $ or.inl h).mpr $ infi_le _ _)
end

lemma mul_infi {ι} [nonempty ι] {f : ι → ennreal} {x : ennreal} (h : x ≠ ⊤) :
  x * infi f = ⨅i, x * f i :=
by { rw [mul_comm, infi_mul h], simp only [mul_comm], assumption }

/-! `supr_mul`, `mul_supr` and variants are in `topology.instances.ennreal`. -/

end infi

section supr

lemma supr_coe_nat : (⨆n:ℕ, (n : ennreal)) = ⊤ :=
(supr_eq_top _).2 $ assume b hb, ennreal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

end supr

end ennreal

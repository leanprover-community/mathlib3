/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Extended non-negative reals
-/
import data.real.nnreal order.bounds tactic.norm_num
noncomputable theory
open classical set lattice

local attribute [instance] prop_decidable
variables {α : Type*} {β : Type*}

/-- The extended nonnegative real numbers. This is usually denoted [0, ∞],
  and is relevant as the codomain of a measure. -/
def ennreal := with_top nnreal

local notation `∞` := (⊤ : ennreal)

namespace ennreal
variables {a b c d : ennreal} {r p q : nnreal}

instance : canonically_ordered_comm_semiring ennreal := by unfold ennreal; apply_instance
instance : decidable_linear_order ennreal := by unfold ennreal; apply_instance
instance : complete_linear_order ennreal := by unfold ennreal; apply_instance
instance : inhabited ennreal := ⟨0⟩

instance : densely_ordered ennreal := with_top.densely_ordered

instance : has_coe nnreal ennreal := ⟨ option.some ⟩

lemma none_eq_top : (none : ennreal) = (⊤ : ennreal) := rfl
lemma some_eq_coe (a : nnreal) : (some a : ennreal) = (↑a : ennreal) := rfl

/-- `to_nnreal x` returns `x` if it is real, otherwise 0. -/
protected def to_nnreal : ennreal → nnreal
| (some r) := r
| none := 0

@[simp] lemma to_nnreal_coe : (r : ennreal).to_nnreal = r := rfl

@[simp] lemma coe_to_nnreal : ∀{a:ennreal}, a ≠ ∞ → ↑(a.to_nnreal) = a
| (some r) h := rfl
| none     h := (h rfl).elim

lemma coe_to_nnreal_le_self : ∀{a:ennreal}, ↑(a.to_nnreal) ≤ a
| (some r) := by rw [some_eq_coe, to_nnreal_coe]; exact le_refl _
| none     := le_top

@[simp] lemma top_to_nnreal : ∞.to_nnreal = 0 := rfl
@[simp] lemma zero_to_nnreal : (0 : ennreal).to_nnreal = 0 := rfl

lemma forall_ennreal {p : ennreal → Prop} : (∀a, p a) ↔ (∀r:nnreal, p r) ∧ p ∞ :=
⟨assume h, ⟨assume r, h _, h _⟩,
  assume ⟨h₁, h₂⟩ a, match a with some r := h₁ _ | none := h₂ end⟩

@[simp] lemma coe_zero : ↑(0 : nnreal) = (0 : ennreal) := rfl
@[simp] lemma coe_one : ↑(1 : nnreal) = (1 : ennreal) := rfl

lemma to_nnreal_eq_zero_iff (x : ennreal) : x.to_nnreal = 0 ↔ x = 0 ∨ x = ⊤ :=
⟨begin
  cases x,
  { simp [none_eq_top] },
  { have A : some (0:nnreal) = (0:ennreal) := rfl,
    simp [ennreal.to_nnreal, A] {contextual := tt} }
end,
by intro h; cases h; simp [h]⟩

@[simp] lemma coe_ne_top : (r : ennreal) ≠ ∞ := with_top.coe_ne_top
@[simp] lemma top_ne_coe : ∞ ≠ (r : ennreal) := with_top.top_ne_coe

@[simp] lemma zero_ne_top : 0 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_zero : ∞ ≠ 0 := top_ne_coe

@[simp] lemma one_ne_top : 1 ≠ ∞ := coe_ne_top
@[simp] lemma top_ne_one : ∞ ≠ 1 := top_ne_coe

@[simp] lemma coe_eq_coe : (↑r : ennreal) = ↑q ↔ r = q := with_top.coe_eq_coe
@[simp] lemma coe_le_coe : (↑r : ennreal) ≤ ↑q ↔ r ≤ q := with_top.coe_le_coe
@[simp] lemma coe_lt_coe : (↑r : ennreal) < ↑q ↔ r < q := with_top.coe_lt_coe

@[simp] lemma coe_eq_zero : (↑r : ennreal) = 0 ↔ r = 0 := coe_eq_coe
@[simp] lemma zero_eq_coe : 0 = (↑r : ennreal) ↔ 0 = r := coe_eq_coe
@[simp] lemma coe_eq_one : (↑r : ennreal) = 1 ↔ r = 1 := coe_eq_coe
@[simp] lemma one_eq_coe : 1 = (↑r : ennreal) ↔ 1 = r := coe_eq_coe
@[simp] lemma coe_nonneg : 0 ≤ (↑r : ennreal) ↔ 0 ≤ r := coe_le_coe
@[simp] lemma coe_pos : 0 < (↑r : ennreal) ↔ 0 < r := coe_lt_coe

@[simp] lemma coe_add : ↑(r + p) = (r + p : ennreal) := with_top.coe_add
@[simp] lemma coe_mul : ↑(r * p) = (r * p : ennreal) := with_top.coe_mul

@[simp] lemma coe_bit0 : (↑(bit0 r) : ennreal) = bit0 r := coe_add
@[simp] lemma coe_bit1 : (↑(bit1 r) : ennreal) = bit1 r := by simp [bit1]

@[simp] lemma add_top : a + ∞ = ∞ := with_top.add_top
@[simp] lemma top_add : ∞ + a = ∞ := with_top.top_add

instance : is_semiring_hom (coe : nnreal → ennreal) :=
by refine_struct {..}; simp

lemma add_eq_top : a + b = ∞ ↔ a = ∞ ∨ b = ∞ := with_top.add_eq_top _ _
lemma add_lt_top : a + b < ∞ ↔ a < ∞ ∧ b < ∞ := with_top.add_lt_top _ _

/- rw has trouble with the generic lt_top_iff_ne_top and bot_lt_iff_ne_bot
(contrary to erw). This is solved with the next lemmas -/
protected lemma lt_top_iff_ne_top : a < ∞ ↔ a ≠ ∞ := lt_top_iff_ne_top
protected lemma bot_lt_iff_ne_bot : 0 < a ↔ a ≠ 0 := bot_lt_iff_ne_bot

lemma mul_top : a * ∞ = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.mul_top h } end

lemma top_mul : ∞ * a = (if a = 0 then 0 else ∞) :=
begin split_ifs, { simp [h] }, { exact with_top.top_mul h } end

@[simp] lemma top_mul_top : ∞ * ∞ = ∞ := with_top.top_mul_top

@[simp] lemma coe_finset_sum {s : finset α} {f : α → nnreal} : ↑(s.sum f) = (s.sum (λa, f a) : ennreal) :=
(finset.sum_hom coe).symm

@[simp] lemma coe_finset_prod {s : finset α} {f : α → nnreal} : ↑(s.prod f) = (s.prod (λa, f a) : ennreal) :=
(finset.prod_hom coe).symm

@[simp] lemma bot_eq_zero : (⊥ : ennreal) = 0 := rfl
section order

@[simp] lemma coe_lt_top : coe r < ∞ := with_top.coe_lt_top r
@[simp] lemma not_top_le_coe : ¬ (⊤:ennreal) ≤ ↑r := with_top.not_top_le_coe r
@[simp] lemma zero_lt_coe_iff : 0 < (↑p : ennreal) ↔ 0 < p := coe_lt_coe
@[simp] lemma one_le_coe_iff : (1:ennreal) ≤ ↑r ↔ 1 ≤ r := coe_le_coe
@[simp] lemma coe_le_one_iff : ↑r ≤ (1:ennreal) ↔ r ≤ 1 := coe_le_coe
@[simp] lemma coe_lt_one_iff : (↑p : ennreal) < 1 ↔ p < 1 := coe_lt_coe
@[simp] lemma one_lt_zero_iff : 1 < (↑p : ennreal) ↔ 1 < p := coe_lt_coe
@[simp] lemma coe_nat (n : nat) : ((n : nnreal) : ennreal) = n := with_top.coe_nat n
@[simp] lemma nat_ne_top (n : nat) : (n : ennreal) ≠ ⊤ := with_top.nat_ne_top n
@[simp] lemma top_ne_nat (n : nat) : (⊤ : ennreal) ≠ n := with_top.top_ne_nat n

lemma le_coe_iff : a ≤ ↑r ↔ (∃p:nnreal, a = p ∧ p ≤ r) := with_top.le_coe_iff r a
lemma coe_le_iff : ↑r ≤ a ↔ (∀p:nnreal, a = p → r ≤ p) := with_top.coe_le_iff r a

lemma lt_iff_exists_coe : a < b ↔ (∃p:nnreal, a = p ∧ ↑p < b) := with_top.lt_iff_exists_coe a b

-- TODO: move to canonically ordered semiring ...
protected lemma zero_lt_one : 0 < (1 : ennreal) := zero_lt_coe_iff.mpr zero_lt_one

@[simp] lemma not_lt_zero : ¬ a < 0 := by simp

lemma add_lt_add_iff_left : a < ⊤ → (a + c < a + b ↔ c < b) :=
with_top.add_lt_add_iff_left

lemma add_lt_add_iff_right : a < ⊤ → (c + a < b + a ↔ c < b) :=
with_top.add_lt_add_iff_right

lemma lt_add_right (ha : a < ⊤) (hb : 0 < b) : a < a + b :=
by rwa [← add_lt_add_iff_left ha, add_zero] at hb

lemma le_of_forall_epsilon_le : ∀{a b : ennreal}, (∀ε:nnreal, ε > 0 → b < ∞ → a ≤ b + ε) → a ≤ b
| a    none     h := le_top
| none (some a) h :=
  have (⊤:ennreal) ≤ ↑a + ↑(1:nnreal), from h 1 zero_lt_one coe_lt_top,
  by rw [← coe_add] at this; exact (not_top_le_coe this).elim
| (some a) (some b) h :=
    by simp only [none_eq_top, some_eq_coe, coe_add.symm, coe_le_coe, coe_lt_top, true_implies_iff] at *;
      exact nnreal.le_of_forall_epsilon_le h

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
  a < b ↔ (∃r:ℝ, 0 ≤ r ∧ a < nnreal.of_real r ∧ (nnreal.of_real r:ennreal) < b) :=
⟨λ h, let ⟨q, q0, aq, qb⟩ := ennreal.lt_iff_exists_rat_btwn.1 h in
  ⟨q, rat.cast_nonneg.2 q0, aq, qb⟩,
λ ⟨q, q0, qa, qb⟩, lt_trans qa qb⟩

protected lemma exists_nat_gt {r : ennreal} (h : r ≠ ⊤) : ∃n:ℕ, r < n :=
begin
  rcases lt_iff_exists_coe.1 (lt_top_iff_ne_top.2 h) with ⟨r, rfl, hb⟩,
  rcases exists_nat_gt r with ⟨n, hn⟩,
  refine ⟨n, _⟩,
  rwa [← ennreal.coe_nat, ennreal.coe_lt_coe],
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
  have J : ↑a'R + ↑b'R ≤ c + d := add_le_add' (le_of_lt a'c) (le_of_lt b'd),
  apply lt_of_lt_of_le I J
end

end order

section complete_lattice

lemma coe_Sup {s : set nnreal} : bdd_above s → (↑(Sup s) : ennreal) = (⨆a∈s, ↑a) := with_top.coe_Sup
lemma coe_Inf {s : set nnreal} : s ≠ ∅ → (↑(Inf s) : ennreal) = (⨅a∈s, ↑a) := with_top.coe_Inf

@[simp] lemma top_mem_upper_bounds {s : set ennreal} : ∞ ∈ upper_bounds s :=
assume x hx, le_top

lemma coe_mem_upper_bounds {s : set nnreal} :
  ↑r ∈ upper_bounds ((coe : nnreal → ennreal) '' s) ↔ r ∈ upper_bounds s :=
by simp [upper_bounds, ball_image_iff, -mem_image, *] {contextual := tt}

end complete_lattice

section mul

lemma mul_eq_mul_left : a ≠ 0 → a ≠ ⊤ → (a * b = a * c ↔ b = c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm,
      nnreal.mul_eq_mul_left] {contextual := tt},
end

lemma mul_le_mul_left : a ≠ 0 → a ≠ ⊤ → (a * b ≤ a * c ↔ b ≤ c) :=
begin
  cases a; cases b; cases c;
    simp [none_eq_top, some_eq_coe, mul_top, top_mul, -coe_mul, coe_mul.symm] {contextual := tt},
  assume h, exact mul_le_mul_left (zero_lt_iff_ne_zero.2 h)
end

lemma mul_eq_top {a b : ennreal} : a * b = ⊤ ↔ (a ≠ 0 ∧ b = ⊤) ∨ (a = ⊤ ∧ b ≠ 0) :=
with_top.mul_eq_top_iff

lemma mul_eq_zero {a b : ennreal} : a * b = 0 ↔ a = 0 ∨ b = 0 :=
canonically_ordered_comm_semiring.mul_eq_zero_iff _ _

end mul

section sub
instance : has_sub ennreal := ⟨λa b, Inf {d | a ≤ d + b}⟩

lemma coe_sub : ↑(p - r) = (↑p:ennreal) - r :=
le_antisymm
  (le_Inf $ assume b (hb : ↑p ≤ b + r), coe_le_iff.2 $
    by rintros d rfl; rwa [← coe_add, coe_le_coe, ← nnreal.sub_le_iff_le_add] at hb)
  (Inf_le $ show (↑p : ennreal) ≤ ↑(p - r) + ↑r,
    by rw [← coe_add, coe_le_coe, ← nnreal.sub_le_iff_le_add])

@[simp] lemma top_sub_coe : ∞ - ↑r = ∞ :=
top_unique $ le_Inf $ by simp [add_eq_top]

@[simp] lemma sub_eq_zero_of_le (h : a ≤ b) : a - b = 0 :=
le_antisymm (Inf_le $ le_add_left h) (zero_le _)

@[simp] lemma zero_sub : 0 - a = 0 :=
le_antisymm (Inf_le $ zero_le _) (zero_le _)

@[simp] lemma sub_infty : a - ∞ = 0 :=
le_antisymm (Inf_le $ by simp) (zero_le _)

lemma sub_le_sub (h₁ : a ≤ b) (h₂ : d ≤ c) : a - c ≤ b - d :=
Inf_le_Inf $ assume e (h : b ≤ e + d),
  calc a ≤ b : h₁
    ... ≤ e + d : h
    ... ≤ e + c : add_le_add' (le_refl _) h₂

@[simp] lemma add_sub_self : ∀{a b : ennreal}, b < ∞ → (a + b) - b = a
| a        none     := by simp [none_eq_top]
| none     (some b) := by simp [none_eq_top, some_eq_coe]
| (some a) (some b) :=
  by simp [some_eq_coe]; rw [← coe_add, ← coe_sub, coe_eq_coe, nnreal.add_sub_cancel]

@[simp] lemma add_sub_self' (h : a < ∞) : (a + b) - a = b :=
by rw [add_comm, add_sub_self h]

lemma add_left_inj (h : a < ∞) : a + b = a + c ↔ b = c :=
⟨λ e, by simpa [h] using congr_arg (λ x, x - a) e, congr_arg _⟩

lemma add_right_inj (h : a < ∞) : b + a = c + a ↔ b = c :=
by rw [add_comm, add_comm c, add_left_inj h]

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

@[simp] protected lemma sub_le_iff_le_add : a - b ≤ c ↔ a ≤ c + b :=
iff.intro
  (assume h : a - b ≤ c,
    calc a ≤ (a - b) + b : by rw [sub_add_self_eq_max]; exact le_max_left _ _
      ... ≤ c + b : add_le_add' h (le_refl _))
  (assume h : a ≤ c + b,
    calc a - b ≤ (c + b) - b : sub_le_sub h (le_refl _)
      ... ≤ c : Inf_le (le_refl (c + b)))

@[simp] lemma sub_eq_zero_iff_le : a - b = 0 ↔ a ≤ b :=
by simpa [-ennreal.sub_le_iff_le_add] using @ennreal.sub_le_iff_le_add a b 0

@[simp] lemma zero_lt_sub_iff_lt : 0 < a - b ↔ b < a :=
by simpa [ennreal.bot_lt_iff_ne_bot, -sub_eq_zero_iff_le] using not_iff_not.2 (@sub_eq_zero_iff_le a b)

lemma sub_le_self (a b : ennreal) : a - b ≤ a :=
ennreal.sub_le_iff_le_add.2 $ le_add_of_nonneg_right' $ zero_le _

@[simp] lemma sub_zero : a - 0 = a :=
eq.trans (add_zero (a - 0)).symm $ by simp

lemma sub_sub_cancel (h : a < ∞) (h2 : b ≤ a) : a - (a - b) = b :=
by rw [← add_right_inj (lt_of_le_of_lt (sub_le_self _ _) h),
  sub_add_cancel_of_le (sub_le_self _ _), add_sub_cancel_of_le h2]

end sub

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
  rwa [add_right_inj, bit0_inj] at h,
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

@[simp] lemma inv_zero : (0 : ennreal)⁻¹ = ∞ :=
show Inf {b : ennreal | 1 ≤ 0 * b} = ∞, by simp; refl

@[simp] lemma inv_top : (∞ : ennreal)⁻¹ = 0 :=
bot_unique $ le_of_forall_le_of_dense $ λ a (h : a > 0), Inf_le $ by simp [*, ne_of_gt h, top_mul]

@[simp] lemma coe_inv (hr : r ≠ 0) : (↑r⁻¹ : ennreal) = (↑r)⁻¹ :=
le_antisymm
  (le_Inf $ assume b (hb : 1 ≤ ↑r * b), coe_le_iff.2 $
    by rintros b rfl; rwa [← coe_mul, ← coe_one, coe_le_coe, ← nnreal.inv_le hr] at hb)
  (Inf_le $ by simp; rw [← coe_mul, nnreal.mul_inv_cancel hr]; exact le_refl 1)

@[simp] lemma coe_div (hr : r ≠ 0) : (↑(p / r) : ennreal) = p / r :=
show ↑(p * r⁻¹) = ↑p * (↑r)⁻¹, by rw [coe_mul, coe_inv hr]

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a :=
by by_cases a = 0; cases a; simp [*, none_eq_top, some_eq_coe,
  -coe_inv, (coe_inv _).symm] at *

@[simp] lemma inv_eq_top : a⁻¹ = ∞ ↔ a = 0 :=
by by_cases a = 0; cases a; simp [*, none_eq_top, some_eq_coe,
  -coe_inv, (coe_inv _).symm] at *

lemma inv_ne_top : a⁻¹ ≠ ∞ ↔ a ≠ 0 := by simp

@[simp] lemma inv_eq_zero : a⁻¹ = 0 ↔ a = ∞ :=
by rw [← inv_eq_top, inv_inv]

lemma inv_ne_zero : a⁻¹ ≠ 0 ↔ a ≠ ∞ := by simp

lemma le_div_iff_mul_le : ∀{b}, b ≠ 0 → b ≠ ⊤ → (a ≤ c / b ↔ a * b ≤ c)
| none     h0 ht := (ht rfl).elim
| (some r) h0 ht :=
  begin
    have hr : r ≠ 0, from mt coe_eq_coe.2 h0,
    rw [← ennreal.mul_le_mul_left h0 ht],
    suffices : ↑r * a ≤ (↑r  * ↑r⁻¹) * c ↔ a * ↑r ≤ c,
    { simpa [some_eq_coe, div_def, hr, mul_left_comm, mul_comm, mul_assoc] },
    rw [← coe_mul, nnreal.mul_inv_cancel hr, coe_one, one_mul, mul_comm]
  end

lemma div_le_iff_le_mul (hb0 : b ≠ 0) (hbt : b ≠ ⊤) : a / b ≤ c ↔ a ≤ c * b :=
suffices a * b⁻¹ ≤ c ↔ a ≤ c / b⁻¹, by simpa [div_def],
(le_div_iff_mul_le (inv_ne_zero.2 hbt) (inv_ne_top.2 hb0)).symm

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
  exact le_div_iff_mul_le (mt coe_eq_coe.1 h) coe_ne_top
end

lemma mul_inv_cancel : ∀{r : ennreal}, r ≠ 0 → r ≠ ⊤ → r * r⁻¹ = 1 :=
begin
  refine forall_ennreal.2 ⟨λ r, _, _⟩; simp [-coe_inv, (coe_inv _).symm] {contextual := tt},
  assume h, rw [← ennreal.coe_mul, nnreal.mul_inv_cancel h, coe_one]
end

lemma mul_le_if_le_inv {a b r : ennreal} (hr₀ : r ≠ 0) (hr₁ : r ≠ ⊤) : (r * a ≤ b ↔ a ≤ r⁻¹ * b) :=
by rw [← @ennreal.mul_le_mul_left _ a _ hr₀ hr₁, ← mul_assoc, mul_inv_cancel hr₀ hr₁, one_mul]

lemma le_of_forall_lt_one_mul_lt : ∀{x y : ennreal}, (∀a<1, a * x ≤ y) → x ≤ y :=
forall_ennreal.2 $ and.intro
  (assume r, forall_ennreal.2 $ and.intro
    (assume q h, coe_le_coe.2 $ nnreal.le_of_forall_lt_one_mul_lt $ assume a ha,
      begin rw [← coe_le_coe, coe_mul], exact h _ (coe_lt_coe.2 ha) end)
    (assume h, le_top))
  (assume r hr,
    have ((1 / 2 : nnreal) : ennreal) * ⊤ ≤ r :=
      hr _ (coe_lt_coe.2 ((@nnreal.coe_lt (1/2) 1).2 one_half_lt_one)),
    have ne : ((1 / 2 : nnreal) : ennreal) ≠ 0,
    begin
      rw [(≠), coe_eq_zero],
      refine zero_lt_iff_ne_zero.1 _,
      show 0 < (1 / 2 : ℝ),
      exact div_pos zero_lt_one two_pos
    end,
    by rwa [mul_top, if_neg ne] at this)

lemma div_add_div_same {a b c : ennreal} : a / c + b / c = (a + b) / c :=
eq.symm $ right_distrib a b (c⁻¹)

lemma div_self {a : ennreal} (h0 : a ≠ 0) (hI : a ≠ ∞) : a / a = 1 :=
have A : 1 ≤ a / a := by simp [le_div_iff_mul_le h0 hI, le_refl],
have B : a / a ≤ 1 := by simp [div_le_iff_le_mul h0 hI, le_refl],
le_antisymm B A

lemma add_halves (a : ennreal) : a / 2 + a / 2 = a :=
have ¬((2 : nnreal) : ennreal) = (0 : nnreal) := by rw [coe_eq_coe]; norm_num,
have A : (2:ennreal) * 2⁻¹ = 1 := by rw [←div_def, div_self]; [assumption, apply coe_ne_top],
calc
   a / 2 + a / 2 = (a + a) / 2 : by rw div_add_div_same
    ... = (a * 1 + a * 1) / 2  : by rw mul_one
    ... = (a * (1 + 1)) / 2    : by rw left_distrib
    ... = (a * 2) / 2          : by rw one_add_one_eq_two
    ... = (a * 2) * 2⁻¹        : by rw div_def
    ... = a * (2 * 2⁻¹)        : by rw mul_assoc
    ... = a * 1                : by rw A
    ... = a                    : by rw mul_one

@[simp] lemma div_zero_iff {a b : ennreal} : a / b = 0 ↔ a = 0 ∨ b = ⊤ :=
by simp [div_def, mul_eq_zero]

@[simp] lemma div_pos_iff {a b : ennreal} : 0 < a / b ↔ a ≠ 0 ∧ b ≠ ⊤ :=
by simp [zero_lt_iff_ne_zero, not_or_distrib]

lemma half_pos {a : ennreal} (h : 0 < a) : 0 < a / 2 :=
by simp [ne_of_gt h]

lemma half_lt_self {a : ennreal} (hz : a ≠ 0) (ht : a ≠ ⊤) : a / 2 < a :=
begin
  cases a,
  { cases ht none_eq_top },
  { simp [some_eq_coe] at hz,
    simpa [-coe_lt_coe, coe_div two_ne_zero'] using
      coe_lt_coe.2 (nnreal.half_lt_self hz) }
end

lemma exists_inv_nat_lt {a : ennreal} (h : a ≠ 0) :
  ∃n:ℕ, (n:ennreal)⁻¹ < a :=
begin
  rcases dense (bot_lt_iff_ne_bot.2 h) with ⟨b, bz, ba⟩,
  have bz' : b ≠ 0 := bot_lt_iff_ne_bot.1 bz,
  have : b⁻¹ ≠ ⊤ := by simp [bz'],
  rcases ennreal.exists_nat_gt this with ⟨n, bn⟩,
  have I : ((n : ℕ) : ennreal)⁻¹ ≤ b := begin
    rw [ennreal.inv_le_iff_le_mul, mul_comm, ← ennreal.inv_le_iff_le_mul],
    exact le_of_lt bn,
    simp only [h, ennreal.nat_ne_top, forall_prop_of_false, ne.def, not_false_iff],
    exact λ_, ne_bot_of_gt bn,
    exact λ_, ne_bot_of_gt bn,
    exact λ_, bz'
  end,
  exact ⟨n, lt_of_le_of_lt I ba⟩
end
end inv

section infi
variables {ι : Sort*} {f g : ι → ennreal}

lemma infi_add : infi f + a = ⨅i, f i + a :=
le_antisymm
  (le_infi $ assume i, add_le_add' (infi_le _ _) $ le_refl _)
  (ennreal.sub_le_iff_le_add.1 $ le_infi $ assume i, ennreal.sub_le_iff_le_add.2 $ infi_le _ _)

lemma supr_sub : (⨆i, f i) - a = (⨆i, f i - a) :=
le_antisymm
  (ennreal.sub_le_iff_le_add.2 $ supr_le $ assume i, ennreal.sub_le_iff_le_add.1 $ le_supr _ i)
  (supr_le $ assume i, ennreal.sub_le_sub (le_supr _ _) (le_refl a))

lemma sub_infi : a - (⨅i, f i) = (⨆i, a - f i) :=
begin
  refine (eq_of_forall_ge_iff $ λ c, _),
  rw [ennreal.sub_le_iff_le_add, add_comm, infi_add],
  simp [ennreal.sub_le_iff_le_add]
end

lemma Inf_add {s : set ennreal} : Inf s + a = ⨅b∈s, b + a :=
by simp [Inf_eq_infi, infi_add]

lemma add_infi {a : ennreal} : a + infi f = ⨅b, a + f b :=
by rw [add_comm, infi_add]; simp

lemma infi_add_infi (h : ∀i j, ∃k, f k + g k ≤ f i + g j) : infi f + infi g = (⨅a, f a + g a) :=
suffices (⨅a, f a + g a) ≤ infi f + infi g,
  from le_antisymm (le_infi $ assume a, add_le_add' (infi_le _ _) (infi_le _ _)) this,
calc (⨅a, f a + g a) ≤ (⨅ a a', f a + g a') :
    le_infi $ assume a, le_infi $ assume a',
      let ⟨k, h⟩ := h a a' in infi_le_of_le k h
  ... ≤ infi f + infi g :
    by simp [add_infi, infi_add, -add_comm, -le_infi_iff]; exact le_refl _

lemma infi_sum {f : ι → α → ennreal} {s : finset α} [nonempty ι]
  (h : ∀(t : finset α) (i j : ι), ∃k, ∀a∈t, f k a ≤ f i a ∧ f k a ≤ f j a) :
  (⨅i, s.sum (f i)) = s.sum (λa, ⨅i, f i a) :=
finset.induction_on s (by simp) $ assume a s ha ih,
  have ∀ (i j : ι), ∃ (k : ι), f k a + s.sum (f k) ≤ f i a + s.sum (f j),
    from assume i j,
    let ⟨k, hk⟩ := h (insert a s) i j in
    ⟨k, add_le_add' (hk a (finset.mem_insert_self _ _)).left $ finset.sum_le_sum' $
      assume a ha, (hk _ $ finset.mem_insert_of_mem ha).right⟩,
  by simp [ha, ih.symm, infi_add_infi this]

end infi

section supr

lemma supr_coe_nat : (⨆n:ℕ, (n : ennreal)) = ⊤ :=
(lattice.supr_eq_top _).2 $ assume b hb, ennreal.exists_nat_gt (lt_top_iff_ne_top.1 hb)

end supr

end ennreal

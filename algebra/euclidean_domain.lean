/-
Copyright (c) 2018 Louis Carlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Louis Carlin

Euclidean domains and Euclidean algorithm (extended to come)
A lot is based on pre-existing code in mathlib for natural number gcds
-/
import tactic.ring

universe u

class euclidean_domain (α : Type u) [decidable_eq α] extends integral_domain α :=
(quotient : α → α → α)
(remainder : α → α → α)
(quotient_mul_add_remainder_eq : ∀ a b, (quotient a b) * b + (remainder a b) = a) -- This could be changed to the same order as int.mod_add_div. We normally write qb+r rather than r + qb though.
(valuation : α → ℕ)
(valuation_remainder_lt : ∀ a b, b ≠ 0 → valuation (remainder a b) <  valuation b)
(le_valuation_mul : ∀ a b, b ≠ 0 → valuation a ≤ valuation (a*b))

/-
le_valuation_mul is often not a required in definitions of a euclidean domain since given the other properties we can show there is a (noncomputable) euclidean domain α with the property le_valuation_mul.
So potentially this definition could be split into two different ones (euclidean_domain_weak and euclidean_domain_strong) with a noncomputable function from weak to strong.
I've currently divided the lemmas into strong and weak depending on whether they require le_valuation_mul or not.
-/

namespace euclidean_domain
variable {α : Type u}
variables [decidable_eq α] [euclidean_domain α]

instance : has_div α := ⟨quotient⟩

instance : has_mod α := ⟨remainder⟩

instance : has_sizeof α := ⟨valuation⟩

lemma gcd_decreasing (a b : α) (w : a ≠ 0) : has_well_founded.r (b % a) a := valuation_remainder_lt b a w

def gcd : α → α → α
| a b := if a_zero : a = 0 then b
  else have h : has_well_founded.r (b % a) a := gcd_decreasing a b a_zero,
    gcd (b%a) a

/- weak lemmas -/

@[simp] lemma mod_zero (a : α) : a % 0 = a := by simpa using
quotient_mul_add_remainder_eq a 0

lemma dvd_mod_self (a : α) : a ∣ a % a :=
begin
  let d := (a/a)*a, -- ring tactic can't solve things without this
  have : a%a = a - (a/a)*a, from
    calc
      a%a = d + a%a  - d : by ring
      ... = (a/a)*a + a%a - (a/a)*a : by dsimp [d]; refl
      ... = a - (a/a)*a : by simp [(%), (/), quotient_mul_add_remainder_eq a a],
  rw this,
  exact dvd_sub (dvd_refl a) (dvd_mul_left a (a/a)),
end

lemma mod_lt  : ∀ (a : α) {b : α}, valuation b > valuation (0:α) →  valuation (a%b) < valuation b :=
begin
  intros a b h,
  by_cases b_zero : (b=0),
  { rw b_zero at h,
    have := lt_irrefl (valuation (0:α)),
    contradiction },
  { exact valuation_remainder_lt a b b_zero }
end

lemma neq_zero_lt_mod_lt (a b : α) :  b ≠ 0 → valuation (a%b) < valuation b
| hnb := valuation_remainder_lt a b hnb

lemma dvd_mod {a b c : α} : c ∣ a → c ∣ b → c ∣ a % b :=
begin
  intros dvd_a dvd_b,
  have : remainder a b = a - quotient a b * b, from
  calc
    a%b = quotient a b * b + a%b - quotient a b * b : by ring
    ... = a - quotient a b * b : by {dsimp[(%)]; rw (quotient_mul_add_remainder_eq a b)},
  dsimp [(%)],
  rw this,
  exact dvd_sub dvd_a (dvd_mul_of_dvd_right dvd_b (a/b)),
end

/- strong lemmas -/

lemma val_lt_one (a : α) : valuation a < valuation (1:α) → a = 0 :=
begin
  intro a_lt,
  by_cases a = 0,
  { exact h },
  { have := le_valuation_mul (1:α) a h,
    simp at this,
    have := not_le_of_lt a_lt,
    contradiction }
end

lemma val_dvd_le : ∀ a b : α, b ∣ a → a ≠ 0 → valuation b ≤ valuation a
| _ b ⟨d, rfl⟩ ha :=
begin
  by_cases d = 0,
  { simp[h] at ha,
    contradiction },
  { exact le_valuation_mul b d h }
end

@[simp] lemma mod_one (a : α) : a % 1 = 0 :=
val_lt_one _ (valuation_remainder_lt a 1 one_ne_zero)

@[simp] lemma zero_mod (b : α) : 0 % b = 0 :=
begin
  have h : remainder 0 b = b * (-quotient 0 b ), from
    calc
      remainder 0 b = quotient 0 b * b + remainder 0 b + b * (-quotient 0 b ) : by ring
      ...                       = b * (-quotient 0 b ) : by rw [quotient_mul_add_remainder_eq 0 b, zero_add],
  by_cases quotient_zero : (-quotient 0 b) = 0,
  { simp[quotient_zero] at h,
    exact h },
  { by_cases h'' : b = 0,
    { rw h'',
      simp },
    { have := not_le_of_lt (valuation_remainder_lt 0 b h''),
      rw h at this,
      have := le_valuation_mul b (-quotient 0 b) quotient_zero,
      contradiction }}
end

@[simp] lemma zero_div (b : α) (hnb : b ≠ 0) : 0 / b = 0 :=
begin
  have h1 : remainder 0 b = 0, from zero_mod b,
  have h2 := quotient_mul_add_remainder_eq 0 b,
  simp[h1] at h2,
  cases eq_zero_or_eq_zero_of_mul_eq_zero h2,
  { exact h },
  { contradiction }
end

@[simp] lemma mod_self (a : α) : a % a = 0 :=
let ⟨m, a_mul⟩ := dvd_mod_self a in
begin
  by_cases m = 0,
  { rw [h, mul_zero] at a_mul,
    exact a_mul },
  { by_cases a_zero : a = 0,
    { rw a_zero,
      simp },
    { have := le_valuation_mul a m h,
      rw ←a_mul at this,
      have := not_le_of_lt (valuation_remainder_lt a a a_zero),
      contradiction}}
end

lemma div_self (a : α) : a ≠ 0 → a / a = (1:α) :=
begin
  intro hna,
  have wit_aa := quotient_mul_add_remainder_eq a a,
  have a_mod_a := mod_self a,
  dsimp [(%)] at a_mod_a,
  simp [a_mod_a] at wit_aa,
  have h1 : 1 * a = a, from one_mul a,
  conv at wit_aa {for a [4] {rw ←h1}},
  exact eq_of_mul_eq_mul_right hna wit_aa
end

/- weak gcd lemmas -/

@[simp] theorem gcd_zero_left (a : α) : gcd 0 a = a :=
begin
  rw gcd,
  simp,
end

@[elab_as_eliminator]
theorem gcd.induction {P : α → α → Prop}
  (a b : α)
  (H0 : ∀ x, P 0 x)
  (H1 : ∀ a b, a ≠ 0 → P (b%a) a → P a b) :
  P a b :=
@well_founded.induction _ _ (has_well_founded.wf α) (λa, ∀b, P a b) a
  begin
    intros c IH,
    by_cases c = 0,
    { rw h,
      exact H0 },
    { intro b,
      exact H1 c b (h) (IH (b%c) (neq_zero_lt_mod_lt b c h) c) }
  end
  b

theorem gcd_dvd (a b : α) : (gcd a b ∣ a) ∧ (gcd a b ∣ b) :=
gcd.induction a b
  (λ b, by simp)
  begin
    intros a b aneq h_dvd,
    rw gcd,
    simp [aneq],
    induction h_dvd,
    split,
    { exact h_dvd_right },
    { conv {for b [2] {rw ←(quotient_mul_add_remainder_eq b a)}},
      have h_dvd_right_a:= dvd_mul_of_dvd_right h_dvd_right (b/a),
      exact dvd_add h_dvd_right_a h_dvd_left }
  end

theorem gcd_dvd_left (a b : α) : gcd a b ∣ a := (gcd_dvd a b).left

theorem gcd_dvd_right (a b : α) : gcd a b ∣ b := (gcd_dvd a b).right

theorem dvd_gcd {a b c : α} : c ∣ a → c ∣ b → c ∣ gcd a b :=
gcd.induction a b
  begin
    intros b dvd_0 dvd_b,
    simp,
    exact dvd_b
  end
  begin
    intros a b hna d dvd_a dvd_b,
    rw gcd,
    simp [hna],
    exact d (dvd_mod dvd_b dvd_a) dvd_a,
  end

/- strong gcd lemmas -/

@[simp] theorem gcd_zero_right (a : α) : gcd a 0 = a :=
begin
  unfold1 gcd,
  split_ifs; simp *
end

@[simp] theorem gcd_one_left (a : α) : gcd 1 a = 1 :=
begin
  rw [gcd],
  simp,
end

theorem gcd_next (a b : α) : gcd a b = gcd (b % a) a :=
begin
  by_cases (a=0),
  { simp [h] },
  { rw gcd,
    simp [h] }
end

@[simp] theorem gcd_self (a : α) : gcd a a = a :=
by rw [gcd_next a a, mod_self a, gcd_zero_left]

end euclidean_domain
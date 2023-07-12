/-
Copyright (c) 2021 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import algebra.algebra.basic
import set_theory.game.birthday
import set_theory.surreal.basic
import ring_theory.localization.basic

/-!
# Dyadic numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
Dyadic numbers are obtained by localizing ℤ away from 2. They are the initial object in the category
of rings with no 2-torsion.

## Dyadic surreal numbers
We construct dyadic surreal numbers using the canonical map from ℤ[2 ^ {-1}] to surreals.
As we currently do not have a ring structure on `surreal` we construct this map explicitly. Once we
have the ring structure, this map can be constructed directly by sending `2 ^ {-1}` to `half`.

## Embeddings
The above construction gives us an abelian group embedding of ℤ into `surreal`. The goal is to
extend this to an embedding of dyadic rationals into `surreal` and use Cauchy sequences of dyadic
rational numbers to construct an ordered field embedding of ℝ into `surreal`.
-/

universes u

local infix (name := pgame.equiv) ` ≈ ` := pgame.equiv

namespace pgame

/-- For a natural number `n`, the pre-game `pow_half (n + 1)` is recursively defined as
`{0 | pow_half n}`. These are the explicit expressions of powers of `1 / 2`. By definition, we have
`pow_half 0 = 1` and `pow_half 1 ≈ 1 / 2` and we prove later on that
`pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n`. -/
def pow_half : ℕ → pgame
| 0       := 1
| (n + 1) := ⟨punit, punit, 0, λ _, pow_half n⟩

@[simp] lemma pow_half_zero : pow_half 0 = 1 := rfl

lemma pow_half_left_moves (n) : (pow_half n).left_moves = punit := by cases n; refl
lemma pow_half_zero_right_moves : (pow_half 0).right_moves = pempty := rfl
lemma pow_half_succ_right_moves (n) : (pow_half (n + 1)).right_moves = punit := rfl

@[simp] lemma pow_half_move_left (n i) : (pow_half n).move_left i = 0 :=
by cases n; cases i; refl
@[simp] lemma pow_half_succ_move_right (n i) : (pow_half (n + 1)).move_right i = pow_half n :=
rfl

instance unique_pow_half_left_moves (n) : unique (pow_half n).left_moves :=
by cases n; exact punit.unique
instance is_empty_pow_half_zero_right_moves : is_empty (pow_half 0).right_moves :=
pempty.is_empty
instance unique_pow_half_succ_right_moves (n) : unique (pow_half (n + 1)).right_moves :=
punit.unique

@[simp] theorem birthday_half : birthday (pow_half 1) = 2 :=
by { rw birthday_def, dsimp, simpa using order.le_succ (1 : ordinal) }

/-- For all natural numbers `n`, the pre-games `pow_half n` are numeric. -/
theorem numeric_pow_half (n) : (pow_half n).numeric :=
begin
  induction n with n hn,
  { exact numeric_one },
  { split,
    { simpa using hn.move_left_lt default },
    { exact ⟨λ _, numeric_zero, λ _, hn⟩ } }
end

theorem pow_half_succ_lt_pow_half (n : ℕ) : pow_half (n + 1) < pow_half n :=
(numeric_pow_half (n + 1)).lt_move_right default

theorem pow_half_succ_le_pow_half (n : ℕ) : pow_half (n + 1) ≤ pow_half n :=
(pow_half_succ_lt_pow_half n).le

theorem pow_half_le_one (n : ℕ) : pow_half n ≤ 1 :=
begin
  induction n with n hn,
  { exact le_rfl },
  { exact (pow_half_succ_le_pow_half n).trans hn }
end

theorem pow_half_succ_lt_one (n : ℕ) : pow_half (n + 1) < 1 :=
(pow_half_succ_lt_pow_half n).trans_le $ pow_half_le_one n

theorem pow_half_pos (n : ℕ) : 0 < pow_half n :=
by { rw [←lf_iff_lt numeric_zero (numeric_pow_half n), zero_lf_le], simp }

theorem zero_le_pow_half (n : ℕ) : 0 ≤ pow_half n :=
(pow_half_pos n).le

theorem add_pow_half_succ_self_eq_pow_half (n) : pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n :=
begin
  induction n using nat.strong_induction_on with n hn,
  { split; rw le_iff_forall_lf; split,
    { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩); apply lf_of_lt,
      { calc 0 + pow_half n.succ ≈ pow_half n.succ : zero_add_equiv _
                             ... < pow_half n      : pow_half_succ_lt_pow_half n },
      { calc pow_half n.succ + 0 ≈ pow_half n.succ : add_zero_equiv _
                             ... < pow_half n      : pow_half_succ_lt_pow_half n } },
    { cases n, { rintro ⟨ ⟩ },
      rintro ⟨ ⟩,
      apply lf_of_move_right_le,
      swap, exact sum.inl default,
      calc  pow_half n.succ + pow_half (n.succ + 1)
          ≤ pow_half n.succ + pow_half n.succ : add_le_add_left (pow_half_succ_le_pow_half _) _
      ... ≈ pow_half n                        : hn _ (nat.lt_succ_self n) },
    { simp only [pow_half_move_left, forall_const],
      apply lf_of_lt,
      calc 0 ≈ 0 + 0                            : (add_zero_equiv 0).symm
        ... ≤ pow_half n.succ + 0               : add_le_add_right (zero_le_pow_half _) _
        ... < pow_half n.succ + pow_half n.succ : add_lt_add_left (pow_half_pos _) _ },
    { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩); apply lf_of_lt,
      { calc pow_half n
            ≈ pow_half n + 0               : (add_zero_equiv _).symm
        ... < pow_half n + pow_half n.succ : add_lt_add_left (pow_half_pos _) _ },
      { calc pow_half n
            ≈ 0 + pow_half n               : (zero_add_equiv _).symm
        ... < pow_half n.succ + pow_half n : add_lt_add_right (pow_half_pos _) _  } } }
end

theorem half_add_half_equiv_one : pow_half 1 + pow_half 1 ≈ 1 :=
add_pow_half_succ_self_eq_pow_half 0

end pgame

namespace surreal
open pgame

/-- Powers of the surreal number `half`. -/
def pow_half (n : ℕ) : surreal := ⟦⟨pgame.pow_half n, pgame.numeric_pow_half n⟩⟧

@[simp] lemma pow_half_zero : pow_half 0 = 1 := rfl

@[simp] lemma double_pow_half_succ_eq_pow_half (n : ℕ) : 2 • pow_half n.succ = pow_half n :=
by { rw two_nsmul, exact quotient.sound (pgame.add_pow_half_succ_self_eq_pow_half n) }

@[simp] lemma nsmul_pow_two_pow_half (n : ℕ) : 2 ^ n • pow_half n = 1 :=
begin
  induction n with n hn,
  { simp only [nsmul_one, pow_half_zero, nat.cast_one, pow_zero] },
  { rw [← hn, ← double_pow_half_succ_eq_pow_half n, smul_smul (2^n) 2 (pow_half n.succ),
        mul_comm, pow_succ] }
end

@[simp] lemma nsmul_pow_two_pow_half' (n k : ℕ) : 2 ^ n • pow_half (n + k) = pow_half k :=
begin
  induction k with k hk,
  { simp only [add_zero, surreal.nsmul_pow_two_pow_half, nat.nat_zero_eq_zero, eq_self_iff_true,
               surreal.pow_half_zero] },
  { rw [← double_pow_half_succ_eq_pow_half (n + k), ← double_pow_half_succ_eq_pow_half k,
        smul_algebra_smul_comm] at hk,
    rwa ← zsmul_eq_zsmul_iff' two_ne_zero }
end

lemma zsmul_pow_two_pow_half (m : ℤ) (n k : ℕ) :
  (m * 2 ^ n) • pow_half (n + k) = m • pow_half k :=
begin
  rw mul_zsmul,
  congr,
  norm_cast,
  exact nsmul_pow_two_pow_half' n k
end

lemma dyadic_aux {m₁ m₂ : ℤ} {y₁ y₂ : ℕ} (h₂ : m₁ * (2 ^ y₁) = m₂ * (2 ^ y₂)) :
  m₁ • pow_half y₂ = m₂ • pow_half y₁ :=
begin
  revert m₁ m₂,
  wlog h : y₁ ≤ y₂,
  { intros m₁ m₂ aux, exact (this (le_of_not_le h) aux.symm).symm },
  intros m₁ m₂ h₂,
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h,
  rw [add_comm, pow_add, ← mul_assoc, mul_eq_mul_right_iff] at h₂,
  cases h₂,
  { rw [h₂, add_comm, zsmul_pow_two_pow_half m₂ c y₁] },
  { have := nat.one_le_pow y₁ 2 nat.succ_pos',
    norm_cast at h₂, linarith },
end

/-- The additive monoid morphism `dyadic_map` sends ⟦⟨m, 2^n⟩⟧ to m • half ^ n. -/
def dyadic_map : localization.away (2 : ℤ) →+ surreal :=
{ to_fun :=
  λ x, localization.lift_on x (λ x y, x • pow_half (submonoid.log y)) $
  begin
    intros m₁ m₂ n₁ n₂ h₁,
    obtain ⟨⟨n₃, y₃, hn₃⟩, h₂⟩ := localization.r_iff_exists.mp h₁,
    simp only [subtype.coe_mk, mul_eq_mul_left_iff] at h₂,
    cases h₂,
    { simp only,
      obtain ⟨a₁, ha₁⟩ := n₁.prop,
      obtain ⟨a₂, ha₂⟩ := n₂.prop,
      have hn₁ : n₁ = submonoid.pow 2 a₁ := subtype.ext ha₁.symm,
      have hn₂ : n₂ = submonoid.pow 2 a₂ := subtype.ext ha₂.symm,
      have h₂ : 1 < (2 : ℤ).nat_abs, from one_lt_two,
      rw [hn₁, hn₂, submonoid.log_pow_int_eq_self h₂, submonoid.log_pow_int_eq_self h₂],
      apply dyadic_aux,
      rwa [ha₁, ha₂, mul_comm, mul_comm m₂] },
    { have : (1 : ℤ) ≤ 2 ^ y₃ := by exact_mod_cast nat.one_le_pow y₃ 2 nat.succ_pos',
      linarith }
    end,
  map_zero' := localization.lift_on_zero _ _,
  map_add' := λ x y, localization.induction_on₂ x y $
  begin
    rintro ⟨a, ⟨b, ⟨b', rfl⟩⟩⟩ ⟨c, ⟨d, ⟨d', rfl⟩⟩⟩,
    have h₂ : 1 < (2 : ℤ).nat_abs, from one_lt_two,
    have hpow₂ := submonoid.log_pow_int_eq_self h₂,
    simp_rw submonoid.pow_apply at hpow₂,
    simp_rw [localization.add_mk, localization.lift_on_mk, subtype.coe_mk,
      submonoid.log_mul (int.pow_right_injective h₂), hpow₂],
    calc (2 ^ b' * c + 2 ^ d' * a) • pow_half (b' + d')
        = (c * 2 ^ b') • pow_half (b' + d') + (a * 2 ^ d') • pow_half (d' + b')
        : by simp only [add_smul, mul_comm,add_comm]
    ... = c • pow_half d' + a • pow_half b' : by simp only [zsmul_pow_two_pow_half]
    ... = a • pow_half b' + c • pow_half d' : add_comm _ _,
  end }

@[simp] lemma dyadic_map_apply (m : ℤ) (p : submonoid.powers (2 : ℤ)) :
  dyadic_map (is_localization.mk' (localization (submonoid.powers 2)) m p) =
  m • pow_half (submonoid.log p) :=
by { rw ← localization.mk_eq_mk', refl }

@[simp] lemma dyadic_map_apply_pow (m : ℤ) (n : ℕ) :
  dyadic_map (is_localization.mk' (localization (submonoid.powers 2)) m (submonoid.pow 2 n)) =
  m • pow_half n :=
by rw [dyadic_map_apply, @submonoid.log_pow_int_eq_self 2 one_lt_two]

/-- We define dyadic surreals as the range of the map `dyadic_map`. -/
def dyadic : set surreal := set.range dyadic_map

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO show that the map from dyadic rationals to surreals is injective

-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective

-- TODO show the maps from the dyadic rationals and from the reals
-- into the surreals are multiplicative

end surreal

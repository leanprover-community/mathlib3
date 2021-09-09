/-
Copyright (c) 2021 Apurva Nakade. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Apurva Nakade
-/
import set_theory.surreal.basic
import ring_theory.localization

/-!
# Dyadic numbers
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

local infix ` ≈ ` := pgame.equiv

namespace pgame

/-- For a natural number `n`, the pre-game `pow_half (n + 1)` is recursively defined as
`{ 0 | pow_half n }`. These are the explicit expressions of powers of `half`. By definition, we have
 `pow_half 0 = 0` and `pow_half 1 = half` and we prove later on that
`pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n`.-/
def pow_half : ℕ → pgame
| 0       := mk punit pempty 0 pempty.elim
| (n + 1) := mk punit punit 0 (λ _, pow_half n)

@[simp] lemma pow_half_left_moves {n} : (pow_half n).left_moves = punit :=
by cases n; refl

@[simp] lemma pow_half_right_moves {n} : (pow_half (n + 1)).right_moves = punit :=
by cases n; refl

@[simp] lemma pow_half_move_left {n i} : (pow_half n).move_left i = 0 :=
by cases n; cases i; refl

@[simp] lemma pow_half_move_right {n i} : (pow_half (n + 1)).move_right i = pow_half n :=
by cases n; cases i; refl

lemma pow_half_move_left' (n) :
  (pow_half n).move_left (equiv.cast (pow_half_left_moves.symm) punit.star) = 0 :=
by simp only [eq_self_iff_true, pow_half_move_left]

lemma pow_half_move_right' (n) :
  (pow_half (n + 1)).move_right (equiv.cast (pow_half_right_moves.symm) punit.star) = pow_half n :=
by simp only [pow_half_move_right, eq_self_iff_true]

/-- For all natural numbers `n`, the pre-games `pow_half n` are numeric. -/
theorem numeric_pow_half {n} : (pow_half n).numeric :=
begin
  induction n with n hn,
  { exact numeric_one },
  { split,
    { rintro ⟨ ⟩ ⟨ ⟩,
      dsimp only [pi.zero_apply],
      rw ← pow_half_move_left' n,
      apply hn.move_left_lt },
    { exact ⟨λ _, numeric_zero, λ _, hn⟩ } }
end

theorem pow_half_succ_lt_pow_half {n : ℕ} : pow_half (n + 1) < pow_half n :=
(@numeric_pow_half (n + 1)).lt_move_right punit.star

theorem pow_half_succ_le_pow_half {n : ℕ} : pow_half (n + 1) ≤ pow_half n :=
le_of_lt numeric_pow_half numeric_pow_half pow_half_succ_lt_pow_half

theorem zero_lt_pow_half {n : ℕ} : 0 < pow_half n :=
by cases n; rw lt_def_le; use ⟨punit.star, pgame.le_refl 0⟩

theorem zero_le_pow_half {n : ℕ} : 0 ≤ pow_half n :=
le_of_lt numeric_zero numeric_pow_half zero_lt_pow_half

theorem add_pow_half_succ_self_eq_pow_half {n} : pow_half (n + 1) + pow_half (n + 1) ≈ pow_half n :=
begin
  induction n with n hn,
  { exact half_add_half_equiv_one },
  { split; rw le_def_lt; split,
    { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩),
      { calc 0 + pow_half (n.succ + 1) ≈ pow_half (n.succ + 1) : zero_add_equiv _
                                   ... < pow_half n.succ       : pow_half_succ_lt_pow_half },
      { calc pow_half (n.succ + 1) + 0 ≈ pow_half (n.succ + 1) : add_zero_equiv _
                                   ... < pow_half n.succ       : pow_half_succ_lt_pow_half } },
    { rintro ⟨ ⟩,
      rw lt_def_le,
      right,
      use sum.inl punit.star,
      calc pow_half (n.succ) + pow_half (n.succ + 1)
          ≤ pow_half (n.succ) + pow_half (n.succ) : add_le_add_left pow_half_succ_le_pow_half
      ... ≈ pow_half n                            : hn },
    { rintro ⟨ ⟩,
      calc 0 ≈ 0 + 0                                        : (add_zero_equiv _).symm
        ... ≤ pow_half (n.succ + 1) + 0                     : add_le_add_right zero_le_pow_half
        ... < pow_half (n.succ + 1) + pow_half (n.succ + 1) : add_lt_add_left zero_lt_pow_half },
    { rintro (⟨⟨ ⟩⟩ | ⟨⟨ ⟩⟩),
      { calc pow_half n.succ
            ≈ pow_half n.succ + 0                           : (add_zero_equiv _).symm
        ... < pow_half (n.succ) + pow_half (n.succ + 1)     : add_lt_add_left zero_lt_pow_half },
      { calc pow_half n.succ
            ≈ 0 + pow_half n.succ                           : (zero_add_equiv _).symm
        ... < pow_half (n.succ + 1) + pow_half (n.succ)     : add_lt_add_right zero_lt_pow_half }}}
end

end pgame

namespace surreal
open pgame

/-- The surreal number `half`. -/
def half : surreal := ⟦⟨pgame.half, pgame.numeric_half⟩⟧

/-- Powers of the surreal number `half`. -/
def pow_half (n : ℕ) : surreal := ⟦⟨pgame.pow_half n, pgame.numeric_pow_half⟩⟧

@[simp] lemma pow_half_zero : pow_half 0 = 1 := rfl

@[simp] lemma pow_half_one : pow_half 1 = half := rfl

@[simp] theorem add_half_self_eq_one : half + half = 1 :=
quotient.sound pgame.half_add_half_equiv_one

lemma double_pow_half_succ_eq_pow_half (n : ℕ) : 2 • pow_half n.succ = pow_half n :=
begin
  rw two_nsmul,
  apply quotient.sound,
  exact pgame.add_pow_half_succ_self_eq_pow_half,
end

lemma nsmul_pow_two_pow_half (n : ℕ) : 2 ^ n • pow_half n = 1 :=
begin
  induction n with n hn,
  { simp only [nsmul_one, pow_half_zero, nat.cast_one, pow_zero] },
  { rw [← hn, ← double_pow_half_succ_eq_pow_half n, smul_smul (2^n) 2 (pow_half n.succ),
        mul_comm, pow_succ] }
end

lemma nsmul_pow_two_pow_half' (n k : ℕ) : 2 ^ n • pow_half (n + k) = pow_half k :=
begin
  induction k with k hk,
  { simp only [add_zero, surreal.nsmul_pow_two_pow_half, nat.nat_zero_eq_zero, eq_self_iff_true,
               surreal.pow_half_zero] },
  { rw [← double_pow_half_succ_eq_pow_half (n + k), ← double_pow_half_succ_eq_pow_half k,
        smul_algebra_smul_comm] at hk,
    rwa ← (gsmul_eq_gsmul_iff' two_ne_zero) }
end

lemma nsmul_int_pow_two_pow_half (m : ℤ) (n k : ℕ) :
  (m * 2 ^ n) • pow_half (n + k) = m • pow_half k :=
begin
  rw mul_gsmul,
  congr,
  norm_cast,
  exact nsmul_pow_two_pow_half' n k,
end

lemma dyadic_aux {m₁ m₂ : ℤ} {y₁ y₂ : ℕ} (h₂ : m₁ * (2 ^ y₁) = m₂ * (2 ^ y₂)) :
  m₁ • pow_half y₂ = m₂ • pow_half y₁ :=
begin
  revert m₁ m₂,
  wlog h : y₁ ≤ y₂,
  intros m₁ m₂ h₂,
  obtain ⟨c, rfl⟩ := le_iff_exists_add.mp h,
  rw [add_comm, pow_add, ← mul_assoc, mul_eq_mul_right_iff] at h₂,
  cases h₂,
  { rw [h₂, add_comm, nsmul_int_pow_two_pow_half m₂ c y₁] },
  { have := nat.one_le_pow y₁ 2 nat.succ_pos',
    linarith },
end

/-- The map `dyadic_map` sends ⟦⟨m, 2^n⟩⟧ to m • half ^ n. -/
def dyadic_map (x : localization (submonoid.powers (2 : ℤ))) : surreal :=
quotient.lift_on' x (λ x : _ × _, x.1 • pow_half (submonoid.log x.2)) $
begin
  rintros ⟨m₁, n₁⟩ ⟨m₂, n₂⟩ h₁,
  obtain ⟨⟨n₃, y₃, hn₃⟩, h₂⟩ := localization.r_iff_exists.mp h₁,
  simp only [subtype.coe_mk, mul_eq_mul_right_iff] at h₂,
  cases h₂,
  { simp only,
    obtain ⟨a₁, ha₁⟩ := n₁.prop,
    obtain ⟨a₂, ha₂⟩ := n₂.prop,
    have hn₁ : n₁ = submonoid.pow 2 a₁ := subtype.ext ha₁.symm,
    have hn₂ : n₂ = submonoid.pow 2 a₂ := subtype.ext ha₂.symm,
    have h₂ : 1 < (2 : ℤ).nat_abs, from dec_trivial,
    rw [hn₁, hn₂, submonoid.log_pow_int_eq_self h₂, submonoid.log_pow_int_eq_self h₂],
    apply dyadic_aux,
    rwa [ha₁, ha₂] },
  { have := nat.one_le_pow y₃ 2 nat.succ_pos',
    linarith }
end

/-- We define dyadic surreals as the range of the map `dyadic_map`. -/
def dyadic : set surreal := set.range dyadic_map

-- We conclude with some ideas for further work on surreals; these would make fun projects.

-- TODO show that the map from dyadic rationals to surreals is a group homomorphism, and injective

-- TODO map the reals into the surreals, using dyadic Dedekind cuts
-- TODO show this is a group homomorphism, and injective

-- TODO show the maps from the dyadic rationals and from the reals
-- into the surreals are multiplicative

end surreal

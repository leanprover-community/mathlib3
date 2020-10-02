/-
Copyright (c) 2018 Guy Leroy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sangwoo Jo (aka Jason), Guy Leroy, Johannes Hölzl, Mario Carneiro
-/
import data.nat.prime

/-!
# Extended GCD and divisibility over ℤ

## Main definitions

* Given `x y : ℕ`, `xgcd x y` computes the pair of integers `(a, b)` such that
  `gcd x y = x * a + y * b`. `gcd_a x y` and `gcd_b x y` are defined to be `a` and `b`,
  respectively.

## Main statements

* `gcd_eq_gcd_ab`: Bézout's lemma, given `x y : ℕ`, `gcd x y = x * gcd_a x y + y * gcd_b x y`.

-/

/-! ### Extended Euclidean algorithm -/
namespace nat

/-- Helper function for the extended GCD algorithm (`nat.xgcd`). -/
def xgcd_aux : ℕ → ℤ → ℤ → ℕ → ℤ → ℤ → ℕ × ℤ × ℤ
| 0          s t r' s' t' := (r', s', t')
| r@(succ _) s t r' s' t' :=
  have r' % r < r, from mod_lt _ $ succ_pos _,
  let q := r' / r in xgcd_aux (r' % r) (s' - q * s) (t' - q * t) r s t

@[simp] theorem xgcd_zero_left {s t r' s' t'} : xgcd_aux 0 s t r' s' t' = (r', s', t') :=
by simp [xgcd_aux]

theorem xgcd_aux_rec {r s t r' s' t'} (h : 0 < r) :
  xgcd_aux r s t r' s' t' = xgcd_aux (r' % r) (s' - (r' / r) * s) (t' - (r' / r) * t) r s t :=
by cases r; [exact absurd h (lt_irrefl _), {simp only [xgcd_aux], refl}]

/-- Use the extended GCD algorithm to generate the `a` and `b` values
  satisfying `gcd x y = x * a + y * b`. -/
def xgcd (x y : ℕ) : ℤ × ℤ := (xgcd_aux x 1 0 y 0 1).2

/-- The extended GCD `a` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_a (x y : ℕ) : ℤ := (xgcd x y).1

/-- The extended GCD `b` value in the equation `gcd x y = x * a + y * b`. -/
def gcd_b (x y : ℕ) : ℤ := (xgcd x y).2

@[simp] theorem xgcd_aux_fst (x y) : ∀ s t s' t',
  (xgcd_aux x s t y s' t').1 = gcd x y :=
gcd.induction x y (by simp) (λ x y h IH s t s' t', by simp [xgcd_aux_rec, h, IH]; rw ← gcd_rec)

theorem xgcd_aux_val (x y) : xgcd_aux x 1 0 y 0 1 = (gcd x y, xgcd x y) :=
by rw [xgcd, ← xgcd_aux_fst x y 1 0 0 1]; cases xgcd_aux x 1 0 y 0 1; refl

theorem xgcd_val (x y) : xgcd x y = (gcd_a x y, gcd_b x y) :=
by unfold gcd_a gcd_b; cases xgcd x y; refl

section
parameters (x y : ℕ)

private def P : ℕ × ℤ × ℤ → Prop
| (r, s, t) := (r : ℤ) = x * s + y * t

theorem xgcd_aux_P {r r'} : ∀ {s t s' t'}, P (r, s, t) → P (r', s', t') →
  P (xgcd_aux r s t r' s' t') :=
gcd.induction r r' (by simp) $ λ a b h IH s t s' t' p p', begin
  rw [xgcd_aux_rec h], refine IH _ p, dsimp [P] at *,
  rw [int.mod_def], generalize : (b / a : ℤ) = k,
  rw [p, p'],
  simp [mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, sub_eq_neg_add, mul_assoc]
end

/-- Bézout's lemma: given `x y : ℕ`, `gcd x y = x * a + y * b`, where `a = gcd_a x y` and
`b = gcd_b x y` are computed by the extended Euclidean algorithm.
-/
theorem gcd_eq_gcd_ab : (gcd x y : ℤ) = x * gcd_a x y + y * gcd_b x y :=
by have := @xgcd_aux_P x y x y 1 0 0 1 (by simp [P]) (by simp [P]);
   rwa [xgcd_aux_val, xgcd_val] at this
end

end nat

lemma pow_gcd_eq_one {M : Type*} [monoid M] (x : M) {m n : ℕ} (hm : x ^ m = 1) (hn : x ^ n = 1) :
  x ^ m.gcd n = 1 :=
begin
  cases m, { simp only [hn, nat.gcd_zero_left] },
  obtain ⟨x, rfl⟩ : is_unit x,
  { apply is_unit_of_pow_eq_one _ _ hm m.succ_pos },
  simp only [← units.coe_pow] at *,
  rw [← units.coe_one, ← gpow_coe_nat, ← units.ext_iff] at *,
  simp only [nat.gcd_eq_gcd_ab, gpow_add, gpow_mul, hm, hn, one_gpow, one_mul]
end

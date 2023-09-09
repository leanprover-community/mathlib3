/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import data.nat.sqrt
import data.set.lattice
import algebra.group.prod
import algebra.order.monoid.min_max

/-!
#  Naturals pairing function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a pairing function for the naturals as follows:
```text
 0  1  4  9 16
 2  3  5 10 17
 6  7  8 11 18
12 13 14 15 19
20 21 22 23 24
```

It has the advantage of being monotone in both directions and sending `⟦0, n^2 - 1⟧` to
`⟦0, n - 1⟧²`.
-/

open prod decidable function

namespace nat

/-- Pairing function for the natural numbers. -/
@[pp_nodot] def mkpair (a b : ℕ) : ℕ :=
if a < b then b*b + a else a*a + a + b

/-- Unpairing function for the natural numbers. -/
@[pp_nodot] def unpair (n : ℕ) : ℕ × ℕ :=
let s := sqrt n in
if n - s*s < s then (n - s*s, s) else (s, n - s*s - s)

@[simp] theorem mkpair_unpair (n : ℕ) : mkpair (unpair n).1 (unpair n).2 = n :=
begin
  dsimp only [unpair], set s := sqrt n,
  have sm : s * s + (n - s * s) = n := add_tsub_cancel_of_le (sqrt_le _),
  split_ifs,
  { simp [mkpair, h, sm] },
  { have hl : n - s*s - s ≤ s :=
      tsub_le_iff_left.mpr (tsub_le_iff_left.mpr $
      by rw ← add_assoc; apply sqrt_le_add),
    simp [mkpair, hl.not_lt, add_assoc, add_tsub_cancel_of_le (le_of_not_gt h), sm] }
end

theorem mkpair_unpair' {n a b} (H : unpair n = (a, b)) : mkpair a b = n :=
by simpa [H] using mkpair_unpair n

@[simp] theorem unpair_mkpair (a b : ℕ) : unpair (mkpair a b) = (a, b) :=
begin
  dunfold mkpair, split_ifs,
  { show unpair (b * b + a) = (a, b),
    have be : sqrt (b * b + a) = b,
      from sqrt_add_eq _ (le_trans (le_of_lt h) (nat.le_add_left _ _)),
    simp [unpair, be, add_tsub_cancel_right, h] },
  { show unpair (a * a + a + b) = (a, b),
    have ae : sqrt (a * a + (a + b)) = a,
    { rw sqrt_add_eq, exact add_le_add_left (le_of_not_gt h) _ },
    simp [unpair, ae, nat.not_lt_zero, add_assoc] }
end

/-- An equivalence between `ℕ × ℕ` and `ℕ`. -/
@[simps { fully_applied := ff }] def mkpair_equiv : ℕ × ℕ ≃ ℕ :=
⟨uncurry mkpair, unpair, λ ⟨a, b⟩, unpair_mkpair a b, mkpair_unpair⟩

lemma surjective_unpair : surjective unpair :=
mkpair_equiv.symm.surjective

@[simp] lemma mkpair_eq_mkpair {a b c d : ℕ} : mkpair a b = mkpair c d ↔ a = c ∧ b = d :=
mkpair_equiv.injective.eq_iff.trans (@prod.ext_iff ℕ ℕ (a, b) (c, d))

theorem unpair_lt {n : ℕ} (n1 : 1 ≤ n) : (unpair n).1 < n :=
let s := sqrt n in begin
  simp [unpair], change sqrt n with s,
  by_cases h : n - s * s < s; simp [h],
  { exact lt_of_lt_of_le h (sqrt_le_self _) },
  { simp at h,
    have s0 : 0 < s := sqrt_pos.2 n1,
    exact lt_of_le_of_lt h (tsub_lt_self n1 (mul_pos s0 s0)) }
end

@[simp] lemma unpair_zero : unpair 0 = 0 :=
by { rw unpair, simp }

theorem unpair_left_le : ∀ (n : ℕ), (unpair n).1 ≤ n
| 0     := by simp
| (n+1) := le_of_lt (unpair_lt (nat.succ_pos _))

theorem left_le_mkpair (a b : ℕ) : a ≤ mkpair a b :=
by simpa using unpair_left_le (mkpair a b)

theorem right_le_mkpair (a b : ℕ) : b ≤ mkpair a b :=
begin
  by_cases h : a < b; simp [mkpair, h],
  exact le_trans (le_mul_self _) (nat.le_add_right _ _)
end

theorem unpair_right_le (n : ℕ) : (unpair n).2 ≤ n :=
by simpa using right_le_mkpair n.unpair.1 n.unpair.2

theorem mkpair_lt_mkpair_left {a₁ a₂} (b) (h : a₁ < a₂) : mkpair a₁ b < mkpair a₂ b :=
begin
  by_cases h₁ : a₁ < b; simp [mkpair, h₁, add_assoc],
  { by_cases h₂ : a₂ < b; simp [mkpair, h₂, h],
    simp at h₂,
    apply add_lt_add_of_le_of_lt,
    exact mul_self_le_mul_self h₂,
    exact lt_add_right _ _ _ h },
  { simp at h₁,
    simp [not_lt_of_gt (lt_of_le_of_lt h₁ h)],
    apply add_lt_add,
    exact mul_self_lt_mul_self h,
    apply add_lt_add_right; assumption }
end

theorem mkpair_lt_mkpair_right (a) {b₁ b₂} (h : b₁ < b₂) : mkpair a b₁ < mkpair a b₂ :=
begin
  by_cases h₁ : a < b₁; simp [mkpair, h₁, add_assoc],
  { simp [mkpair, lt_trans h₁ h, h],
    exact mul_self_lt_mul_self h },
  { by_cases h₂ : a < b₂; simp [mkpair, h₂, h],
    simp at h₁,
    rw [add_comm, add_comm _ a, add_assoc, add_lt_add_iff_left],
    rwa [add_comm, ← sqrt_lt, sqrt_add_eq],
    exact le_trans h₁ (nat.le_add_left _ _) }
end

theorem mkpair_lt_max_add_one_sq (m n : ℕ) : mkpair m n < (max m n + 1) ^ 2 :=
begin
  rw [mkpair, add_sq, mul_one, two_mul, sq, add_assoc, add_assoc],
  cases lt_or_le m n,
  { rw [if_pos h, max_eq_right h.le, add_lt_add_iff_left, add_assoc],
    exact h.trans_le (self_le_add_right n _) },
  { rw [if_neg h.not_lt, max_eq_left h, add_lt_add_iff_left, add_assoc, add_lt_add_iff_left],
    exact lt_succ_of_le h }
end

theorem max_sq_add_min_le_mkpair (m n : ℕ) : max m n ^ 2 + min m n ≤ mkpair m n :=
begin
  rw mkpair,
  cases lt_or_le m n,
  { rw [if_pos h, max_eq_right h.le, min_eq_left h.le, sq], },
  { rw [if_neg h.not_lt, max_eq_left h, min_eq_right h, sq, add_assoc, add_le_add_iff_left],
    exact le_add_self }
end

theorem add_le_mkpair (m n : ℕ) : m + n ≤ mkpair m n :=
(max_sq_add_min_le_mkpair _ _).trans' $
  by { rw [sq, ←min_add_max, add_comm, add_le_add_iff_right], exact le_mul_self _ }

theorem unpair_add_le (n : ℕ) : (unpair n).1 + (unpair n).2 ≤ n :=
(add_le_mkpair _ _).trans_eq (mkpair_unpair _)

end nat
open nat

section complete_lattice

lemma supr_unpair {α} [complete_lattice α] (f : ℕ → ℕ → α) :
  (⨆ n : ℕ, f n.unpair.1 n.unpair.2) = ⨆ i j : ℕ, f i j :=
by rw [← (supr_prod : (⨆ i : ℕ × ℕ, f i.1 i.2) = _), ← nat.surjective_unpair.supr_comp]

lemma infi_unpair {α} [complete_lattice α] (f : ℕ → ℕ → α) :
  (⨅ n : ℕ, f n.unpair.1 n.unpair.2) = ⨅ i j : ℕ, f i j :=
supr_unpair (show ℕ → ℕ → αᵒᵈ, from f)

end complete_lattice

namespace set

lemma Union_unpair_prod {α β} {s : ℕ → set α} {t : ℕ → set β} :
  (⋃ n : ℕ, s n.unpair.fst ×ˢ t n.unpair.snd) = (⋃ n, s n) ×ˢ (⋃ n, t n) :=
by { rw [← Union_prod], convert surjective_unpair.Union_comp _, refl }

lemma Union_unpair {α} (f : ℕ → ℕ → set α) :
  (⋃ n : ℕ, f n.unpair.1 n.unpair.2) = ⋃ i j : ℕ, f i j :=
supr_unpair f

lemma Inter_unpair {α} (f : ℕ → ℕ → set α) :
  (⋂ n : ℕ, f n.unpair.1 n.unpair.2) = ⋂ i j : ℕ, f i j :=
infi_unpair f

end set

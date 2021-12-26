/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.algebra.basic

/-!
# `ne_zero` typeclass

We create a typeclass `ne_zero n` which carries around the fact that `(n : R) ≠ 0`.

## Main declarations

* `ne_zero`: `n ≠ 0` as a typeclass.

-/

/-- A type-class version of `n ≠ 0`.  -/
class ne_zero {R} [has_zero R] (n : R) : Prop := (out : n ≠ 0)

lemma ne_zero.ne {R} [has_zero R] (n : R) [h : ne_zero n] : n ≠ 0 := h.out

lemma ne_zero.ne' (n : ℕ) (R) [has_zero R] [has_one R] [has_add R] [h : ne_zero (n : R)] :
  (n : R) ≠ 0 := h.out

namespace ne_zero

variables {K R S M : Type*} {n : ℕ} {a : ℕ+}

instance pnat : ne_zero (a : ℕ) := ⟨a.ne_zero⟩
instance succ : ne_zero (n + 1) := ⟨n.succ_ne_zero⟩

instance char_zero [ne_zero n] [add_monoid M] [has_one M] [char_zero M] : ne_zero (n : M) :=
⟨nat.cast_ne_zero.mpr $ ne_zero.ne n⟩

lemma of_no_zero_smul_divisors [comm_ring R] [ne_zero (n : R)] (S) [ring S] [nontrivial S]
  [algebra R S] [no_zero_smul_divisors R S] : ne_zero (n : S) :=
⟨λ h, (ne_zero.ne' n R) $ no_zero_smul_divisors.algebra_map_injective R S $ by simpa⟩

lemma nat_of_ne [has_zero R] [has_one R] [has_add R] [h : ne_zero (n : R)] : ne_zero n :=
⟨by {casesI h, rintro rfl, contradiction}⟩

end ne_zero

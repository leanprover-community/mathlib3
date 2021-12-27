/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.algebra.basic
import algebra.char_p.basic

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

variables {R M : Type*} {x y : M} {n p : ℕ} {a : ℕ+}

instance pnat : ne_zero (a : ℕ) := ⟨a.ne_zero⟩
instance succ : ne_zero (n + 1) := ⟨n.succ_ne_zero⟩

lemma of_pos [preorder M] [has_zero M] (h : 0 < x) : ne_zero x := ⟨h.ne'⟩
lemma of_gt  [canonically_ordered_add_monoid M] (h : x < y) : ne_zero y := of_pos $ pos_of_gt h

instance char_zero [ne_zero n] [add_monoid M] [has_one M] [char_zero M] : ne_zero (n : M) :=
⟨nat.cast_ne_zero.mpr $ ne_zero.ne n⟩

variables (R M)

lemma of_not_dvd [add_monoid M] [has_one M] [char_p M p] (h : ¬ p ∣ n) : ne_zero (n : M) :=
⟨(not_iff_not.mpr $ char_p.cast_eq_zero_iff M p n).mpr h⟩

lemma of_injective [semiring R] [ne_zero (n : R)] [semiring M] [nontrivial M] {f : R →+* M}
  (hf : function.injective f) : ne_zero (n : M) :=
⟨λ h, (ne_zero.ne' n R) $ hf $ by simpa⟩

lemma of_no_zero_smul_divisors [comm_ring R] [ne_zero (n : R)] [ring M] [nontrivial M]
  [algebra R M] [no_zero_smul_divisors R M] : ne_zero (n : M) :=
of_injective _ _ $ no_zero_smul_divisors.algebra_map_injective R M

lemma nat_of_ne [has_zero R] [has_one R] [has_add R] [h : ne_zero (n : R)] : ne_zero n :=
⟨by {casesI h, rintro rfl, contradiction}⟩

end ne_zero

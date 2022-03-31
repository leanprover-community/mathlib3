/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import algebra.char_p.basic

/-! # `char_p R 0` and `char_zero R` need not coincide for semirings

This file shows that there are semiring `R` for which `char_p R 0` holds and `char_zero R` does not.

The example is `F2 = {0, 1}` with saturating addition.  We actually make `F2` into a semiring,
but multiplication plays no role.
--/

/--  `F2` is a `comm_semiring` satisfying `char_p F2 0` and `¬ char_zero F2`. -/
@[derive [decidable_eq]]
inductive F2
| zero
| one

namespace F2

instance : has_zero F2 := ⟨zero⟩
instance : has_one F2 := ⟨one⟩

instance inhabited : inhabited F2 := ⟨zero⟩

/-- A tactic to prove facts by cases. -/
meta def boom : tactic unit :=
`[repeat {rintro ⟨⟩}; dec_trivial]

/--  The addition on `{0, 1}`: the only sum that is not equal to `1` is `0 + 0`. -/
def add : F2 → F2 → F2
| 0 0 := 0
| _ _ := 1

/--  The multiplication on `{0, 1}`: the only product that is not equal to `0` is `1 * 1`. -/
def mul : F2 → F2 → F2
| 1 1 := 1
| _ _ := 0

instance : comm_semiring F2 :=
{ add := add,
  add_assoc := by boom,
  zero := 0,
  zero_add := by boom,
  add_zero := by boom,
  add_comm := by boom,
  mul := mul,
  left_distrib := by boom,
  right_distrib := by boom,
  zero_mul := by boom,
  mul_zero := by boom,
  mul_assoc := by boom,
  one := 1,
  one_mul := by boom,
  mul_one := by boom,
  mul_comm := by boom }

@[simp] lemma add_one_eq_one : ∀ (x : F2), x + 1 = 1
| 0 := rfl
| 1 := rfl

lemma char_p_F2_zero : char_p F2 0 :=
begin
  refine⟨λ x, _⟩,
  cases x,
  { simp },
  { simp only [nat.cast_succ, add_one_eq_one, zero_dvd_iff, nat.succ_ne_zero, iff_false],
    exact λ h, F2.no_confusion h }
end

lemma not_char_zero : ¬ char_zero F2 :=
begin
  rintro ⟨h⟩,
  have diff : (coe : ℕ → F2) (1 + 1) ≠ (coe : ℕ → F2) (0 + 1), { exact λ h1, by simpa using h h1 },
  exact diff (by simp)
end

end F2

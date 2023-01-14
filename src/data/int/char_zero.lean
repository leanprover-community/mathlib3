/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.int.cast.field

/-!
# Injectivity of `int.cast` into characteristic zero rings and fields.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

variables {α : Type*}

open nat

namespace int

@[simp]
theorem cast_eq_zero [add_group_with_one α] [char_zero α] {n : ℤ} : (n : α) = 0 ↔ n = 0 :=
⟨λ h, begin cases n,
  { rw [int.cast_of_nat] at h, exact congr_arg coe (nat.cast_eq_zero.1 h) },
  { rw [cast_neg_succ_of_nat, neg_eq_zero, nat.cast_eq_zero] at h,
    contradiction }
end, λ h, by rw [h, cast_zero]⟩

@[simp, norm_cast] theorem cast_inj [add_group_with_one α] [char_zero α] {m n : ℤ} :
  (m : α) = n ↔ m = n :=
by rw [← sub_eq_zero, ← cast_sub, cast_eq_zero, sub_eq_zero]

theorem cast_injective [add_group_with_one α] [char_zero α] : function.injective (coe : ℤ → α)
| m n := cast_inj.1

theorem cast_ne_zero [add_group_with_one α] [char_zero α] {n : ℤ} : (n : α) ≠ 0 ↔ n ≠ 0 :=
not_congr cast_eq_zero

@[simp, norm_cast]
theorem cast_div_char_zero {k : Type*} [field k] [char_zero k] {m n : ℤ}
  (n_dvd : n ∣ m) : ((m / n : ℤ) : k) = m / n :=
begin
  rcases eq_or_ne n 0 with rfl | hn,
  { simp [int.div_zero] },
  { exact cast_div n_dvd (cast_ne_zero.mpr hn), },
end

end int

lemma ring_hom.injective_int {α : Type*} [non_assoc_ring α] (f : ℤ →+* α) [char_zero α] :
  function.injective f :=
subsingleton.elim (int.cast_ring_hom _) f ▸ int.cast_injective

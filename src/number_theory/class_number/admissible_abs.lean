/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import number_theory.class_number.admissible_absolute_value

/-!
# Admissible absolute value on the integers
This file defines an admissible absolute value `absolute_value.abs_is_admissible`
which we use to show the class number of the ring of integers of a number field
is finite.

## Main results

 * `absolute_value.abs_is_admissible` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is admissible.
-/

namespace absolute_value

open int

/-- We can partition a finite family into `partition_card ε` sets, such that the remainders
in each set are close together. -/
lemma exists_partition_int (n : ℕ) {ε : ℝ} (hε : 0 < ε) {b : ℤ} (hb : b ≠ 0) (A : fin n → ℤ) :
  ∃ (t : fin n → fin (nat_ceil (1 / ε))),
  ∀ i₀ i₁, t i₀ = t i₁ → ↑(abs (A i₁ % b - A i₀ % b)) < abs b • ε :=
begin
  have hb' : (0 : ℝ) < ↑(abs b) := int.cast_pos.mpr (abs_pos.mpr hb),
  have hbε : 0 < abs b • ε,
  { rw algebra.smul_def,
    exact mul_pos hb' hε },
  have hfloor : ∀ i, 0 ≤ floor ((A i % b : ℤ) / (abs b • ε) : ℝ),
  { intro i,
    exact floor_nonneg.mpr (div_nonneg (cast_nonneg.mpr (mod_nonneg _ hb)) hbε.le) },
  refine ⟨λ i, ⟨nat_abs (floor ((A i % b : ℤ) / (abs b • ε) : ℝ)), _⟩, _⟩,
  { rw [← coe_nat_lt, nat_abs_of_nonneg (hfloor i), floor_lt],
    apply lt_of_lt_of_le _ (le_nat_ceil _),
    rw [algebra.smul_def, ring_hom.eq_int_cast, ← div_div_eq_div_mul, div_lt_div_right hε,
        div_lt_iff hb', one_mul, cast_lt],
    exact int.mod_lt _ hb },
  intros i₀ i₁ hi,
  have hi : (⌊↑(A i₀ % b) / abs b • ε⌋.nat_abs : ℤ) = ⌊↑(A i₁ % b) / abs b • ε⌋.nat_abs :=
    congr_arg (coe : ℕ → ℤ) (subtype.mk_eq_mk.mp hi),
  rw [nat_abs_of_nonneg (hfloor i₀), nat_abs_of_nonneg (hfloor i₁)] at hi,
  have hi := abs_sub_lt_one_of_floor_eq_floor hi,
  rw [abs_sub_comm, ← sub_div, abs_div, abs_of_nonneg hbε.le, div_lt_iff hbε, one_mul] at hi,
  rwa [int.cast_abs, int.cast_sub]
end

/-- `abs : ℤ → ℤ` is an admissible absolute value -/
noncomputable def abs_is_admissible : is_admissible absolute_value.abs :=
{ card := λ ε, nat_ceil (1 / ε),
  exists_partition' := λ n ε hε b hb, exists_partition_int n hε hb,
  .. absolute_value.abs_is_euclidean }

noncomputable instance : inhabited (is_admissible absolute_value.abs) :=
⟨abs_is_admissible⟩

end absolute_value

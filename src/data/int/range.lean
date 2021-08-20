/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
import data.int.basic
import data.list.range

/-!
# Intervals in ℤ

This file defines integer ranges. `range m n` is the set of integers greater than `m` and strictly
less than `n`.

## Note

This could be unified with `data.list.intervals`. See the TODOs there.
-/

namespace int

local attribute [semireducible] int.nonneg

/-- List enumerating `[m, n)`. This is the ℤ variant of `list.Ico`. -/
def range (m n : ℤ) : list ℤ :=
(list.range (to_nat (n-m))).map $ λ r, m+r

theorem mem_range_iff {m n r : ℤ} : r ∈ range m n ↔ m ≤ r ∧ r < n :=
⟨λ H, let ⟨s, h1, h2⟩ := list.mem_map.1 H in h2 ▸
  ⟨le_add_of_nonneg_right trivial,
  add_lt_of_lt_sub_left $ match n-m, h1 with
    | (k:ℕ), h1 := by rwa [list.mem_range, to_nat_coe_nat, ← coe_nat_lt] at h1
    end⟩,
λ ⟨h1, h2⟩, list.mem_map.2 ⟨to_nat (r-m),
  list.mem_range.2 $ by rw [← coe_nat_lt, to_nat_of_nonneg (sub_nonneg_of_le h1),
      to_nat_of_nonneg (sub_nonneg_of_le (le_of_lt (lt_of_le_of_lt h1 h2)))];
    exact sub_lt_sub_right h2 _,
  show m + _ = _, by rw [to_nat_of_nonneg (sub_nonneg_of_le h1), add_sub_cancel'_right]⟩⟩

instance decidable_le_lt (P : int → Prop) [decidable_pred P] (m n : ℤ) :
  decidable (∀ r, m ≤ r → r < n → P r) :=
decidable_of_iff (∀ r ∈ range m n, P r) $ by simp only [mem_range_iff, and_imp]

instance decidable_le_le (P : int → Prop) [decidable_pred P] (m n : ℤ) :
  decidable (∀ r, m ≤ r → r ≤ n → P r) :=
decidable_of_iff (∀ r ∈ range m (n+1), P r) $ by simp only [mem_range_iff, and_imp, lt_add_one_iff]

instance decidable_lt_lt (P : int → Prop) [decidable_pred P] (m n : ℤ) :
  decidable (∀ r, m < r → r < n → P r) :=
int.decidable_le_lt P _ _

instance decidable_lt_le (P : int → Prop) [decidable_pred P] (m n : ℤ) :
  decidable (∀ r, m < r → r ≤ n → P r) :=
int.decidable_le_le P _ _

end int

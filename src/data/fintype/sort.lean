/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Mario Carneiro
-/
import data.fintype.basic
import data.finset.sort

variables {α : Type*}

open finset

/-- Given a linearly ordered fintype `α` of cardinal `k`, the equiv `mono_equiv_of_fin α h`
is the increasing bijection between `fin k` and `α`. Here, `h` is a proof that
the cardinality of `s` is `k`. We use this instead of a map `fin s.card → α` to avoid
casting issues in further uses of this function. -/
noncomputable def mono_equiv_of_fin (α) [fintype α] [decidable_linear_order α] {k : ℕ}
  (h : fintype.card α = k) : fin k ≃ α :=
equiv.of_bijective (mono_of_fin univ h) begin
  apply set.bijective_iff_bij_on_univ.2,
  rw ← @coe_univ α _,
  exact mono_of_fin_bij_on (univ : finset α) h
end

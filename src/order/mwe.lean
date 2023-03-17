/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import order.locally_finite
import order.well_founded_set

/-! # Thoughts on where to put this? -/

variables {α : Type*} {s : set α} [preorder α] [locally_finite_order α]

open set

lemma bdd_below.well_founded_on_lt : bdd_below s → s.well_founded_on (<) :=
begin
  rw well_founded_on_iff_no_descending_seq,
  rintro ⟨a, ha⟩ f hf,
  exact infinite_range_of_injective f.injective ((finite_Icc a $ f 0).subset $ range_subset_iff.2 $
    λ n, ⟨ha $ hf _, antitone_iff_forall_lt.2 (λ a b hab, (f.map_rel_iff.2 hab).le) $ zero_le _⟩),
end

lemma bdd_above.well_founded_on_gt (hs : bdd_above s) : s.well_founded_on (>) :=
hs.dual.well_founded_on_lt

/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.multiset.basic
import combinatorics.simplicial_complex.to_move.list

lemma multiset.exists_min_of_inf_closed {α : Type*} [semilattice_inf α] {s : multiset α}
  (hs₁ : s ≠ 0) (hs₂ : ∀ x y ∈ s, x ⊓ y ∈ s) :
  ∃ z ∈ s, ∀ y ∈ s, z ≤ y :=
begin
  revert hs₁ hs₂,
  apply quotient.induction_on s,
  intros s hs₁ hs₂,
  apply list.exists_min_of_inf_closed _ hs₂,
  intro t,
  rw ←multiset.coe_eq_zero at t,
  apply hs₁ t,
end

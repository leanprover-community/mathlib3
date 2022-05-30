/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/

/-!
# To move
-/

variables {α : Type*} {R : α → α → Prop} {a b : α}

lemma curry_eq_of_symmetric_transitive (hRsymm : symmetric R) (hRtrans : transitive R)
  (hab : R a b) : R a = R b :=
funext $ λ c, propext ⟨hRtrans $ hRsymm hab, hRtrans hab⟩

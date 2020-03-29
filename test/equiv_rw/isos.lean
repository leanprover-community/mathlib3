/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw
import category_theory.functorial
import category_theory.types
import algebra.category.CommRing.basic
import data.polynomial

universes u

set_option trace.equiv_rw_type true

open category_theory

mk_simp_attribute functoriality
"The simpset `functoriality` is used by the tactic `equiv_rw`
to write expressions explicitly as applications of functors."

@[functoriality]
lemma coe_as_forget (R : Ring.{u}) : (R : Type u) = (forget Ring.{u}).obj R := rfl

-- set_option trace.app_builder true
-- set_option pp.all true

example (R S : Ring.{u}) (i : R ≅ S) (r : R) : S :=
begin
  -- let t : R ≃ _ := by equiv_rw_type i,
  equiv_rw i at r,
  exact r,
end

example (R S : Ring.{u}) (i : R ≅ S) (s : S) : R :=
begin
  equiv_rw i,
  dsimp, -- maybe dsimp the other way afterwards?
  exact s,
end

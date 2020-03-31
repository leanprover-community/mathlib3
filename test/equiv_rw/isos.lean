/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.equiv_rw
import category_theory.functorial
import category_theory.types
import algebra.category.CommRing.basic

universes u

set_option trace.equiv_rw_type true

open category_theory

mk_simp_attribute functoriality
"The simpset `functoriality` is used by the tactic `equiv_rw`
to write expressions explicitly as applications of functors."

@[functoriality]
lemma coe_as_forget (R : Ring.{u}) : (R : Type u) = (forget Ring.{u}).obj R := rfl


example (R S : Ring.{u}) (i : R ≅ S) (r : R) : S :=
begin
  equiv_rw i at r,
  exact r,
end

example (R S : Ring.{u}) (i : R ≅ S) (s : S) : R :=
begin
  equiv_rw i,
  dsimp,
  exact s,
end

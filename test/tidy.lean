/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import tactic.tidy

open tactic

namespace tidy.test

meta def interactive_simp := `[simp]

def tidy_test_1 (a : string) : ∀ x : unit, x = unit.star :=
begin
  tidy -- intros x, exact dec_trivial
end

structure A :=
(z : ℕ)

structure B :=
(a : A)
(aa : a.z = 0)

structure C :=
(a : A)
(b : B)
(ab : a.z = b.a.z)

structure D :=
(a : B)
(b : C)
(ab : a.a.z = b.a.z)

open tactic

def d : D :=
begin
  tidy,

  -- Try this: fsplit, work_on_goal 0 { fsplit, work_on_goal 0 { fsplit }, work_on_goal 1 { refl }
  -- }, work_on_goal 0 { fsplit, work_on_goal 0 { fsplit }, work_on_goal 1 { fsplit, work_on_goal 0
  -- { fsplit }, work_on_goal 1 { refl } }, work_on_goal 1 { refl } }, refl
end.

def f : unit → unit → unit := by tidy -- intros a a_1, cases a_1, cases a, fsplit

def g (P Q : Prop) (p : P) (h : P ↔ Q) : Q := by tidy

end tidy.test

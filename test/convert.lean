/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import data.set.basic
import tactic.interactive

open set

variables {α β : Type}
@[simp] lemma singleton_inter_singleton_eq_empty {x y : α} :
  ({x} ∩ {y} = (∅ : set α)) ↔ x ≠ y :=
by simp [singleton_inter_eq_empty]

example {f : β → α} {x y : α} (h : x ≠ y) : f ⁻¹' {x} ∩ f ⁻¹' {y} = ∅ :=
begin
  have : {x} ∩ {y} = (∅ : set α) := by simpa using h,
  convert preimage_empty,
  rw [←preimage_inter,this],
end

example (P : Prop) (h : P) : P := by convert h

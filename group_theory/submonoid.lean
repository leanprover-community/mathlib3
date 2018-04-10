/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
import algebra.group_power

variables {α : Type*} [monoid α]

/-- `s` is a submonoid: a set containing 1 and closed under multiplication. -/
class is_submonoid (s : set α) : Prop :=
(one_mem : (1:α) ∈ s)
(mul_mem {a b} : a ∈ s → b ∈ s → a * b ∈ s)

section powers
def powers (x : α) : set α := {y | ∃ n:ℕ, x^n = y}

instance powers.is_submonoid (x : α) : is_submonoid (powers x) :=
{ one_mem := ⟨0, by simp⟩,
  mul_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [pow_add, *]⟩ }

lemma is_submonoid.pow_mem {a : α} {s : set α} [is_submonoid s] (h : a ∈ s) :
  ∀{n:ℕ}, a ^ n ∈ s
| 0 := is_submonoid.one_mem s
| (n + 1) := is_submonoid.mul_mem h is_submonoid.pow_mem

end powers

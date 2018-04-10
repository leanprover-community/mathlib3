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

instance subtype.monoid {s : set α} [is_submonoid s] : monoid s :=
{ mul       := λa b : s, ⟨a * b, is_submonoid.mul_mem a.2 b.2⟩,
  one       := ⟨1, is_submonoid.one_mem s⟩,
  mul_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq $ mul_assoc _ _ _,
  one_mul   := assume ⟨a, _⟩, subtype.eq $ one_mul _,
  mul_one   := assume ⟨a, _⟩, subtype.eq $ mul_one _ }

namespace monoid

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| one : in_closure 1
| mul {a b : α} : in_closure a → in_closure b → in_closure (a * b)

def closure (s : set α) : set α := {a | in_closure s a }

instance closure.is_submonoid (s : set α) : is_submonoid (closure s) :=
{ one_mem := in_closure.one s, mul_mem := assume a b, in_closure.mul }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_submonoid.one_mem, is_submonoid.mul_mem]

end monoid

/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Johannes Hölzl, Kenny Lau.

This file is a modification of `group_theory/submonoid.lean`.
It simply translates all the multiplicative
notions into their additive counterparts.
-/
import algebra.group_power

variables {α : Type*} [add_monoid α] {s : set α}

/-- `s` is an additive submonoid: a set containing 0 and closed under addition. -/
class is_add_submonoid (s : set α) : Prop :=
(zero_mem : (0:α) ∈ s)
(add_mem {a b} : a ∈ s → b ∈ s → a + b ∈ s)

section multiples
def multiples (x : α) : set α := {y | ∃ n:ℕ, add_monoid.smul n x = y}

instance multiples.is_add_submonoid (x : α) : is_add_submonoid (multiples x) :=
{ zero_mem := ⟨0, by simp⟩,
  add_mem := λ x₁ x₂ ⟨n₁, hn₁⟩ ⟨n₂, hn₂⟩, ⟨n₁ + n₂, by simp [add_monoid.add_smul, *]⟩ }

lemma is_add_submonoid.smul_mem {a : α} [is_add_submonoid s] (h : a ∈ s) :
  ∀{n:ℕ}, add_monoid.smul n a ∈ s
| 0 := is_add_submonoid.zero_mem s
| (n + 1) := is_add_submonoid.add_mem h is_add_submonoid.smul_mem

lemma is_add_submonoid.multiple_subset {a : α} [is_add_submonoid s] (h : a ∈ s) : multiples a ⊆ s :=
assume x ⟨n, hx⟩, hx ▸ is_add_submonoid.smul_mem h

end multiples

lemma is_add_submonoid.list_sum_mem [is_add_submonoid s] : ∀{l : list α}, (∀x∈l, x ∈ s) → l.sum ∈ s
| []     h := is_add_submonoid.zero_mem s
| (a::l) h :=
  suffices a + l.sum ∈ s, by simpa,
  have a ∈ s ∧ (∀x∈l, x ∈ s), by simpa using h,
  is_add_submonoid.add_mem this.1 (is_add_submonoid.list_sum_mem this.2)

instance subtype.add_monoid {s : set α} [is_add_submonoid s] : add_monoid s :=
{ add       := λa b : s, ⟨a + b, is_add_submonoid.add_mem a.2 b.2⟩,
  zero       := ⟨0, is_add_submonoid.zero_mem s⟩,
  add_assoc := assume ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩, subtype.eq $ add_assoc _ _ _,
  zero_add   := assume ⟨a, _⟩, subtype.eq $ zero_add _,
  add_zero   := assume ⟨a, _⟩, subtype.eq $ add_zero _ }

namespace add_monoid

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| zero : in_closure 0
| add {a b : α} : in_closure a → in_closure b → in_closure (a + b)

def closure (s : set α) : set α := {a | in_closure s a }

instance closure.is_add_submonoid (s : set α) : is_add_submonoid (closure s) :=
{ zero_mem := in_closure.zero s, add_mem := assume a b, in_closure.add }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_add_submonoid t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, is_add_submonoid.zero_mem, is_add_submonoid.add_mem]

theorem exists_list_of_mem_closure {s : set α} {a : α} (h : a ∈ closure s) :
  (∃l:list α, (∀x∈l, x ∈ s) ∧ l.sum = a) :=
begin
  induction h,
  case in_closure.basic : a ha { existsi ([a]), simp [ha] },
  case in_closure.zero { existsi ([]), simp },
  case in_closure.add : a b _ _ ha hb {
    rcases ha with ⟨la, ha, eqa⟩,
    rcases hb with ⟨lb, hb, eqb⟩,
    existsi (la ++ lb),
    simp [eqa.symm, eqb.symm, or_imp_distrib],
    exact assume a, ⟨ha a, hb a⟩
  }
end

end add_monoid
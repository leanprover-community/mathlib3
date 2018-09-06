/-
Copyright (c) 2018 Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Sean Leather

Constructive infinite types.
-/

import data.finset data.fintype

variables {α : Type*}

/-- A type is (constructively) infinite if it can be shown that, for any finite
set of inhabitants of that type, there exists an inhabitant not in the set.

To contrast with `fintype` nomenclature, any `finset α`, in which `α` is
infinite, is naturally incomplete. -/
class infinite (α : Type*) : Prop :=
(incomplete : ∀ (s : finset α), ∃ (a : α), a ∉ s)

namespace fintype
open infinite

theorem not_infinite [fintype α] : ¬ infinite α :=
λ h, let ⟨a, h'⟩ := @incomplete _ h (elems α) in h' (complete a)

end fintype

/- infinite nat -/

namespace finset

/-- Successor of the maximum: the minimum nat not a member of a finite set -/
def max_succ (s : finset ℕ) : ℕ :=
match s.max with
| none   := 0
| some m := m + 1
end

@[simp] theorem max_succ_empty : max_succ ∅ = 0 :=
rfl

@[simp] theorem max_succ_of_ne_empty {s : finset ℕ} (h : s ≠ ∅) :
  s.max_succ = s.max.iget + 1 :=
let ⟨m, hm⟩ := finset.max_of_ne_empty h in
by simp [option.mem_def.mp hm, max_succ, option.iget]

theorem max_succ_not_mem (s : finset ℕ) : s.max_succ ∉ s :=
λ h, if p : s = ∅ then
  by simpa [p] using h
else
  let ⟨m, hm⟩ := finset.max_of_ne_empty p in
  have hms : m+1 ∈ s := by simpa [max_succ, option.mem_def.mp hm] using h,
  m.not_succ_le_self $ le_max_of_mem hms hm

end finset

instance infinite.nat : infinite ℕ :=
⟨λ s, ⟨finset.max_succ s, finset.max_succ_not_mem s⟩⟩

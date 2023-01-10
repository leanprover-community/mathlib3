/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import data.nat.modeq
import data.list.rotate

/-! # List rotation and modular arithmetic -/

namespace list
variable {α : Type*}

lemma nth_rotate {l : list α} {n m : ℕ} (hml : m < l.length) :
  (l.rotate n).nth m = l.nth ((m + n) % l.length) :=
begin
  rw [nth_le_nth, nth_le_nth (nat.mod_lt _ _), nth_le_rotate],
  rwa [length_rotate]
end

lemma head'_rotate {l : list α} {n : ℕ} (h : n < l.length) :
  head' (l.rotate n) = l.nth n :=
by rw [← nth_zero, nth_rotate (n.zero_le.trans_lt h), zero_add, nat.mod_eq_of_lt h]

lemma rotate_eq_self_iff_eq_replicate [hα : nonempty α] :
  ∀ {l : list α}, (∀ n, l.rotate n = l) ↔ ∃ a, l = replicate l.length a
| [] := by simp
| (a :: l) := ⟨λ h, ⟨a, ext_le (length_replicate _ _).symm $ λ n h₁ h₂,
  begin
    inhabit α,
    rw [nth_le_replicate, ← option.some_inj, ← nth_le_nth, ← head'_rotate h₁, h, head']
  end⟩, λ ⟨b, hb⟩ n, by rw [hb, rotate_replicate]⟩

lemma rotate_one_eq_self_iff_eq_replicate [nonempty α] {l : list α} :
  l.rotate 1 = l ↔ ∃ a : α, l = list.replicate l.length a :=
⟨λ h, rotate_eq_self_iff_eq_replicate.mp (λ n, nat.rec l.rotate_zero
  (λ n hn, by rwa [nat.succ_eq_add_one, ←l.rotate_rotate, hn]) n),
    λ h, rotate_eq_self_iff_eq_replicate.mpr h 1⟩

end list

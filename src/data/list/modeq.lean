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

lemma nth_rotate : ∀ {l : list α} {n m : ℕ} (hml : m < l.length),
  (l.rotate n).nth m = l.nth ((m + n) % l.length)
| []     n     m hml := (nat.not_lt_zero _ hml).elim
| l      0     m hml := by simp [nat.mod_eq_of_lt hml]
| (a::l) (n+1) m hml :=
have h₃ : m < list.length (l ++ [a]), by simpa using hml,
(lt_or_eq_of_le (nat.le_of_lt_succ $ nat.mod_lt (m + n)
  (lt_of_le_of_lt (nat.zero_le _) hml))).elim
(λ hml',
  have h₁ : (m + (n + 1)) % ((a :: l : list α).length) =
      (m + n) % ((a :: l : list α).length) + 1,
    from calc (m + (n + 1)) % (l.length + 1) =
      ((m + n) % (l.length + 1) + 1) % (l.length + 1) :
        add_assoc m n 1 ▸ nat.modeq.add_right 1 (nat.mod_mod _ _).symm
    ... = (m + n) % (l.length + 1) + 1 : nat.mod_eq_of_lt (nat.succ_lt_succ hml'),
  have h₂ : (m + n) % (l ++ [a]).length < l.length, by simpa [nat.add_one] using hml',
  by rw [list.rotate_cons_succ, nth_rotate h₃, list.nth_append h₂, h₁, list.nth]; simp)
(λ hml',
  have h₁ : (m + (n + 1)) % (l.length + 1) = 0,
    from calc (m + (n + 1)) % (l.length + 1) = (l.length + 1) % (l.length + 1) :
      add_assoc m n 1 ▸ nat.modeq.add_right 1
        (hml'.trans (nat.mod_eq_of_lt (nat.lt_succ_self _)).symm)
    ... = 0 : by simp,
  by rw [list.length, list.rotate_cons_succ, nth_rotate h₃, list.length_append,
    list.length_cons, list.length, zero_add, hml', h₁, list.nth_concat_length]; refl)

lemma rotate_eq_self_iff_eq_repeat [hα : nonempty α] : ∀ {l : list α},
  (∀ n, l.rotate n = l) ↔ ∃ a, l = list.repeat a l.length
| []     := ⟨λ h, nonempty.elim hα (λ a, ⟨a, by simp⟩), by simp⟩
| (a::l) :=
⟨λ h, ⟨a, list.ext_le (by simp) $ λ n hn h₁,
  begin
    rw [← option.some_inj, ← list.nth_le_nth],
    conv {to_lhs, rw ← h ((list.length (a :: l)) - n)},
    rw [nth_rotate hn, add_tsub_cancel_of_le (le_of_lt hn),
      nat.mod_self, nth_le_repeat], refl
  end⟩,
  λ ⟨a, ha⟩ n, ha.symm ▸ list.ext_le (by simp)
    (λ m hm h,
      have hm' : (m + n) % (list.repeat a (list.length (a :: l))).length < list.length (a :: l),
        by rw list.length_repeat; exact nat.mod_lt _ (nat.succ_pos _),
      by rw [nth_le_repeat, ← option.some_inj, ← list.nth_le_nth, nth_rotate h, list.nth_le_nth,
        nth_le_repeat]; simp * at *)⟩

lemma rotate_repeat (a : α) (n : ℕ) (k : ℕ) :
  (list.repeat a n).rotate k = list.repeat a n :=
let h : nonempty α := ⟨a⟩ in by exactI rotate_eq_self_iff_eq_repeat.mpr ⟨a, by rw length_repeat⟩ k

lemma rotate_one_eq_self_iff_eq_repeat [nonempty α] {l : list α} :
  l.rotate 1 = l ↔ ∃ a : α, l = list.repeat a l.length :=
⟨λ h, rotate_eq_self_iff_eq_repeat.mp (λ n, nat.rec l.rotate_zero
  (λ n hn, by rwa [nat.succ_eq_add_one, ←l.rotate_rotate, hn]) n),
    λ h, rotate_eq_self_iff_eq_repeat.mpr h 1⟩

end list

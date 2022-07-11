/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.list.defs

/-!
# Accessing lists with default values

-/

namespace list

section inth

variables {α : Type*} [inhabited α] (l : list α) (x : α) (xs : list α) (n : ℕ)

@[simp] lemma inth_nil : inth ([] : list α) n = default := rfl

@[simp] lemma inth_cons_zero : inth (x::xs) 0 = x := rfl

@[simp] lemma inth_cons_succ : inth (x::xs) (n + 1) = inth xs n := rfl

lemma inth_eq_nth_le {n : ℕ} (hn : n < l.length) : l.inth n = l.nth_le n hn :=
begin
  induction l with hd tl IH generalizing n,
  { exact absurd hn (not_lt_of_ge (nat.zero_le _)) },
  { cases n,
    { exact inth_cons_zero _ _ },
    { exact IH _ } }
end

lemma inth_eq_default {n : ℕ} (hn : l.length ≤ n) : l.inth n = default :=
begin
  induction l with hd tl IH generalizing n,
  { exact inth_nil _ },
  { cases n,
    { refine absurd (nat.zero_lt_succ _) (not_lt_of_ge hn) },
    { exact IH (nat.le_of_succ_le_succ hn) } }
end

end inth

section nthd

variables {α : Type*} (l : list α) (x : α) (xs : list α) (d : α) (n : ℕ)

/-- "default" `nth` function: returns `d` instead of `none` in the case
  that the index is out of bounds. -/
def nthd (l : list α) (n : ℕ) : α :=
@inth _ ⟨d⟩ l n

@[simp] lemma nthd_nil : nthd d [] n = d := rfl

@[simp] lemma nthd_cons_zero : nthd d (x::xs) 0 = x := rfl

@[simp] lemma nthd_cons_succ : nthd d (x::xs) (n + 1) = nthd d xs n := rfl

lemma nthd_eq_nth_le {n : ℕ} (hn : n < l.length) : l.nthd d n = l.nth_le n hn :=
by letI : inhabited α := _; exact inth_eq_nth_le _ _

lemma nthd_eq_default {n : ℕ} (hn : l.length ≤ n) : l.nthd d n = d :=
by letI : inhabited α := _; exact inth_eq_default _ hn

instance decidable_nthd_nil_ne {α} (a : α) : decidable_pred
  (λ (i : ℕ), nthd a ([] : list α) i ≠ a) := λ i, is_false $ λ H, H (nthd_nil _ _)

@[simp] lemma nthd_singleton_default_eq (n : ℕ) : [d].nthd d n = d :=
by { cases n; simp }

@[simp] lemma nthd_repeat_default_eq (r n : ℕ) : (repeat d r).nthd d n = d :=
begin
  induction r with r IH generalizing n,
  { simp },
  { cases n;
    simp [IH] }
end

lemma nthd_default_eq_inth {α : Type*} [inhabited α] (l : list α) :
  l.nthd default = l.inth :=
begin
  funext n,
  cases lt_or_le n l.length with hn hn,
  { rw [nthd_eq_nth_le _ _ hn, inth_eq_nth_le _ hn] },
  { rw [nthd_eq_default _ _ hn, inth_eq_default _ hn] }
end

end nthd

end list

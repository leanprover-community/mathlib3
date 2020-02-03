/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import data.nat.basic
import tactic

/-!
# Strong recursion

A strong recursion principle based on `fin`.

-/

namespace nat
universe variable u
variables {X : ℕ → Sort u} (f : Π n, (Π (m:fin n), X m) → X n)

protected def strong_recursion_aux :
  Π n m, m < n → X m
| 0     := λ _ h, absurd h (not_lt_zero _)
| (n+1) := λ m h,
(lt_or_eq_of_le (le_of_lt_succ h)).by_cases
  (strong_recursion_aux n m)
  (λ e, f _ (λ k, strong_recursion_aux n _ $ lt_of_lt_of_le k.2 $ le_of_eq e))

def strong_recursion (n : ℕ) : X n :=
nat.strong_recursion_aux f (n+1) n $ n.lt_succ_self

@[simp] lemma strong_recursion_aux_lt (m n : ℕ) (h : m < n) :
  nat.strong_recursion_aux f n m h = strong_recursion f m :=
begin
  obtain ⟨k, rfl⟩ : ∃ k, n = m + 1 + k :=
  by simpa [add_right_comm] using nat.exists_eq_add_of_lt h,
  induction k with k ih, { refl },
  have hm : m < m + 1 + k, by linarith,
  rw ← ih hm,
  exact dif_pos hm,
end

lemma strong_recursion_apply (n : ℕ) :
  strong_recursion f n = f n (λ i, strong_recursion f i) :=
begin
  show nat.strong_recursion_aux f (n+1) n _ = _,
  show dite (n < n) _ _ = _,
  rw [dif_neg (lt_irrefl n)],
  show dite (n = n) _ _ = _,
  rw [dif_pos rfl],
  refine congr_arg (f n) _,
  funext k,
  apply strong_recursion_aux_lt,
end

end nat

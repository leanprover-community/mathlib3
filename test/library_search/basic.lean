import data.nat.basic
import tactic.library_search

-- Turn off trace messages so they don't pollute the test build:
set_option trace.silence_library_search true
-- For debugging purposes, we can display the list of lemmas:
-- set_option trace.library_search true

-- Check that `library_search` fails if there are no goals.
example : true :=
begin
  trivial,
  success_if_fail { library_search },
end

example (a b : ℕ) : a + b = b + a :=
by library_search -- says: `exact add_comm a b`

example {a b : ℕ} : a ≤ a + b :=
by library_search -- says: `exact le_add_right a b`

example (n m k : ℕ) : n * (m - k) = n * m - n * k :=
by library_search -- says: `exact nat.mul_sub_left_distrib n m k`

example {n m : ℕ} (h : m < n) : m ≤ n - 1 :=
by library_search -- says: `exact nat.le_pred_of_lt h`

example {α : Type} (x y : α) : x = y ↔ y = x :=
by library_search -- says: `exact eq_comm`

example (a b : ℕ) (ha : 0 < a) (hb : 0 < b) : 0 < a + b :=
by library_search -- says: `exact add_pos ha hb`

example (a b : ℕ) : 0 < a → 0 < b → 0 < a + b :=
by library_search -- says: `exact add_pos`

example (a b : ℕ) (h : a ∣ b) (w : b > 0) : a ≤ b :=
by library_search -- says: `exact nat.le_of_dvd w h`


-- We even find `iff` results:

example {b : ℕ} (w : b > 0) : b ≥ 1 :=
by library_search -- says: `exact nat.succ_le_iff.mpr w`

example : ∀ P : Prop, ¬(P ↔ ¬P) :=
by library_search -- says: `λ (a : Prop), (iff_not_self a).mp`

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
by library_search -- says `exact (nat.dvd_add_left h₁).mp h₂`

example {a b c : ℕ} (h₁ : a ∣ b) (h₂ : a ∣ b + c) : a ∣ c :=
by library_search -- says `exact (nat.dvd_add_left h₁).mp h₂`

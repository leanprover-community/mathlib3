/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Scott Morrison
-/
import tactic data.set.lattice data.prod data.vector
       tactic.rewrite data.stream.basic

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
begin
  apply_assumption,
  apply_assumption,
end

example {a b : Prop} (h₀ : a → b) (h₁ : a) : b :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : ∀ x : α, b x = a x) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
  success_if_fail { solve_by_elim only [] },
  success_if_fail { solve_by_elim only [h₀] },
  solve_by_elim only [h₀, congr_fun]
end

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
by solve_by_elim [h₀]

example {α : Type} {a b : α → Prop} (h₀ : b = a) (y : α) : a y = b y :=
begin
 success_if_fail { solve_by_elim [*, -h₀] },
 solve_by_elim [*]
end

example {α β : Type} (a b : α) (f : α → β) (i : function.injective f) (h : f a = f b) : a = b :=
begin
  success_if_fail { solve_by_elim only [i] },
  success_if_fail { solve_by_elim only [h] },
  solve_by_elim only [i,h]
end

@[user_attribute]
meta def ex : user_attribute := {
  name := `ex,
  descr := "An example attribute for testing solve_by_elim."
}

@[ex] def f : ℕ := 0

example : ℕ := by solve_by_elim [f]

example : ℕ :=
begin
  success_if_fail { solve_by_elim },
  success_if_fail { solve_by_elim [-f] with ex },
  solve_by_elim with ex,
end

example {α : Type} {p : α → Prop} (h₀ : ∀ x, p x) (y : α) : p y :=
begin
  apply_assumption,
end

open tactic

example : true :=
begin
  (do gs ← get_goals,
     set_goals [],
     success_if_fail `[solve_by_elim],
     set_goals gs),
  trivial
end

example {α : Type} (r : α → α → Prop) (f : α → α → α)
  (l : ∀ a b c : α, r a b → r a (f b c) → r a c)
  (a b c : α) (h₁ : r a b) (h₂ : r a (f b c)) : r a c :=
begin
  solve_by_elim,
end

-- Verifying that solve_by_elim behaves as expected in the presence of multiple goals.
example (n : ℕ) : ℕ × ℕ :=
begin
  split,
  solve_by_elim,
  solve_by_elim
end

example {P Q : Prop} (h : P ↔ Q) (h : P) : Q :=
begin
  solve_by_elim
end

example {P Q : Prop} (h : P ↔ Q) (h : Q) : P :=
begin
  solve_by_elim
end

example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  solve_by_elim [nat.dvd_add_iff_left],
end

meta def dvd_attribute : user_attribute := {
  name := `dvd,
  descr := "A lemma that concludes a ∣ b."
}

run_cmd attribute.register ``dvd_attribute

local attribute [dvd] dvd.intro dvd.intro_left dvd_add dvd_add_iff_left dvd_add_iff_right dvd_mul_left 
  dvd_mul_of_dvd_left dvd_mul_of_dvd_right dvd_mul_right dvd_neg_iff_dvd dvd_neg_of_dvd dvd_of_dvd_neg 
  dvd_of_mul_left_dvd dvd_of_mul_right_dvd dvd_of_neg_dvd dvd_refl dvd_sub dvd_trans dvd_zero list.dvd_prod
  mul_dvd_mul mul_dvd_mul_left mul_dvd_mul_right nat.decidable_dvd._proof_1 nat.div_dvd_of_dvd nat.dvd_add_iff_left
  nat.dvd_add_iff_right nat.dvd_div_of_mul_dvd nat.dvd_fact nat.dvd_iff_mod_eq_zero nat.dvd_mod_iff
  nat.dvd_of_mod_eq_zero nat.dvd_of_mul_dvd_mul_left nat.dvd_of_mul_dvd_mul_right nat.dvd_of_pow_dvd nat.dvd_one
  nat.dvd_sub nat.fact_dvd_fact nat.mul_dvd_mul_iff_left nat.mul_dvd_mul_iff_right nat.mul_dvd_of_dvd_div
  nat.pow_dvd_of_le_of_pow_dvd nat.pow_dvd_pow nat.pow_dvd_pow_of_dvd neg_dvd_iff_dvd neg_dvd_of_dvd one_dvd

lemma dvd_example {a b c : ℕ} (h₁ : a ∣ c) (h₂ : a ∣ b + c) : a ∣ b :=
begin
  solve_by_elim with dvd,
end.

-- #print dvd_example

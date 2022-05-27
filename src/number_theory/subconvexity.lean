/-
Copyright (c) 2022 Alex Kontorovich and Paul Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Paul Nelson
-/

import linear_algebra.general_linear_group
import analysis.matrix

/-!
# Stuff we prove

We will prove yadda yadda

## Main definitions

The definitions

## Main results

Main results

# Discussion

Stuff

-/

open complex matrix

noncomputable theory

local notation `M` n := matrix (fin n) (fin n) ℂ

def upper_left_injection {n : ℕ} :
  (M n) → (M (n+1)) := λ A i j,
  dite (i.val < n ∧ j.val < n)
  (λ (hij : i.val < n ∧ j.val < n), A (fin.mk i hij.1) (fin.mk j hij.2))
  (λ (hij : ¬ (i.val < n ∧ j.val < n)), 0)

def z {n : ℕ} : M (n+1) :=
  λ i j, if (i.val < n ∧ j.val < n ∧ i.val = j.val) then 1 else 0

def bracket {n : ℕ} (A B : M n) : M n :=
  A * B - B * A

def upper_left_restriction {n : ℕ} :
  (M (n+1)) → (M n) := λ A i j,
  A (fin.mk i (by linarith [i.2] : i.val < n + 1)) (fin.mk j (by linarith [j.2] : j.val < n + 1))

def is_eigenvalue {n : ℕ} (A : M n) (μ : ℂ) : Prop := (A - μ • 1).det = 0

theorem one_point_eight {n : ℕ} (τ x : M (n+1))
  (hτ : ∃ c : ℂ, is_eigenvalue τ c → ¬ (is_eigenvalue (upper_left_restriction τ) c))
  (hxτ : bracket τ x = 0)
  (hxτ' : ∃ y : M (n+1), bracket x (bracket z τ ) = bracket y τ)
  : ∃ μ : ℂ, x = μ • 1 :=
  sorry

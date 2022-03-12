/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import data.fin.tuple
import data.finsupp.basic

/-! `cons` and `tail` for maps `fin n →₀ M` and their properties -/

noncomputable theory

namespace finsupp

variable {n : ℕ}

/-- `tail` for maps `fin (n+1) →₀ M`. See `fin.tail` for more details. -/
def tail (s : fin (n+1) →₀ ℕ) : fin n →₀ ℕ :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.tail s.to_fun)

/-- `cons` for maps `fin n →₀ M`. See `fin.cons` for more details. -/
def cons (y : ℕ) (s : fin n →₀ ℕ) : fin (n+1) →₀ ℕ :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.cons y s.to_fun)

lemma tail_apply (s : fin (n+1) →₀ ℕ) (i : fin n) : tail s i = s i.succ :=
begin
  simp only [tail, equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe],
  congr,
end

@[simp] lemma cons_zero (y : ℕ) (s : fin n →₀ ℕ) : cons y s 0 = y :=
by simp [cons, finsupp.equiv_fun_on_fintype]

@[simp] lemma cons_succ (i : fin n) (y : ℕ) (s : fin n →₀ ℕ) : cons y s i.succ = s i :=
begin

  simp only [finsupp.cons, fin.cons, finsupp.equiv_fun_on_fintype, fin.cases_succ, finsupp.coe_mk],
  refl,
end

@[simp] lemma tail_cons (y : ℕ) (s : fin n →₀ ℕ) : tail (cons y s) = s :=
begin
  simp only [finsupp.cons, fin.cons, finsupp.tail, fin.tail],
  ext,
  simp only [equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe,
  finsupp.coe_mk, fin.cases_succ, equiv_fun_on_fintype],
  refl,
end

@[simp] lemma cons_tail (s : fin (n + 1) →₀ ℕ) : cons (s 0) (tail s) = s :=
begin
  ext,
  by_cases c_a : a = 0,
  { rw [c_a, cons_zero] },
  { rw [←fin.succ_pred a c_a, cons_succ, ←tail_apply] },
end

@[simp] lemma cons_zero_zero : cons 0 (0 : fin n →₀ ℕ) = 0 :=
begin
  ext,
  by_cases c : a ≠ 0,
  { rw [←fin.succ_pred a c, cons_succ],
    simp },
  { simp only [not_not] at c,
    rw [c, cons_zero 0 0],
    simp },
end

lemma cons_ne_zero_of_left {y : ℕ} {m : fin n →₀ ℕ} (h : y ≠ 0) : cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h1 : cons y m 0 = 0 := by simp [c],
  rw cons_zero at h1,
  cc,
end

lemma cons_ne_zero_of_right {y : ℕ} {m: fin n →₀ ℕ} (h : m ≠ 0) : cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h' : m = 0,
  { ext,
    simp [ ← cons_succ a y m, c] },
  cc,
end

lemma cons_ne_zero_iff {y : ℕ} {m: fin n →₀ ℕ} : cons y m ≠ 0 ↔ y ≠ 0 ∨ m ≠ 0 :=
begin
  apply iff.intro,
  { intro h,
    by_contra c,
    simp only [not_or_distrib, ne.def, not_not] at c,
    simpa [c.1, c.2, cons_zero_zero] using h },
  { intro h,
    cases h,
    { exact cons_ne_zero_of_left h },
    { exact cons_ne_zero_of_right h } },
end

end finsupp

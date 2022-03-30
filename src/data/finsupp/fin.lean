/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import data.fin.tuple
import data.finsupp.basic
/-!
# `cons` and `tail` for maps `fin n →₀ M`

We interpret maps `fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `finsupp.tail` : the tail of a map `fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`data.fin.tuple.basic`.
-/

noncomputable theory

namespace finsupp

variables {M : Type*} [has_zero M] {n : ℕ}

/-- `tail` for maps `fin (n + 1) →₀ M`. See `fin.tail` for more details. -/
def tail (s : fin (n + 1) →₀ M) : fin n →₀ M :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.tail s.to_fun)

/-- `cons` for maps `fin n →₀ M`. See `fin.cons` for more details. -/
def cons (y : M) (s : fin n →₀ M) : fin (n + 1) →₀ M :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.cons y s.to_fun)

lemma tail_apply (s : fin (n + 1) →₀ M) (i : fin n) : tail s i = s i.succ :=
begin
  simp only [tail, equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe],
  congr,
end

@[simp] lemma cons_zero (y : M) (s : fin n →₀ M) : cons y s 0 = y :=
by simp [cons, finsupp.equiv_fun_on_fintype]

@[simp] lemma cons_succ (i : fin n) (y : M) (s : fin n →₀ M) : cons y s i.succ = s i :=
begin

  simp only [finsupp.cons, fin.cons, finsupp.equiv_fun_on_fintype, fin.cases_succ, finsupp.coe_mk],
  refl,
end

@[simp] lemma tail_cons (y : M) (s : fin n →₀ M) : tail (cons y s) = s :=
begin
  simp only [finsupp.cons, fin.cons, finsupp.tail, fin.tail],
  ext,
  simp only [equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe,
  finsupp.coe_mk, fin.cases_succ, equiv_fun_on_fintype],
  refl,
end

@[simp] lemma cons_tail (s : fin (n + 1) →₀ M) : cons (s 0) (tail s) = s :=
begin
  ext,
  by_cases c_a : a = 0,
  { rw [c_a, cons_zero] },
  { rw [←fin.succ_pred a c_a, cons_succ, ←tail_apply] },
end

@[simp] lemma cons_zero_zero : cons 0 (0 : fin n →₀ M) = 0 :=
begin
  ext,
  by_cases c : a ≠ 0,
  { rw [←fin.succ_pred a c, cons_succ],
    simp },
  { simp only [not_not] at c,
    simp [c] },
end

lemma cons_ne_zero_of_left {y : M} {m : fin n →₀ M} (h : y ≠ 0) : cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h1 : cons y m 0 = 0 := by simp [c],
  rw cons_zero at h1,
  cc,
end

lemma cons_ne_zero_of_right {y : M} {m: fin n →₀ M} (h : m ≠ 0) : cons y m ≠ 0 :=
begin
  by_contradiction c,
  have h' : m = 0,
  { ext,
    simp [ ← cons_succ a y m, c] },
  cc,
end

lemma cons_ne_zero_iff {y : M} {m: fin n →₀ M} : cons y m ≠ 0 ↔ y ≠ 0 ∨ m ≠ 0 :=
begin
  apply iff.intro,
  { intro h,
    apply or_iff_not_imp_left.2,
    intro h',
    simp only [not_not] at h',
    by_contra c,
    rw [h', c] at h,
    simpa using h },
  { intro h,
    cases h,
    { exact cons_ne_zero_of_left h },
    { exact cons_ne_zero_of_right h } },
end

end finsupp

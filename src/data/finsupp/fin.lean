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

variables {n : ℕ} (i : fin n) {M : Type*} [has_zero M] (y : M)
  (t : fin (n + 1) →₀ M) (s : fin n →₀ M)


/-- `tail` for maps `fin (n + 1) →₀ M`. See `fin.tail` for more details. -/
def tail (s : fin (n + 1) →₀ M) : fin n →₀ M :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.tail s.to_fun)

/-- `cons` for maps `fin n →₀ M`. See `fin.cons` for more details. -/
def cons (y : M) (s : fin n →₀ M) : fin (n + 1) →₀ M :=
finsupp.equiv_fun_on_fintype.inv_fun (fin.cons y s.to_fun)

lemma tail_apply : tail t i = t i.succ :=
begin
  simp only [tail, equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe],
  congr,
end

@[simp] lemma cons_zero : cons y s 0 = y :=
by simp [cons, finsupp.equiv_fun_on_fintype]

@[simp] lemma cons_succ : cons y s i.succ = s i :=
begin
  simp only [finsupp.cons, fin.cons, finsupp.equiv_fun_on_fintype, fin.cases_succ, finsupp.coe_mk],
  refl,
end

@[simp] lemma tail_cons : tail (cons y s) = s :=
begin
  simp only [finsupp.cons, fin.cons, finsupp.tail, fin.tail],
  ext,
  simp only [equiv_fun_on_fintype_symm_apply_to_fun, equiv.inv_fun_as_coe,
  finsupp.coe_mk, fin.cases_succ, equiv_fun_on_fintype],
  refl,
end

@[simp] lemma cons_tail : cons (t 0) (tail t) = t :=
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

variables {s} {y}

lemma cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 :=
begin
  by_contradiction c,
  have h1 : cons y s 0 = 0 := by simp [c],
  rw cons_zero at h1,
  cc,
end

lemma cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 :=
begin
  by_contradiction c,
  have h' : s = 0,
  { ext,
    simp [ ← cons_succ a y s, c] },
  cc,
end

lemma cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 :=
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

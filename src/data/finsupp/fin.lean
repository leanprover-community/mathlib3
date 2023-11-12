/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import data.finsupp.defs

/-!
# `cons` and `tail` for maps `fin n →₀ M`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
finsupp.equiv_fun_on_finite.symm (fin.tail s)

/-- `cons` for maps `fin n →₀ M`. See `fin.cons` for more details. -/
def cons (y : M) (s : fin n →₀ M) : fin (n + 1) →₀ M :=
finsupp.equiv_fun_on_finite.symm (fin.cons y s : fin (n + 1) → M)

lemma tail_apply : tail t i = t i.succ := rfl

@[simp] lemma cons_zero : cons y s 0 = y := rfl

@[simp] lemma cons_succ : cons y s i.succ = s i := fin.cons_succ _ _ _

@[simp] lemma tail_cons : tail (cons y s) = s :=
ext $ λ k, by simp only [tail_apply, cons_succ]

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
  by_cases c : a = 0,
  { simp [c] },
  { rw [←fin.succ_pred a c, cons_succ],
    simp },
end

variables {s} {y}

lemma cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 :=
begin
  contrapose! h with c,
  rw [←cons_zero y s, c, finsupp.coe_zero, pi.zero_apply],
end

lemma cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 :=
begin
  contrapose! h with c,
  ext,
  simp [ ← cons_succ a y s, c],
end

lemma cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 :=
begin
  refine ⟨λ h, _, λ h, h.cases_on cons_ne_zero_of_left cons_ne_zero_of_right⟩,
  refine imp_iff_not_or.1 (λ h' c, h _),
  rw [h', c, finsupp.cons_zero_zero],
end

end finsupp

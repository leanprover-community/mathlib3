/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
-/
import order.filter.at_top_bot
import algebra.archimedean

/-!
# `at_top` filter and archimedean (semi)rings/fields

In this file we prove that for a linear ordered archimedean semiring `R` and a function `f : α → ℕ`,
the function `coe ∘ f : α → R` tends to `at_top` along a filter `l` if and only if so does `f`.
We also prove that `coe : ℕ → R` tends to `at_top` along `at_top`, as well as version of these
two results for `ℤ` (and a ring `R`) and `ℚ` (and a field `R`).
-/

variables {α R : Type*}

open filter

lemma tendsto_coe_nat_at_top_iff [linear_ordered_semiring R] [archimedean R]
  {f : α → ℕ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, nat.cast_le) exists_nat_ge

lemma tendsto_coe_nat_at_top_at_top [linear_ordered_semiring R] [archimedean R] :
  tendsto (coe : ℕ → R) at_top at_top :=
tendsto_coe_nat_at_top_iff.2 tendsto_id

lemma tendsto_coe_int_at_top_iff [linear_ordered_ring R] [archimedean R]
  {f : α → ℤ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, int.cast_le) $
  assume r, let ⟨n, hn⟩ := exists_nat_ge r in ⟨(n:ℤ), hn⟩

lemma tendsto_coe_int_at_top_at_top [linear_ordered_ring R] [archimedean R] :
  tendsto (coe : ℤ → R) at_top at_top :=
tendsto_coe_int_at_top_iff.2 tendsto_id

lemma tendsto_coe_rat_at_top_iff [linear_ordered_field R] [archimedean R]
  {f : α → ℚ} {l : filter α} :
  tendsto (λ n, (f n : R)) l at_top ↔ tendsto f l at_top :=
tendsto_at_top_embedding (assume a₁ a₂, rat.cast_le) $
  assume r, let ⟨n, hn⟩ := exists_nat_ge r in ⟨(n:ℚ), by assumption_mod_cast⟩

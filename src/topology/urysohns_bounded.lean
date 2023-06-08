/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.urysohns_lemma
import topology.continuous_function.bounded

/-!
# Urysohn's lemma for bounded continuous functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we reformulate Urysohn's lemma `exists_continuous_zero_one_of_closed` in terms of
bounded continuous functions `X →ᵇ ℝ`. These lemmas live in a separate file because
`topology.continuous_function.bounded` imports too many other files.

## Tags

Urysohn's lemma, normal topological space
-/

open_locale bounded_continuous_function
open set function

/-- Urysohns lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
then there exists a continuous function `f : X → ℝ` such that

* `f` equals zero on `s`;
* `f` equals one on `t`;
* `0 ≤ f x ≤ 1` for all `x`.
-/
lemma exists_bounded_zero_one_of_closed {X : Type*} [topological_space X] [normal_space X]
  {s t : set X} (hs : is_closed s) (ht : is_closed t)
  (hd : disjoint s t) :
  ∃ f : X →ᵇ ℝ, eq_on f 0 s ∧ eq_on f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
let ⟨f, hfs, hft, hf⟩ := exists_continuous_zero_one_of_closed hs ht hd
in ⟨⟨f, 1, λ x y, real.dist_le_of_mem_Icc_01 (hf _) (hf _)⟩, hfs, hft, hf⟩

/-- Urysohns lemma: if `s` and `t` are two disjoint closed sets in a normal topological space `X`,
and `a ≤ b` are two real numbers, then there exists a continuous function `f : X → ℝ` such that

* `f` equals `a` on `s`;
* `f` equals `b` on `t`;
* `a ≤ f x ≤ b` for all `x`.
-/
lemma exists_bounded_mem_Icc_of_closed_of_le {X : Type*} [topological_space X] [normal_space X]
  {s t : set X} (hs : is_closed s) (ht : is_closed t) (hd : disjoint s t)
  {a b : ℝ} (hle : a ≤ b) :
  ∃ f : X →ᵇ ℝ, eq_on f (const X a) s ∧ eq_on f (const X b) t ∧ ∀ x, f x ∈ Icc a b :=
let ⟨f, hfs, hft, hf01⟩ := exists_bounded_zero_one_of_closed hs ht hd
in ⟨bounded_continuous_function.const X a + (b - a) • f,
  λ x hx, by simp [hfs hx], λ x hx, by simp [hft hx],
  λ x, ⟨by dsimp; nlinarith [(hf01 x).1], by dsimp; nlinarith [(hf01 x).2]⟩⟩

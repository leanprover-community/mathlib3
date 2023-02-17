/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.fin.vec_notation

/-!
# Monotone finite sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove `simp` lemmas that allow to simplify propositions like `monotone ![a, b, c]`.
-/

open set fin matrix function
variables {α : Type*}

lemma lift_fun_vec_cons {n : ℕ} (r : α → α → Prop) [is_trans α r] {f : fin (n + 1) → α} {a : α} :
  ((<) ⇒ r) (vec_cons a f) (vec_cons a f) ↔ r a (f 0) ∧ ((<) ⇒ r) f f :=
by simp only [lift_fun_iff_succ r, forall_fin_succ, cons_val_succ, cons_val_zero, ← succ_cast_succ,
  cast_succ_zero]

variables [preorder α] {n : ℕ} {f : fin (n + 1) → α} {a : α}

@[simp] lemma strict_mono_vec_cons : strict_mono (vec_cons a f) ↔ a < f 0 ∧ strict_mono f :=
lift_fun_vec_cons (<)

@[simp] lemma monotone_vec_cons : monotone (vec_cons a f) ↔ a ≤ f 0 ∧ monotone f :=
by simpa only [monotone_iff_forall_lt] using @lift_fun_vec_cons α n (≤) _ f a

@[simp] lemma strict_anti_vec_cons : strict_anti (vec_cons a f) ↔ f 0 < a ∧ strict_anti f :=
lift_fun_vec_cons (>)

@[simp] lemma antitone_vec_cons : antitone (vec_cons a f) ↔ f 0 ≤ a ∧ antitone f :=
@monotone_vec_cons αᵒᵈ _ _ _ _

lemma strict_mono.vec_cons (hf : strict_mono f) (ha : a < f 0) :
  strict_mono (vec_cons a f) :=
strict_mono_vec_cons.2 ⟨ha, hf⟩

lemma strict_anti.vec_cons (hf : strict_anti f) (ha : f 0 < a) :
  strict_anti (vec_cons a f) :=
strict_anti_vec_cons.2 ⟨ha, hf⟩

lemma monotone.vec_cons (hf : monotone f) (ha : a ≤ f 0) :
  monotone (vec_cons a f) :=
monotone_vec_cons.2 ⟨ha, hf⟩

lemma antitone.vec_cons (hf : antitone f) (ha : f 0 ≤ a) :
  antitone (vec_cons a f) :=
antitone_vec_cons.2 ⟨ha, hf⟩

example : monotone ![1, 2, 2, 3] := by simp [subsingleton.monotone]

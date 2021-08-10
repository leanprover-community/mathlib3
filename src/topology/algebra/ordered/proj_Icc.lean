/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Patrick Massot
-/
import topology.algebra.ordered.basic
import data.set.intervals.proj_Icc

/-!
# Projection onto a closed interval

In this file we prove that the projection `set.proj_Icc f a b h` is a quotient map, and use it
to show that `Icc_extend h f` is continuous if and only if `f` is continuous.
-/

variables {α β : Type*} [topological_space α] [linear_order α] [order_topology α]
  [topological_space β] {a b : α} {h : a ≤ b}

open set

@[continuity]
lemma continuous_proj_Icc : continuous (proj_Icc a b h) :=
continuous_subtype_mk _ $ continuous_const.max $ continuous_const.min continuous_id

lemma quotient_map_proj_Icc : quotient_map (proj_Icc a b h) :=
quotient_map_iff.2 ⟨proj_Icc_surjective h, λ s,
  ⟨λ hs, hs.preimage continuous_proj_Icc,
   λ hs, ⟨_, hs, by { ext, simp }⟩⟩⟩

@[simp] lemma continuous_Icc_extend_iff {f : Icc a b → β} :
  continuous (Icc_extend h f) ↔ continuous f :=
quotient_map_proj_Icc.continuous_iff.symm

@[continuity]
lemma continuous.Icc_extend {f : Icc a b → β} (hf : continuous f) :
  continuous (Icc_extend h f) :=
hf.comp continuous_proj_Icc

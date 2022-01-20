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

open set filter
open_locale filter topological_space

variables {α β γ : Type*} [linear_order α] [topological_space γ] {a b c : α} {h : a ≤ b}

lemma filter.tendsto.Icc_extend (f : γ → Icc a b → β) {z : γ} {l : filter α} {l' : filter β}
  (hf : tendsto ↿f (𝓝 z ×ᶠ l.map (proj_Icc a b h)) l') :
  tendsto ↿(Icc_extend h ∘ f) (𝓝 z ×ᶠ l) l' :=
show tendsto (↿f ∘ prod.map id (proj_Icc a b h)) (𝓝 z ×ᶠ l) l', from
hf.comp $ tendsto_id.prod_map tendsto_map

variables [topological_space α] [order_topology α] [topological_space β]

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

/-- See Note [continuity lemma statement]. -/
lemma continuous.Icc_extend {f : γ → Icc a b → β} {g : γ → α}
  (hf : continuous ↿f) (hg : continuous g) : continuous (λ a, Icc_extend h (f a) (g a)) :=
hf.comp $ continuous_id.prod_mk $ continuous_proj_Icc.comp hg

/-- A useful special case of `continuous.Icc_extend`. -/
@[continuity]
lemma continuous.Icc_extend' {f : Icc a b → β} (hf : continuous f) : continuous (Icc_extend h f) :=
hf.comp continuous_proj_Icc

lemma continuous_at.Icc_extend {x : γ} (f : γ → Icc a b → β) {g : γ → α}
  (hf : continuous_at ↿f (x, proj_Icc a b h (g x))) (hg : continuous_at g x) :
  continuous_at (λ a, Icc_extend h (f a) (g a)) x :=
show continuous_at (↿f ∘ λ x, (x, proj_Icc a b h (g x))) x, from
continuous_at.comp hf $ continuous_at_id.prod $ continuous_proj_Icc.continuous_at.comp hg

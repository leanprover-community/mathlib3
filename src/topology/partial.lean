/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import topology.continuous_on
import order.filter.partial

/-!
# Partial functions and topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove properties of `filter.ptendsto` etc in topological spaces. We also introduce
`pcontinuous`, a version of `continuous` for partially defined functions.
-/

open filter
open_locale topology

variables {α β : Type*} [topological_space α]

theorem rtendsto_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto r l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → r.core s ∈ l) :=
all_mem_nhds_filter _ _ (λ s t, id) _

theorem rtendsto'_nhds {r : rel β α} {l : filter β} {a : α} :
  rtendsto' r l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → r.preimage s ∈ l) :=
by { rw [rtendsto'_def], apply all_mem_nhds_filter, apply rel.preimage_mono }

theorem ptendsto_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f.core s ∈ l) :=
rtendsto_nhds

theorem ptendsto'_nhds {f : β →. α} {l : filter β} {a : α} :
  ptendsto' f l (𝓝 a) ↔ (∀ s, is_open s → a ∈ s → f.preimage s ∈ l) :=
rtendsto'_nhds

/-! ### Continuity and partial functions -/

variable [topological_space β]

/-- Continuity of a partial function -/
def pcontinuous (f : α →. β) := ∀ s, is_open s → is_open (f.preimage s)

lemma open_dom_of_pcontinuous {f : α →. β} (h : pcontinuous f) : is_open f.dom :=
by rw [←pfun.preimage_univ]; exact h _ is_open_univ

lemma pcontinuous_iff' {f : α →. β} :
  pcontinuous f ↔ ∀ {x y} (h : y ∈ f x), ptendsto' f (𝓝 x) (𝓝 y) :=
begin
  split,
  { intros h x y h',
    simp only [ptendsto'_def, mem_nhds_iff],
    rintros s ⟨t, tsubs, opent, yt⟩,
    exact ⟨f.preimage t, pfun.preimage_mono _ tsubs, h _ opent, ⟨y, yt, h'⟩⟩ },
  intros hf s os,
  rw is_open_iff_nhds,
  rintros x ⟨y, ys, fxy⟩ t,
  rw [mem_principal],
  assume h : f.preimage s ⊆ t,
  change t ∈ 𝓝 x,
  apply mem_of_superset _ h,
  have h' : ∀ s ∈ 𝓝 y, f.preimage s ∈ 𝓝 x,
  { intros s hs,
     have : ptendsto' f (𝓝 x) (𝓝 y) := hf fxy,
     rw ptendsto'_def at this,
     exact this s hs },
  show f.preimage s ∈ 𝓝 x,
  apply h', rw mem_nhds_iff, exact ⟨s, set.subset.refl _, os, ys⟩
end

theorem continuous_within_at_iff_ptendsto_res (f : α → β) {x : α} {s : set α} :
  continuous_within_at f s x ↔ ptendsto (pfun.res f s) (𝓝 x) (𝓝 (f x)) :=
tendsto_iff_ptendsto _ _ _ _

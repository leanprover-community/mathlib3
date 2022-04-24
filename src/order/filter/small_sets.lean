/-
Copyright (c) 2022 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Floris van Doorn
-/
import order.filter.lift

/-!
# The filter of small sets

This file defines the filter of small sets w.r.t. a filter `f`, which is the largest filter
containing all powersets of members of `f`.

`g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`.

An example usage is that if `f : ι → ℝ` is a family of nonnegative functions with integral 1, then
saying that `f` tendsto `(𝓝 0).small_sets` is a way of saying that `f` tends to the Dirac delta
distribution.
-/

open_locale filter
open filter set

variables {α β : Type*} {ι : Sort*}

namespace filter

/-- The filter `f.small_sets` is the largest filter containing all powersets of members of `f`. -/
def small_sets (f : filter α) : filter (set α) := f.lift' powerset

lemma small_sets_eq_generate {f : filter α} : f.small_sets = generate (powerset '' f.sets) :=
by { simp_rw [generate_eq_binfi, small_sets, infi_image], refl }

lemma has_basis.small_sets {f : filter α} {p : ι → Prop} {s : ι → set α}
  (h : has_basis f p s) : has_basis f.small_sets p (λ i, 𝒫 (s i)) :=
h.lift' monotone_powerset

lemma has_basis_small_sets (f : filter α) :
  has_basis f.small_sets (λ t : set α, t ∈ f) powerset :=
f.basis_sets.small_sets

/-- `g` converges to `f.small_sets` if for all `s ∈ f`, eventually we have `g x ⊆ s`. -/
lemma tendsto_small_sets_iff {la : filter α} {lb : filter β} {f : α → set β} :
  tendsto f la lb.small_sets ↔ ∀ t ∈ lb, ∀ᶠ x in la, f x ⊆ t :=
(has_basis_small_sets lb).tendsto_right_iff

end filter

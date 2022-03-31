/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.local_homeomorph

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

* `is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `is_locally_homeomorph` is a global condition. This is in contrast to
  `local_homeomorph`, which is a homeomorphism between specific open subsets.
-/

open_locale topological_space

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (g : Y → Z) (f : X →  Y)

/-- A function `f : X → Y` satisfies `is_locally_homeomorph` if each `x : x` is contained in
  the source of some `e : local_homeomorph X Y` with `f = e`. -/
def is_locally_homeomorph :=
∀ x : X, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ f = e

namespace is_locally_homeomorph

/-- Proves that `f` satisfies `is_locally_homeomorph`. The condition `h` is weaker than definition
of `is_locally_homeomorph`, since it only requires `e : local_homeomorph X Y` to agree with `f` on
its source `e.source`, as opposed to on the whole space `X`. -/
lemma mk (h : ∀ x : X, ∃ e : local_homeomorph X Y, x ∈ e.source ∧ ∀ x, x ∈ e.source → f x = e x) :
  is_locally_homeomorph f :=
begin
  intro x,
  obtain ⟨e, hx, he⟩ := h x,
  exact ⟨{ to_fun := f,
    map_source' := λ x hx, by rw he x hx; exact e.map_source' hx,
    left_inv' := λ x hx, by rw he x hx; exact e.left_inv' hx,
    right_inv' := λ y hy, by rw he _ (e.map_target' hy); exact e.right_inv' hy,
    continuous_to_fun := (continuous_on_congr he).mpr e.continuous_to_fun,
    .. e }, hx, rfl⟩,
end

variables {g f}

lemma map_nhds_eq (hf : is_locally_homeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) :=
begin
  obtain ⟨e, hx, rfl⟩ := hf x,
  exact e.map_nhds_eq hx,
end

protected lemma continuous (hf : is_locally_homeomorph f) : continuous f :=
continuous_iff_continuous_at.mpr (λ x, le_of_eq (hf.map_nhds_eq x))

lemma is_open_map (hf : is_locally_homeomorph f) : is_open_map f :=
is_open_map.of_nhds_le (λ x, ge_of_eq (hf.map_nhds_eq x))

protected lemma comp (hg : is_locally_homeomorph g) (hf : is_locally_homeomorph f) :
  is_locally_homeomorph (g ∘ f) :=
begin
  intro x,
  obtain ⟨eg, hxg, rfl⟩ := hg (f x),
  obtain ⟨ef, hxf, rfl⟩ := hf x,
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩,
end

end is_locally_homeomorph

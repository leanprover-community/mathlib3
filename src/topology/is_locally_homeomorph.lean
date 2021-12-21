
/-
Copyright (c) 2019 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import topology.local_homeomorph

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

`is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if it is
locally a homeomorphism.
-/

variables {X Y Z : Type*} [topological_space X] [topological_space Y] [topological_space Z]
  (g : Y → Z) (f : X →  Y)

def is_locally_homeomorph :=
∀ x : X, ∃ e : local_homeomorph X Y, f = e ∧ x ∈ e.source

namespace is_locally_homeomorph

variables {g f}

lemma continuous (hf : is_locally_homeomorph f) : continuous f :=
begin
  refine continuous_iff_continuous_at.mpr (λ x, _),
  obtain ⟨e, rfl, hx⟩ := hf x,
  exact e.continuous_at hx,
end

lemma comp (hg : is_locally_homeomorph g) (hf : is_locally_homeomorph f) :
  is_locally_homeomorph (g ∘ f) :=
begin
  intro x,
  obtain ⟨eg, rfl, hxg⟩ := hg (f x),
  obtain ⟨ef, rfl, hxf⟩ := hf x,
  exact ⟨ef.trans eg, rfl, hxf, hxg⟩,
end

lemma is_open_map (hf : is_locally_homeomorph f) : is_open_map f :=
begin
  refine is_open_map.of_nhds_le (forall_imp _ hf),
  rintros x ⟨e, rfl, hx⟩,
  exact ge_of_eq (e.map_nhds_eq hx),
end

end is_locally_homeomorph

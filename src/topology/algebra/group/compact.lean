/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.algebra.group.basic
import topology.compact_open
import topology.sets.compacts

/-!
# Additional results on topological groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Two results on topological groups that have been separated out as they require more substantial
imports developing either positive compacts or the compact open topology.

-/

open classical set filter topological_space function
open_locale classical topology filter pointwise

universes u v w x
variables {α : Type u} {β : Type v} {G : Type w} {H : Type x}

section

/-! Some results about an open set containing the product of two sets in a topological group. -/

variables [topological_space G] [group G] [topological_group G]

/-- Every separated topological group in which there exists a compact set with nonempty interior
is locally compact. -/
@[to_additive "Every separated topological group in which there exists a compact set with nonempty
interior is locally compact."]
lemma topological_space.positive_compacts.locally_compact_space_of_group
  [t2_space G] (K : positive_compacts G) :
  locally_compact_space G :=
begin
  refine locally_compact_of_compact_nhds (λ x, _),
  obtain ⟨y, hy⟩ := K.interior_nonempty,
  let F := homeomorph.mul_left (x * y⁻¹),
  refine ⟨F '' K, _, K.is_compact.image F.continuous⟩,
  suffices : F.symm ⁻¹' K ∈ 𝓝 x, by { convert this, apply equiv.image_eq_preimage },
  apply continuous_at.preimage_mem_nhds F.symm.continuous.continuous_at,
  have : F.symm x = y, by simp [F, homeomorph.mul_left_symm],
  rw this,
  exact mem_interior_iff_mem_nhds.1 hy
end

end

section quotient
variables [group G] [topological_space G] [topological_group G] {Γ : subgroup G}

@[to_additive]
instance quotient_group.has_continuous_smul [locally_compact_space G] :
  has_continuous_smul G (G ⧸ Γ) :=
{ continuous_smul := begin
    let F : G × G ⧸ Γ → G ⧸ Γ := λ p, p.1 • p.2,
    change continuous F,
    have H : continuous (F ∘ (λ p : G × G, (p.1, quotient_group.mk p.2))),
    { change continuous (λ p : G × G, quotient_group.mk (p.1 * p.2)),
      refine continuous_coinduced_rng.comp continuous_mul },
    exact quotient_map.continuous_lift_prod_right quotient_map_quotient_mk H,
  end }

end quotient

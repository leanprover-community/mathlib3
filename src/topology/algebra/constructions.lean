/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import topology.homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define `topological_space` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `has_continuous_mul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/

variables {M X : Type*}

open filter
open_locale topology

namespace mul_opposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive "Put the same topological space structure on the opposite monoid as on the original
space."]
instance [topological_space M] : topological_space Mᵐᵒᵖ :=
topological_space.induced (unop : Mᵐᵒᵖ → M) ‹_›

variables [topological_space M]

@[continuity, to_additive] lemma continuous_unop : continuous (unop : Mᵐᵒᵖ → M) :=
continuous_induced_dom

@[continuity, to_additive] lemma continuous_op : continuous (op : M → Mᵐᵒᵖ) :=
continuous_induced_rng.2 continuous_id

/-- `mul_opposite.op` as a homeomorphism. -/
@[to_additive "`add_opposite.op` as a homeomorphism.", simps]
def op_homeomorph : M ≃ₜ Mᵐᵒᵖ :=
{ to_equiv := op_equiv,
  continuous_to_fun := continuous_op,
  continuous_inv_fun := continuous_unop }

@[to_additive] instance [t2_space M] : t2_space Mᵐᵒᵖ :=
op_homeomorph.symm.embedding.t2_space

@[simp, to_additive] lemma map_op_nhds (x : M) : map (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (op x) :=
op_homeomorph.map_nhds_eq x

@[simp, to_additive] lemma map_unop_nhds (x : Mᵐᵒᵖ) : map (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (unop x) :=
op_homeomorph.symm.map_nhds_eq x

@[simp, to_additive] lemma comap_op_nhds (x : Mᵐᵒᵖ) : comap (op : M → Mᵐᵒᵖ) (𝓝 x) = 𝓝 (unop x) :=
op_homeomorph.comap_nhds_eq x

@[simp, to_additive] lemma comap_unop_nhds (x : M) : comap (unop : Mᵐᵒᵖ → M) (𝓝 x) = 𝓝 (op x) :=
op_homeomorph.symm.comap_nhds_eq x

end mul_opposite

namespace units

open mul_opposite

variables [topological_space M] [monoid M] [topological_space X]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive "The additive units of a monoid are equipped with a topology, via the embedding into
`M × M`."]
instance : topological_space Mˣ := prod.topological_space.induced (embed_product M)

@[to_additive] lemma inducing_embed_product : inducing (embed_product M) := ⟨rfl⟩

@[to_additive] lemma embedding_embed_product : embedding (embed_product M) :=
⟨inducing_embed_product, embed_product_injective M⟩

@[to_additive] lemma topology_eq_inf :
  units.topological_space = topological_space.induced (coe : Mˣ → M) ‹_› ⊓
    topological_space.induced (λ u, ↑u⁻¹ : Mˣ → M) ‹_› :=
by simp only [inducing_embed_product.1, prod.topological_space, induced_inf,
  mul_opposite.topological_space, induced_compose]; refl

/-- An auxiliary lemma that can be used to prove that coercion `Mˣ → M` is a topological embedding.
Use `units.coe_embedding₀`, `units.coe_embedding`, or `to_units_homeomorph` instead. -/
@[to_additive "An auxiliary lemma that can be used to prove that coercion `add_units M → M` is a
topological embedding. Use `add_units.coe_embedding` or `to_add_units_homeomorph` instead."]
lemma embedding_coe_mk {M : Type*} [division_monoid M] [topological_space M]
  (h : continuous_on has_inv.inv {x : M | is_unit x}) : embedding (coe : Mˣ → M) :=
begin
  refine ⟨⟨_⟩, ext⟩,
  rw [topology_eq_inf, inf_eq_left, ← continuous_iff_le_induced, continuous_iff_continuous_at],
  intros u s hs,
  simp only [coe_inv, nhds_induced, filter.mem_map] at hs ⊢,
  exact ⟨_, mem_inf_principal.1 (h u u.is_unit hs), λ u' hu', hu' u'.is_unit⟩
end

@[to_additive] lemma continuous_embed_product : continuous (embed_product M) :=
continuous_induced_dom

@[to_additive] lemma continuous_coe : continuous (coe : Mˣ → M) :=
(@continuous_embed_product M _ _).fst

@[to_additive] protected lemma continuous_iff {f : X → Mˣ} :
  continuous f ↔ continuous (coe ∘ f : X → M) ∧ continuous (λ x, ↑(f x)⁻¹ : X → M) :=
by simp only [inducing_embed_product.continuous_iff, embed_product_apply, (∘), continuous_prod_mk,
  op_homeomorph.symm.inducing.continuous_iff, op_homeomorph_symm_apply, unop_op]

@[to_additive] lemma continuous_coe_inv : continuous (λ u, ↑u⁻¹ : Mˣ → M) :=
(units.continuous_iff.1 continuous_id).2

end units

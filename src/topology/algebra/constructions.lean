/-
Copyright (c) 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import topology.homeomorph

/-!
# Topological space structure on the opposite monoid and on the units group

In this file we define `topological_space` structure on `Mᵐᵒᵖ`, `Mᵃᵒᵖ`, `Mˣ`, and `add_units M`.
This file does not import definitions of a topological monoid and/or a continuous multiplicative
action, so we postpone the proofs of `has_continuous_mul Mᵐᵒᵖ` etc till we have these definitions.

## Tags

topological space, opposite monoid, units
-/

variables {M X : Type*}

open filter
open_locale topological_space

namespace mul_opposite

/-- Put the same topological space structure on the opposite monoid as on the original space. -/
@[to_additive] instance [topological_space M] : topological_space Mᵐᵒᵖ :=
topological_space.induced (unop : Mᵐᵒᵖ → M) ‹_›

variables [topological_space M]

@[continuity, to_additive] lemma continuous_unop : continuous (unop : Mᵐᵒᵖ → M) :=
continuous_induced_dom

@[continuity, to_additive] lemma continuous_op : continuous (op : M → Mᵐᵒᵖ) :=
continuous_induced_rng continuous_id

/-- `mul_opposite.op` as a homeomorphism. -/
@[to_additive "`add_opposite.op` as a homeomorphism."]
def op_homeomorph : M ≃ₜ Mᵐᵒᵖ :=
{ to_equiv := op_equiv,
  continuous_to_fun := continuous_op,
  continuous_inv_fun := continuous_unop }

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

variables [topological_space M] [monoid M]

/-- The units of a monoid are equipped with a topology, via the embedding into `M × M`. -/
@[to_additive] instance : topological_space Mˣ :=
topological_space.induced (embed_product M) prod.topological_space

@[to_additive] lemma continuous_embed_product : continuous (embed_product M) :=
continuous_induced_dom

@[to_additive] lemma continuous_coe : continuous (coe : Mˣ → M) :=
(@continuous_embed_product M _ _).fst

end units

import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import combinatorics.simple_graph.prod
import .mathlib
import .reachable_outside
import .ends

open function
open finset
open set
open classical
open simple_graph.walk
open relation

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)
           {V' : Type v}
           (G' : simple_graph V')
           {V'' : Type w}
           (G'' : simple_graph V'')

namespace ends

open ro_component
open simple_graph

lemma ends_product [Vnempty : nonempty V] [Vnempty' : nonempty V']
  [locally_finite G] [locally_finite G']
  (Gpc :G.preconnected) (Gpc' : G'.preconnected)
  (Vinf : set.infinite (@set.univ V)) (V'inf : set.infinite (@set.univ V'))
: ends  (box_prod G  G') (simple_graph.preconnected.box_prod Gpc Gpc') ≃ true :=
begin

  let VV := V × V',
  let GG := G □ G',
  let GGpc := simple_graph.preconnected.box_prod Gpc Gpc',
  haveI : locally_finite GG, by sorry,
  haveI all_fin : ∀ K : finset VV, fintype (inf_ro_components GG K), from
     λ K, inf_components_finite' GG GGpc K,
  suffices : ∀ K : finset VV, (inf_ro_components GG K) ≃ true,
  {
    have all_inj : ∀ (K L : finset VV) (KL : K ⊆ L), injective (bwd_map GG GGpc KL), by
    { rintros K L KL,
      sorry, -- we have true ≃ inf_ro_components GG L → inf_ro_components GG K ≃ true
      -- this composes to a surjection, since all functions are, and thus to an injection, because
      -- all maps true -> true are injection, thus bwd is also an injection.
    },
    have lol := eval_bijective GG GGpc ∅ (λ L hL, all_inj ∅ L hL),
    exact (equiv.of_bijective _ lol).trans (this ∅),
  },
  rintros K,
  -- Thta's not the correct construction: we want to take a box containing K
  let L := (finset.image prod.fst K) × (finset.image prod.snd K),
  /-
  Then we show that VV \ L is subconnected (our terminology), hence contained in some infinite connected component.
  Since L is finite, there can be no other infinite connected component than this one, and we construct the bijection with true.
  -/
  sorry,
end
-- just want to say the cardinality is 1

end ends

end simple_graph

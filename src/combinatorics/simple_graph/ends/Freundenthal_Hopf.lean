import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
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


namespace ends

open ro_component

variables  {V : Type u}
           (G : simple_graph V)


/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_bwd_map_not_inj [locally_finite G] (Gpc : G.preconnected)
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V) (Knempty : K.nonempty)
  (inf_comp_K_large : @fintype.card (inf_ro_components G K) (ro_component.inf_components_finite G Gpc K) ≥ 3) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),  ¬ injective (bwd_map G Gpc ‹K' ⊆ L›) :=
begin
  rcases extend_to_subconnected G Gpc K (nonempty.intro Knempty.some) with ⟨Kp,KKp,Kpconn⟩ ,
  rcases extend_subconnected_to_fin_ro_components G Gpc Kp (finset.nonempty.mono KKp Knempty) Kpconn  with ⟨K',KK',K'conn,finn⟩,
  rcases auts K' with ⟨φ,φgood⟩,

  let φK' := finset.image φ K',
  let K'nempty := finset.nonempty.mono (KKp.trans KK') Knempty,
  let φK'nempty := finset.nonempty.image K'nempty φ,
  let L := K' ∪ φK',
  use [K',L,KKp.trans KK',finset.subset_union_left  K' (φK')],


  have φK'conn : subconnected G φK' := begin
    have := simple_graph.subconnected.image G G φ K'conn,
    simp only [coe_coe, rel_embedding.coe_coe_fn, rel_iso.coe_coe_fn, coe_image] at this,
    simp only [coe_image],
    exact this,
  end,


  rcases of_subconnected_disjoint G K' φK' φK'nempty (finset.disjoint_coe.mpr φgood.symm) φK'conn with ⟨E,Ecomp,Esub⟩,
  rcases of_subconnected_disjoint G φK' K' K'nempty (finset.disjoint_coe.mpr φgood) K'conn with ⟨F,Fcomp,Fsub⟩,

  have Einf : E.infinite := finn ⟨E,Ecomp⟩,
  have Finf : F.infinite, by {
    rcases  ro_component.bij_ro_components_of_isom G G K' φ with ⟨mapsto,inj,sur⟩,
    rcases sur Fcomp with ⟨F₀,F₀comp,rfl⟩,
    let F₀inf := finn ⟨F₀,F₀comp⟩,
    rcases ro_component.bij_inf_ro_components_of_isom G G K' φ with ⟨infmapsto,_,_⟩,
    exact (infmapsto ⟨F₀comp,F₀inf⟩).2,
},

  apply @nicely_arranged_bwd_map_not_inj V G Gpc _ φK' K' (φK'nempty) (K'nempty) ⟨F,Fcomp,Finf⟩ _ ⟨E,Ecomp,Einf⟩ Esub Fsub,

  have := (bij_inf_ro_components_of_isom G G K' φ).bijective,
  --fintype.card_of_bijective
  have lol := @fintype.of_bijective _ _ (ro_component.inf_components_finite G Gpc K')  _ this,
  have lol2 := @fintype.card_of_bijective _ _ (ro_component.inf_components_finite G Gpc K') lol _ this,
  -- confusion :
  sorry,
end


lemma Freudenthal_Hopf [locally_finite G] (Gpc: G.preconnected) [nonempty V]
  [fintype (ends G Gpc)]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K)) :
  (fintype.card (ends G Gpc)) ≤ 2 :=
begin


  by_contradiction h,
  have many_ends : 3 ≤ (fintype.card (ends G Gpc)) := (nat.succ_le_iff.mpr (not_le.mp h)),
  rcases finite_ends_to_inj G Gpc with ⟨K,Knempty,Kinj⟩,

  haveI : fintype ↥(inf_ro_components G K), from ro_component.inf_components_finite G Gpc K,

  have : 3 ≤ fintype.card ↥(inf_ro_components G K), by {
    have := fintype.card_le_of_injective (eval G Gpc K) (eval_injective G Gpc K Kinj),
    exact many_ends.trans this,
  },

  rcases (good_autom_bwd_map_not_inj G Gpc auts K Knempty this.ge) with ⟨K',L,hK',hL,bwd_K_not_inj⟩,

  have : injective (bwd_map G hL) := by {
    let llo := Kinj  L (hK'.trans hL),
    rw ((bwd_map_comp G hK' hL).symm) at llo,
    exact injective.of_comp llo,
  },
  exact bwd_K_not_inj this,
end

end ends

end simple_graph

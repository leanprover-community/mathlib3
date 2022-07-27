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
           --[preconnected G]
           --[locally_finite G]
           [decidable_eq V]

/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_bwd_map_not_inj [locally_finite G] [G.preconnected]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V) (Knempty : K.nonempty)
  (inf_comp_K_large : @fintype.card (inf_ro_components G K) (sorry) ≥ 3) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),  ¬ injective (bwd_map G ‹K' ⊆ L›) :=
begin
  rcases @extend_to_subconnected V G K (sorry) (sorry) (nonempty.intro Knempty.some) with ⟨Kp,KKp,Kpconn⟩ ,
  rcases @extend_subconnected_to_fin_ro_components V G Kp (sorry) (finset.nonempty.mono KKp Knempty) Kpconn  with ⟨K',KK',K'conn,finn⟩,
  rcases auts K' with ⟨φ,φgood⟩,

  let φK' := finset.image φ K',
  let K'nempty := finset.nonempty.mono (KKp.trans KK') Knempty,
  let φK'nempty := finset.nonempty.image K'nempty φ,
  let L := K' ∪ φK',
  use [K',L,KKp.trans KK',finset.subset_union_left  K' (φK')],



  -- Why doesn't this work!!!
  --have φK'conn := simple_graph.subconnected.image G G φ K'conn,
  have φK'conn : subconnected G φK' := sorry,


  rcases ro_of_subconnected_disjoint G K' φK' (finset.disjoint_coe.mpr φgood.symm) φK'conn with ⟨E,Ecomp,Esub⟩,
  rcases ro_of_subconnected_disjoint G φK' K' (finset.disjoint_coe.mpr φgood) K'conn with ⟨F,Fcomp,Fsub⟩,

  have Einf : E.infinite := finn ⟨E,Ecomp⟩,
  have Finf : F.infinite, by {
    rcases  @component.bij_components_of_autom V G _ _ (sorry) K' φ with ⟨mapsto,inj,sur⟩,
    rcases sur Fcomp with ⟨F₀,F₀comp,rfl⟩,
    let F₀inf := finn ⟨F₀,F₀comp⟩,
    rcases @bij_inf_components_of_autom V G _ _ (sorry) K' φ with ⟨infmapsto,_,_⟩,
    let lol := infmapsto ⟨F₀comp,F₀inf⟩,
    simp at lol,
    simp,
    sorry, -- almost done but had to go
  },

  apply nicely_arranged_bwd_map_not_inj G φK' K' (φK'nempty) (K'nempty) ⟨F,Fcomp,Finf⟩ _ ⟨E,Ecomp,Einf⟩ Esub Fsub,

  have := @bij_inf_components_of_autom V G _ _ (sorry) K' φ,


  sorry,
end


lemma Freudenthal_Hopf [locally_finite G] [G.preconnected]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  [fintype (ends G)] : (fintype.card (ends G)) ≤ 2 :=
begin
  by_contradiction h,
  have many_ends : 3 ≤ (fintype.card (ends G)) := (nat.succ_le_iff.mpr (not_le.mp h)),
  rcases @finite_ends_to_inj V G _ (sorry) _ _ (sorry) with ⟨K,Knempty,Kinj⟩,

  have : 3 ≤ @fintype.card ↥(inf_ro_components G K) (sorry), by {
    have := @fintype.card_le_of_injective _ _ _ (sorry) (eval G K) (eval_injective G K Kinj),
    exact many_ends.trans this,
  },

  rcases (@good_autom_bwd_map_not_inj V G _ _ (sorry) auts K Knempty this) with ⟨K',L,hK',hL,bwd_K_not_inj⟩,

  have : injective (bwd_map G hL) := by {
    let llo := Kinj  L (hK'.trans hL),
    rw ((bwd_map_comp G hK' hL).symm) at llo,
    exact injective.of_comp llo,
  },
  exact bwd_K_not_inj this,
end

end ends

end simple_graph

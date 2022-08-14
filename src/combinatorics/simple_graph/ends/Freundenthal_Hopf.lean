import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import .mathlib
import .reachable_outside
import .bwd_map
import .end_limit_construction
import .mathlib_fintype_inverse_systems


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
open bwd_map

variables  {V : Type u}
           (G : simple_graph V)


/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_bwd_map_not_inj [locally_finite G]  (Gpc : G.preconnected)
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V)
  (inf_comp_H_large : fin 3 ↪ (inf_ro_components' G K)) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),  ¬ injective (bwd_map_inf G Gpc ‹K' ⊆ L›) :=
begin

  by_cases Knempty : K.nonempty,
  { rcases extend_to_subconnected G Gpc K (nonempty.intro Knempty.some) with ⟨Kp,KKp,Kpconn⟩ ,
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
      exact (infmapsto ⟨F₀comp,F₀inf⟩).2,},

    apply nicely_arranged_bwd_map_not_inj G Gpc φK' K' (φK'nempty) (K'nempty) ⟨⟨F,Fcomp⟩,Finf⟩ _ ⟨⟨E,Ecomp⟩,Einf⟩ Esub Fsub,
    have := (inf_ro_components_equiv_of_isom' G G K' φ),
    apply inf_comp_H_large.trans,
    refine function.embedding.trans _ (inf_ro_components_equiv_of_isom' G G K' φ).to_embedding,
    apply function.embedding.of_surjective,
    exact bwd_map_inf.surjective G Gpc (KKp.trans KK'),},
  { rw finset.not_nonempty_iff_eq_empty at Knempty,
    sorry, -- Need a lemma saying that the connected components for K=∅ are just {V} when G is connected
    -- or even better a general statement holding when G is disconnected.
    -- in any case, here we know that we have at least 3 components, which is a contradiction.
    -- Probably the proof here shouldn't be done by cases, but Knempty argued from the assumptions.
  }

end


lemma Freudenthal_Hopf [locally_finite G] (Gpc: G.preconnected)
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K)) :
  (fin 3 ↪ Endsinfty G Gpc) → (Endsinfty G Gpc).infinite :=
begin

  intro many_ends,
  intro finite_ends,

  have Vinf : (@set.univ V).infinite := sorry, -- from the assumption that at least three ends
  haveI : fintype (ComplInfComp G Gpc).sections := finite.fintype finite_ends,
  haveI : Π (j : finset V), fintype ((ComplInfComp G Gpc).obj j) := ComplInfComp_fintype G Gpc,
  --haveI : Π (j : finset V), nonempty ((ComplInfComp G Gpc).obj j) := ComplInfComp_nonempty G Gpc Vinf,
  have surj : inverse_system.is_surjective (ComplInfComp G Gpc) := ComplInfComp.surjective G Gpc,

  obtain ⟨K,top⟩ := inverse_system.sections_fintype_to_injective (ComplInfComp G Gpc) surj,
  let inj' := inverse_system.sections_injective (ComplInfComp G Gpc) K top,

  rcases (good_autom_bwd_map_not_inj G Gpc auts K (many_ends.trans ⟨_,inj'⟩)) with ⟨K',L,KK',K'L,bwd_K_not_inj⟩,
  apply bwd_K_not_inj,
  -- The following is just that if f ∘ g is injective, then so is g
  rintro x y eq,
  apply top ⟨L,by {exact KK'.trans K'L,}⟩,
  have eq' := congr_arg (bwd_map_inf G Gpc KK') eq,
  simp only [bwd_map_inf.comp'] at eq', exact eq',
end

end ends

end simple_graph

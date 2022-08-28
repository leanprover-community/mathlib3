import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import .mathlib
import .comp_out
import .mathlib_fintype_inverse_systems
import .end_limit_construction


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


/-
  This is the key part of Hopf-Freudenthal
  Assuming this is proved:
  As long as K has at least three infinite connected components, then so does K', and
  bwd_map ‹K'⊆L› is not injective, hence the graph has more than three ends.
-/
lemma good_autom_bwd_map_not_inj [locally_finite G]  (Gpc : G.preconnected)
  (auts : ∀ K : finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K))
  (K : finset V)
  (inf_comp_H_large : fin 3 ↪ (G.inf_comp_out K)) :
  ∃ (K' L : finset V) (hK' : K ⊆ K') (hL : K' ⊆ L),
    ¬ injective (inf_comp_out.back ‹↑K' ⊆ ↑L› : G.inf_comp_out L → G.inf_comp_out K') :=
begin
  have Knempty : K.nonempty, by sorry,
  /-{ rw nonempty_iff_ne_empty,
    by_contradiction h, rw h at inf_comp_H_large,
    have e : fin 3 ↪ (G.dis_comp_out (∅ : finset V)), by
    { apply inf_comp_H_large.trans,
      fconstructor,
      exact subtype.val, exact subtype.val_injective,},
    haveI := conn_comp_outside.of_empty_is_subsingleton Gpc,
    have := e.inj' (subsingleton.elim (e 0) (e 1)),
    finish,},-/
  obtain ⟨Kp,⟨KKp,Kpconn⟩⟩ := conn_comp_outside.extend_to_connected G K Knempty,
  rcases conn_comp_outside.extend_connected_with_fin_components G Kp Kpconn  with ⟨K',KK',K'conn,finn⟩,
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
  exact inf_conn_comp_outside_back.surjective G Gpc (KKp.trans KK'),


end


lemma Freudenthal_Hopf [locally_finite G] [Gpc : G.preconnected]
  (auts : ∀ K :finset V, ∃ φ : G ≃g G, disjoint K (finset.image φ K)) :
  (fin 3 ↪ Endsinfty G) → (Endsinfty G).infinite :=
begin

  -- Assume we have at least three ends, but finitely many
  intros many_ends finite_ends,

  -- Boring boilerplate
  --have Vinf : (@set.univ V).infinite := sorry, -- from the assumption that at least three ends
  haveI : fintype (ComplInfComp G).sections := finite.fintype finite_ends,
  haveI : Π (j : finset V), fintype ((ComplInfComp G).obj j) := @ComplInfComp_fintype V _ G _ Gpc,
  have surj : inverse_system.is_surjective (ComplInfComp G) := ComplInfComp.surjective G,

  -- By finitely many ends, and since the system is nice, there is some K such that each inf_conn_comp_outside_back to K is injective
  obtain ⟨K,top⟩ := inverse_system.sections_fintype_to_injective (ComplInfComp G) surj,
  -- Since each inf_conn_comp_outside_back to K is injective, the map from sections to K is also injective
  let inj' := inverse_system.sections_injective (ComplInfComp G) K top,

  -- Because we have at least three ends and enough automorphisms, we can apply `good_autom_bwd_map_not_inj`
  -- giving us K ⊆ K' ⊆ L with the inf_conn_comp_outside_back from L to K' not injective.
  rcases (good_autom_bwd_map_not_inj G Gpc auts K (many_ends.trans ⟨_,inj'⟩)) with ⟨K',L,KK',K'L,bwd_K_not_inj⟩,
  -- which is in contradiction with the fact that all inf_conn_comp_outside_back to K are injective
  apply bwd_K_not_inj,
  -- The following is just that if f ∘ g is injective, then so is g
  rintro x y eq,
  apply top ⟨L,by {exact KK'.trans K'L,}⟩,
  simp only [ComplInfComp.map],
  have eq' := congr_arg (@inf_conn_comp_outside_back _ _ _ G KK') eq,
  simp only [inf_conn_comp_outside_back.comp_apply] at eq',
  exact eq',
end


end simple_graph

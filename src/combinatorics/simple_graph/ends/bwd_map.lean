import data.set.finite
import data.sym.sym2
import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import topology.metric_space.basic
import data.setoid.partition
import set_theory.cardinal.basic

import .mathlib
import .reachable_outside

open function
open finset
open set
open classical
open simple_graph.walk
open relation
open cardinal

universes u v w



noncomputable theory
local attribute [instance] prop_decidable

namespace simple_graph


variables  {V : Type u}
           (G : simple_graph V)



namespace bwd_map

open ro_component


def bwd_map (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L) : ro_components G L → ro_components G K :=
λ D,
let
  itexists := ro_component.of_ro_set G
              K D.val
              (ro_component.nempty G L D.val D.prop)
              (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop)
, C := some itexists
, C_prop := some_spec itexists
in
  ⟨C,C_prop.1⟩


def bwd_map_def  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : ro_components G L) (C : ro_components G K) :
  bwd_map G Gpc K_sub_L D = C ↔ D.val ⊆ C.val :=
let
  itexists := ro_component.of_ro_set G K D (ro_component.nempty G L D.val D.prop) (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop),
  C' := some itexists,
  C_prop' := some_spec itexists
in
  begin
    have eqdef : bwd_map G Gpc K_sub_L D =
           ⟨C',C_prop'.1⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := ro_component.unique_of_ro_set G K D (ro_component.nempty G L D.val D.prop) (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop,sub⟩).symm,simp,
    }
  end

def bwd_map_sub  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : ro_components G L) : D.val ⊆ (bwd_map G Gpc K_sub_L D).val :=
begin
  apply (bwd_map_def G Gpc K_sub_L D (bwd_map G Gpc K_sub_L D)).mp,
  reflexivity,
end

lemma bwd_map_refl'  (Gpc : G.preconnected) (K : finset V) (C : ro_components G K) : bwd_map G Gpc (set.subset.refl K) C = C :=
by {rw bwd_map_def}

lemma bwd_map_refl  (Gpc : G.preconnected) (K : finset V) : bwd_map G Gpc (subset.refl K) = id :=
funext (bwd_map_refl' G Gpc K)



def bwd_map_comp  (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) :
  (bwd_map G Gpc K_sub_L) ∘ (bwd_map G Gpc L_sub_M) = (bwd_map G Gpc (K_sub_L.trans L_sub_M)) :=
begin
  apply funext,
  rintro E,
  let D := bwd_map G Gpc L_sub_M E,
  let C := bwd_map G Gpc K_sub_L D,
  apply eq.symm,
  unfold function.comp,
  apply (bwd_map_def G Gpc (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G Gpc L_sub_M E).trans (bwd_map_sub G Gpc K_sub_L D),
end

def bwd_map_comp'   (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) (E : ro_components G M) :
  bwd_map G Gpc K_sub_L (bwd_map G Gpc L_sub_M E) = bwd_map G Gpc (K_sub_L.trans L_sub_M) E :=
begin
  let D := bwd_map G Gpc L_sub_M E,
  let C := bwd_map G Gpc K_sub_L D,
  apply eq.symm,
  apply (bwd_map_def G Gpc (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G Gpc L_sub_M E).trans (bwd_map_sub G Gpc K_sub_L D),
end

def bwd_map_diamond  (Gpc : G.preconnected) {K L L' M : finset V}
  (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)  (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)
  (E : ro_components G M) :
  bwd_map G Gpc K_sub_L (bwd_map G Gpc L_sub_M E) = bwd_map G Gpc K_sub_L' (bwd_map G Gpc L'_sub_M E) :=
by rw [bwd_map_comp',bwd_map_comp']


/- TODO : A converse lemma to the one below: if some component is in the image of all bwd_maps, it is infinite-/

lemma bwd_map_surjective_on_of_inf [locally_finite G]  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (C : ro_components G K) (Cinf : C.val.infinite) : C ∈ set.range (bwd_map G Gpc K_sub_L) :=

begin
  rcases C with ⟨C,C_comp⟩,

  let L_comps := ro_components G L,
  let L_comps_in_C := { D : set V | D ∈ ro_components G L ∧ D ⊆ C},
  have sub : L_comps_in_C ⊆ L_comps, from (λ D ⟨a,b⟩,  a),
  have : L_comps_in_C.finite, from set.finite.subset (ro_component.finite G Gpc L) sub,
  have : (⋃₀ L_comps_in_C).infinite, by {
    rintro hfin,
    have lol := set.infinite.mono (ro_component.sub_ro_components_cover G Gpc K L K_sub_L C C_comp) Cinf,
    have := set.finite_union.mpr ⟨finset.finite_to_set L,hfin⟩,
    exact lol this,
  },

  have : ∃ D : set V, D ∈ L_comps_in_C ∧ D.infinite, by {
    by_contra' all_fin,
    simp at all_fin,
    exact this ( set.finite.sUnion
                 ‹L_comps_in_C.finite›
                 ( λ D ⟨D_comp,D_sub_C⟩, all_fin D D_comp D_sub_C) ),},
  rcases this with ⟨D,⟨⟨D_comp_L,D_sub_C⟩,Dinf⟩⟩,
  simp,
  use [D,D_comp_L],
  rw (bwd_map_def G Gpc K_sub_L ⟨D,D_comp_L⟩ ⟨C,C_comp⟩),
  exact D_sub_C,
end

lemma bwd_map_inf_of_surjective_on [locally_finite G]  (Gpc : G.preconnected) (K : finset V)
  (C : ro_components G K)
  (surj_on : ∀ (L : finset V) (KL : K ⊆ L), C ∈ set.range (bwd_map G Gpc KL)) : C.val.infinite :=
begin
  intro Cfin,
  let Cfinset := Cfin.to_finset,
  let L := Cfinset ∪ K,
  obtain ⟨D,DtoC⟩ := surj_on L (subset_union_right Cfinset K),
  have : D.val ⊆ C.val, from DtoC ▸  bwd_map_sub G Gpc (subset_union_right Cfinset K) D,
  sorry,
  -- D is a subset of C, but at the same time it is disjoint from L, hence from C.
  -- It follows that D is empty, a contradiction, since ro_components are not empty
end

lemma bwd_map_inf_to_inf [locally_finite G]  (Gpc : G.preconnected) {K L : finset V} (KL : K ⊆ L) :
  maps_to (bwd_map G Gpc KL) {C : ro_components G L | C.val.infinite} {D : ro_components G K | D.val.infinite} :=
begin
  sorry,
end

end bwd_map

end simple_graph

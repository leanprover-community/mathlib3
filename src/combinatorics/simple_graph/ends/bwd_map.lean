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


def bwd_map.def  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
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
  apply (bwd_map.def G Gpc K_sub_L D (bwd_map G Gpc K_sub_L D)).mp,
  reflexivity,
end

lemma bwd_map.refl'  (Gpc : G.preconnected) (K : finset V) (C : ro_components G K) : bwd_map G Gpc (set.subset.refl K) C = C :=
by {rw bwd_map.def}

lemma bwd_map.refl  (Gpc : G.preconnected) (K : finset V) : bwd_map G Gpc (subset.refl K) = id :=
funext (bwd_map.refl' G Gpc K)



def bwd_map.comp  (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) :
  (bwd_map G Gpc K_sub_L) ∘ (bwd_map G Gpc L_sub_M) = (bwd_map G Gpc (K_sub_L.trans L_sub_M)) :=
begin
  apply funext,
  rintro E,
  let D := bwd_map G Gpc L_sub_M E,
  let C := bwd_map G Gpc K_sub_L D,
  apply eq.symm,
  unfold function.comp,
  apply (bwd_map.def G Gpc (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G Gpc L_sub_M E).trans (bwd_map_sub G Gpc K_sub_L D),
end

def bwd_map.comp'   (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) (E : ro_components G M) :
  bwd_map G Gpc K_sub_L (bwd_map G Gpc L_sub_M E) = bwd_map G Gpc (K_sub_L.trans L_sub_M) E :=
begin
  let D := bwd_map G Gpc L_sub_M E,
  let C := bwd_map G Gpc K_sub_L D,
  apply eq.symm,
  apply (bwd_map.def G Gpc (K_sub_L.trans L_sub_M) E C).mpr,
  exact (bwd_map_sub G Gpc L_sub_M E).trans (bwd_map_sub G Gpc K_sub_L D),
end

def bwd_map.diamond  (Gpc : G.preconnected) {K L L' M : finset V}
  (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M)  (K_sub_L' : K ⊆ L') (L'_sub_M : L' ⊆ M)
  (E : ro_components G M) :
  bwd_map G Gpc K_sub_L (bwd_map G Gpc L_sub_M E) = bwd_map G Gpc K_sub_L' (bwd_map G Gpc L'_sub_M E) :=
by rw [bwd_map.comp',bwd_map.comp']


/- TODO : A converse lemma to the one below: if some component is in the image of all bwd_maps, it is infinite-/

lemma bwd_map.surjective_on_of_inf [locally_finite G]  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
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
  rw (bwd_map.def G Gpc K_sub_L ⟨D,D_comp_L⟩ ⟨C,C_comp⟩),
  exact D_sub_C,
end

lemma bwd_map.inf_of_surjective_on [locally_finite G]  (Gpc : G.preconnected) (K : finset V)
  (C : ro_components G K)
  (surj_on : ∀ (L : finset V) (KL : K ⊆ L), C ∈ set.range (bwd_map G Gpc KL)) : C.val.infinite :=
begin
  intro Cfin,
  let Cfinset := Cfin.to_finset,
  let L := Cfinset ∪ K,
  obtain ⟨D,DtoC⟩ := surj_on L (subset_union_right Cfinset K),
  have : D.val ⊆ C.val, from DtoC ▸ bwd_map_sub G Gpc (subset_union_right Cfinset K) D,
  sorry,
  -- D is a subset of C, but at the same time it is disjoint from L, hence from C.
  -- It follows that D is empty, a contradiction, since ro_components are not empty
end

lemma bwd_map.inf_to_inf (Gpc : G.preconnected) {K L : finset V} (KL : K ⊆ L) :
  maps_to (bwd_map G Gpc KL) (inf_ro_components' G L) (inf_ro_components' G K)   :=
begin
  dsimp [inf_ro_components'],
  unfold maps_to,
  rintro C Cinf,
  let sub := bwd_map_sub G Gpc KL C,
  exact infinite.mono sub Cinf,
end


-- TODO: use this def in `end_limit_construction` too
-- TODO: lemmas for this def
def bwd_map_inf  (Gpc : G.preconnected) {K L : finset V} (KL : K ⊆ L) :
  inf_ro_components' G L → inf_ro_components' G K := maps_to.restrict _ _ _ (bwd_map.inf_to_inf G Gpc KL)

def bwd_map_inf.def  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : inf_ro_components' G L) (C : inf_ro_components' G K) :
  bwd_map_inf G Gpc K_sub_L D = C ↔ D.val.val ⊆ C.val.val := sorry

lemma bwd_map_inf.surjective  (Gpc : G.preconnected) {K L : finset V} (KL : K ⊆ L) :
  function.surjective (bwd_map_inf G Gpc KL) := sorry

lemma bwd_map_inf.refl'  (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components' G K) :
bwd_map_inf G Gpc (set.subset.refl K) C = C := sorry

lemma bwd_map_inf.refl  (Gpc : G.preconnected) (K : finset V)  :
bwd_map_inf G Gpc (set.subset.refl K) = id := sorry


def bwd_map_inf.comp  (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) :
  (bwd_map_inf G Gpc K_sub_L) ∘ (bwd_map_inf G Gpc L_sub_M) = (bwd_map_inf G Gpc (K_sub_L.trans L_sub_M)) := sorry

def bwd_map_inf.comp'   (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) (E : inf_ro_components' G M) :
  bwd_map_inf G Gpc K_sub_L (bwd_map_inf G Gpc L_sub_M E) = bwd_map_inf G Gpc (K_sub_L.trans L_sub_M) E := sorry

def bwd_map_inf.sub  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : inf_ro_components' G L) : D.val.val ⊆ (bwd_map_inf G Gpc K_sub_L D).val.val := sorry


-- Towards Hopf-Freudenthal

lemma bwd_map_non_inj [locally_finite G] (Gpc : G.preconnected) (H K : finset V) (C : inf_ro_components' G H)
  (D D' : inf_ro_components' G K)
  (Ddist : D ≠ D')
  (h : D.val.val ⊆ C.val.val) (h' : D'.val.val ⊆ C.val.val) :
  ¬ injective (bwd_map_inf G Gpc (finset.subset_union_left H K : H ⊆ H ∪ K)) :=
begin
  rcases bwd_map_inf.surjective G Gpc (finset.subset_union_right H K) D  with ⟨E,rfl⟩,
  rcases bwd_map_inf.surjective G Gpc (finset.subset_union_right H K) D' with ⟨E',rfl⟩,
  have Edist : E ≠ E', by {rintro Eeq, rw Eeq at Ddist,exact Ddist (refl _)},
  have : bwd_map_inf G Gpc (finset.subset_union_left H K) E = bwd_map_inf G Gpc (finset.subset_union_left H K) E', by {
    have EsubC : E.val.val ⊆ C.val.val, by {apply set.subset.trans (bwd_map_inf.sub G Gpc _ E) h,},
    have E'subC : E'.val.val ⊆ C.val.val, by {apply set.subset.trans (bwd_map_inf.sub G Gpc _ E') h',},
    rw (bwd_map_inf.def G Gpc (finset.subset_union_left H K) E C).mpr EsubC,
    rw ←(bwd_map_inf.def G Gpc (finset.subset_union_left H K) E' C).mpr E'subC,
  },
  rintro inj,
  exact Edist (inj this),
end



lemma nicely_arranged_bwd_map_not_inj[locally_finite G] (Gpc : G.preconnected) (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E : inf_ro_components' G H) (inf_comp_H_large : 2 < @fintype.card _ (ro_component.inf_components_finite G Gpc H))
  (F : inf_ro_components' G K)
  (H_F : (H : set V) ⊆ F.val)
  (K_E : (K : set V) ⊆ E.val) : ¬ injective (bwd_map G Gpc (finset.subset_union_left K H : K ⊆ K ∪ H)) :=
begin
 have : ∃ E₁ E₂ : inf_ro_components' G H, E ≠ E₁ ∧ E ≠ E₂ ∧ E₁ ≠ E₂ :=
  begin
    rcases ((@fintype.two_lt_card_iff _ (ro_component.inf_components_finite G Gpc H)).mp (inf_comp_H_large)) with ⟨E₀, E₁, E₂, h₀₁, h₀₂, h₁₂⟩,
    by_cases hyp : E ≠ E₁ ∧ E ≠ E₂,
    { cases hyp, refine ⟨E₁, E₂, _, _, _⟩, all_goals {assumption}, },
    { have hyp' : E = E₁ ∨ E = E₂ := by {simp [auto.classical.implies_iff_not_or] at hyp, assumption,}, cases hyp',
      { subst hyp', refine ⟨E₀, E₂, ne.symm _, _, _⟩, all_goals {assumption}, },
      { subst hyp', refine ⟨E₀, E₁, ne.symm _, ne.symm _, _⟩, all_goals {assumption}, } }
  end,
  rcases this with ⟨E₁, E₂, h₀₁, h₀₂, h₁₂⟩,
  apply bwd_map_non_inj G Gpc K H F E₁ E₂ h₁₂ _ _,
  {apply nicely_arranged G Gpc H K Hnempty Knempty E E₁ h₀₁ F H_F K_E,},
  {apply nicely_arranged G Gpc H K Hnempty Knempty E E₂ h₀₂ F H_F K_E,},
end


end bwd_map

end simple_graph

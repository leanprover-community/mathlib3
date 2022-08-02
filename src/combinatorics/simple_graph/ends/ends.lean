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



namespace ends

open ro_component


-- TODO: maybe, define bwd_map for (potentially finite) ro_components and then restrict it

def bwd_map (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L) : inf_ro_components G L → inf_ro_components G K :=
λ D,
let
  itexists := ro_component.of_ro_set G
              K D.val
              (ro_component.nempty G L D.val D.prop.1)
              (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop.1)
, C := some itexists
, C_prop := some_spec itexists
in
  ⟨C,C_prop.1, λ fin, D.prop.2 (set.finite.subset fin C_prop.2)⟩


def bwd_map_def  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : inf_ro_components G L) (C : inf_ro_components G K) :
  bwd_map G Gpc K_sub_L D = C ↔ D.val ⊆ C.val :=
let
  itexists := ro_component.of_ro_set G K D (ro_component.nempty G L D.val D.prop.1) (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop.1),
  C' := some itexists,
  C_prop' := some_spec itexists
in
  begin
    have eqdef : bwd_map G Gpc K_sub_L D =
           ⟨C',C_prop'.1, λ fin, D.prop.2 (set.finite.subset fin C_prop'.2)⟩, by
    { unfold bwd_map, dsimp,simpa,},
    split,
    { intro eq, cases eq, exact C_prop'.2,},
    { intro sub,
      have lol := ro_component.unique_of_ro_set G K D (ro_component.nempty G L D.val D.prop.1) (ro_component.ro_of_ro_component G Gpc K L K_sub_L D.val D.prop.1), -- the fact that D is still connected wrt K … should be easy
      rcases lol with ⟨uniqueC,uniqueC_is_good,unicity⟩,
      rw eqdef,
      apply subtype.ext_val, simp,
      rw (unicity C' C_prop'),
      rw (unicity C.val ⟨C.prop.1,sub⟩).symm,simp,
    }
  end

def bwd_map_sub  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L)
  (D : inf_ro_components G L) : D.val ⊆ (bwd_map G Gpc K_sub_L D).val :=
begin
  apply (bwd_map_def G Gpc K_sub_L D (bwd_map G Gpc K_sub_L D)).mp,
  reflexivity,
end

lemma bwd_map_refl'  (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components G K) : bwd_map G Gpc (set.subset.refl K) C = C :=
by {rw bwd_map_def}

lemma bwd_map_refl  (Gpc : G.preconnected) (K : finset V) : bwd_map G Gpc (subset.refl K) = id :=
funext (bwd_map_refl' G Gpc K)

lemma bwd_map_surjective [locally_finite G]  (Gpc : G.preconnected) {K L : finset V} (K_sub_L : K ⊆ L) :
surjective (bwd_map G Gpc K_sub_L) :=
begin
  unfold surjective,
  rintros ⟨C,C_comp,C_inf⟩,
  let L_comps := ro_components G L,
  let L_comps_in_C := { D : set V | D ∈ ro_components G L ∧ D ⊆ C},
  have sub : L_comps_in_C ⊆ L_comps, from (λ D ⟨a,b⟩,  a),
  have : L_comps_in_C.finite, from set.finite.subset (ro_component.finite G Gpc L) sub,
  have : (⋃₀ L_comps_in_C).infinite, by {
    rintro hfin,
    have lol := set.infinite.mono (ro_component.sub_ro_components_cover G Gpc K L K_sub_L C C_comp) C_inf,
    have := set.finite_union.mpr ⟨finset.finite_to_set L,hfin⟩,
    exact lol this,
  },
    --λ fin, C_inf ((sorry : (L : set V).finite).union fin).subset (subcomponents_cover G Gpc K_sub_L C C_comp)),

  have : ∃ D : set V, D ∈ L_comps_in_C ∧ D.infinite, by {
    by_contra' all_fin,
    simp at all_fin,
    exact this ( set.finite.sUnion
                 ‹L_comps_in_C.finite›
                 ( λ D ⟨D_comp,D_sub_C⟩, all_fin D D_comp D_sub_C) ),},
  rcases this with ⟨D,⟨D_comp_L,D_sub_C⟩,D_inf⟩,
  use ⟨D,D_comp_L,D_inf⟩,
  rw (bwd_map_def G Gpc K_sub_L ⟨D,D_comp_L,D_inf⟩ ⟨C,C_comp,C_inf⟩),
  exact D_sub_C,
end


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

def bwd_map_comp'   (Gpc : G.preconnected) {K L M : finset V} (K_sub_L : K ⊆ L) (L_sub_M : L ⊆ M) (E : inf_ro_components G M) :
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
  (E : inf_ro_components G M) :
  bwd_map G Gpc K_sub_L (bwd_map G Gpc L_sub_M E) = bwd_map G Gpc K_sub_L' (bwd_map G Gpc L'_sub_M E) :=
by rw [bwd_map_comp',bwd_map_comp']


-- Towards Hopf-Freudenthal

lemma bwd_map_non_inj [locally_finite G] (Gpc : G.preconnected) (H K : finset V) (C : inf_ro_components G H)
  (D D' : inf_ro_components G K)
  (Ddist : D ≠ D')
  (h : D.val ⊆ C.val) (h' : D'.val ⊆ C.val) :
  ¬ injective (bwd_map G Gpc (finset.subset_union_left H K : H ⊆ H ∪ K)) :=
begin
  rcases bwd_map_surjective G Gpc (finset.subset_union_right H K) D  with ⟨E,rfl⟩,
  rcases bwd_map_surjective G Gpc (finset.subset_union_right H K) D' with ⟨E',rfl⟩,
  have Edist : E ≠ E', by {rintro Eeq, rw Eeq at Ddist,exact Ddist (refl _)},
  have : bwd_map G Gpc (finset.subset_union_left H K) E = bwd_map G Gpc (finset.subset_union_left H K) E', by {
    have : E.val ⊆ C.val, by {apply set.subset.trans (bwd_map_sub G Gpc _ E) h,},
    have : E'.val ⊆ C.val, by {apply set.subset.trans (bwd_map_sub G Gpc _ E') h',},
    rw (bwd_map_def G Gpc (finset.subset_union_left H K) E C).mpr ‹E.val ⊆ C.val›,
    rw ←(bwd_map_def G Gpc (finset.subset_union_left H K) E' C).mpr ‹E'.val ⊆ C.val›,
  },
  rintro inj,
  exact Edist (inj this),
end

lemma nicely_arranged [locally_finite G] (Gpc : G.preconnected) (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E E' : inf_ro_components G H) (En : E ≠ E')
  (F : inf_ro_components G K)
  (H_F : (H : set V) ⊆ F.val)
  (K_E : (K : set V) ⊆ E.val) : E'.val ⊆ F.val :=
begin
  by_cases h : (E'.val ∩ K).nonempty,
  { rcases h with ⟨v,v_in⟩,
    have vE' : v ∈ E'.val, from ((set.mem_inter_iff v E'.val K).mp v_in).left,
    have vE : v ∈ E.val, from  K_E ((set.mem_inter_iff v E'.val K).mp v_in).right,
    have := ro_component.eq_of_common_mem G H E.val E'.val E.prop.1 E'.prop.1 v vE vE',
    exfalso,
    exact En (subtype.eq this),},
  {
    have : ∃ F' : inf_ro_components G K, E'.val ⊆ F'.val, by {
      rcases ro_component.of_subconnected_disjoint G K E'.val
             (set.infinite.nonempty E'.prop.2)
             (by {unfold disjoint, rw [le_bot_iff], rw [set.not_nonempty_iff_eq_empty] at h, assumption,}) -- empty intersection means disjoint
             (ro_component.to_subconnected G H E' E'.prop.1) with ⟨F',F'comp,sub⟩,
      have F'inf : F'.infinite, from set.infinite.mono sub E'.prop.2,
      use ⟨F',F'comp,F'inf⟩,
      exact sub,
    },
    rcases this with ⟨F',E'_sub_F'⟩,
    by_cases Fe : F' = F,
    { exact Fe ▸ E'_sub_F',},
    { rcases ro_component.adjacent_to G Gpc H Hnempty E'.val E'.prop.1 with ⟨v,vh,vhH,vF',adj⟩,
      have : vh ∈ F.val, from H_F vhH,
      have : F.val = F'.val,
        from ro_component.eq_of_adj_mem G K F.val F.prop.1 F'.val F'.prop.1 vh v this (E'_sub_F' vF') adj,
      exfalso,
      exact Fe (subtype.eq this).symm,
    },
  },
end

lemma nicely_arranged_bwd_map_not_inj[locally_finite G] (Gpc : G.preconnected) (H K : finset V)
  (Hnempty : H.nonempty) (Knempty : K.nonempty)
  (E : inf_ro_components G H) (inf_comp_H_large : 2 < @fintype.card _ (ro_component.inf_components_finite G Gpc H))
  (F : inf_ro_components G K)
  (H_F : (H : set V) ⊆ F.val)
  (K_E : (K : set V) ⊆ E.val) : ¬ injective (bwd_map G Gpc (finset.subset_union_left K H : K ⊆ K ∪ H)) :=
begin
 have : ∃ E₁ E₂ : inf_ro_components G H, E ≠ E₁ ∧ E ≠ E₂ ∧ E₁ ≠ E₂ :=
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





private def up (K : finset V) := {L : finset V | K ⊆ L}
private lemma in_up  (K : finset V) : K ∈ (up K) := finset.subset.refl K
private lemma up_cofin  (K : finset V) :
  ∀ M : finset V, ∃ L : finset V, L ∈ up K ∧  M ⊆ L := λ M, ⟨M ∪ K,⟨subset_union_right M K,subset_union_left M K⟩⟩




private structure fam :=
  (fam: set (finset V))
  (cof: ∀ K : finset V, ∃ F : finset V, F ∈ fam ∧ K ⊆ F)
private def fin_fam : fam := ⟨@set.univ (finset V),(λ K, ⟨K,trivial,finset.subset.refl K⟩)⟩
private def fin_fam_up (K : finset V) : fam := ⟨up K, up_cofin K⟩

private def mem_fin_fam {ℱ : @fam V} (K : ℱ.fam) : (@fin_fam V).fam := ⟨↑K,trivial⟩


def ends_for (Gpc: G.preconnected) (ℱ : fam) :=
{ f : Π (K : ℱ.fam), inf_ro_components G K.val | ∀ K L : ℱ.fam, ∀ h : K.val ⊆ L.val, bwd_map G Gpc h (f L) = (f K) }

lemma ends_for_directed (Gpc: G.preconnected) (ℱ : fam)
  (g : ends_for G Gpc ℱ) (K L : ℱ.fam) :
  ∃ (F : ℱ.fam) (hK : K.val ⊆ F.val) (hL : L.val ⊆ F.val),
    g.1 K = bwd_map G Gpc hK (g.1 F) ∧ g.1 L = bwd_map G Gpc hL (g.1 F) :=
begin
  rcases (ℱ.cof (↑K ∪ ↑L)) with ⟨F,F_fam,sub_F⟩,
  use F,
  use F_fam,
  use ((finset.subset_union_left K.val L.val).trans sub_F),
  use ((finset.subset_union_right K.val L.val).trans sub_F),
  split;
  { apply eq.symm,
    apply g.2,}
 end

def ends (Gpc: G.preconnected) := ends_for G Gpc fin_fam


def to_ends_for (Gpc: G.preconnected) (ℱ : fam) : ends G Gpc → ends_for G Gpc ℱ :=
λ f : ends G Gpc, ⟨ λ K, f.1 (mem_fin_fam K)
              , λ K L h, f.2 (mem_fin_fam K) (mem_fin_fam L) h⟩

def to_ends_for_def (Gpc: G.preconnected) (ℱ : fam) (e : ends G Gpc) (K : ℱ.fam) :
  e.val (mem_fin_fam K) = (to_ends_for G Gpc ℱ e).val K := refl _


def of_ends_for_fun  (Gpc: G.preconnected) (ℱ : @fam V) (e : ends_for G Gpc ℱ) : Π (K : (fin_fam).fam), inf_ro_components G K.val := λ K,
let
  F :=  (ℱ.cof K).some
, F_fam := (ℱ.cof K).some_spec.1
, K_sub_F := (ℱ.cof K).some_spec.2
in
  bwd_map G Gpc K_sub_F (e.1 ⟨F,F_fam⟩)

def of_ends_for_comm (Gpc: G.preconnected) (ℱ : fam) (e : ends_for G Gpc ℱ) :
  ∀ K L : (fin_fam).fam, ∀ h : K.val ⊆ L.val, bwd_map G Gpc h ((of_ends_for_fun G Gpc ℱ) e L) = (of_ends_for_fun G Gpc ℱ) e K :=
λ K L hKL, by {
      rcases (ℱ.cof K) with ⟨FK,⟨FK_fam,K_FK⟩⟩,
      rcases (ℱ.cof L) with ⟨FL,⟨FL_fam,L_FL⟩⟩,
      rcases ends_for_directed G Gpc ℱ e ⟨FK,FK_fam⟩ ⟨FL,FL_fam⟩ with ⟨M,FK_M,FL_M,backK,backL⟩,
      have hey : of_ends_for_fun G Gpc ℱ e K = bwd_map G Gpc K_FK (e.1 ⟨FK,FK_fam⟩), by {
        unfold of_ends_for_fun,
        simp,
        sorry,
      },
      have hoo : of_ends_for_fun G Gpc ℱ e L = bwd_map G Gpc L_FL (e.1 ⟨FL,FL_fam⟩), by {sorry},
      rw [hey,hoo,backK,backL,bwd_map_comp',bwd_map_comp',bwd_map_comp'],
}


def of_ends_for (Gpc: G.preconnected) (ℱ : fam) : ends_for G Gpc ℱ → ends G Gpc :=
λ e, ⟨of_ends_for_fun G Gpc ℱ e, of_ends_for_comm G Gpc ℱ e⟩

lemma of_ends_for.preserves (Gpc: G.preconnected) (ℱ : fam) (K : ℱ.fam) (e : ends_for G Gpc ℱ) :
  e.val K = (of_ends_for G Gpc ℱ e).val (mem_fin_fam K) := sorry

lemma to_ends_for.preserves (Gpc: G.preconnected) (ℱ : fam) (K : ℱ.fam) (e : ends G Gpc) :
  e.val (mem_fin_fam K) = (to_ends_for G Gpc ℱ e).val K := sorry

-- Thanks Kyle Miller
def equiv_ends_for (Gpc: G.preconnected) (ℱ : fam) : ends G Gpc ≃ ends_for G Gpc ℱ :=
{ to_fun := to_ends_for G Gpc ℱ,
  inv_fun := of_ends_for G Gpc ℱ,
  left_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end,
  right_inv := begin
    rintro ⟨g, g_comm⟩,
    simp only [of_ends_for, to_ends_for, comp_app, id.def, subtype.mk_eq_mk],
    ext1 F,
    apply g_comm,
  end }


lemma ends_empty_graph (Gpc: G.preconnected) : is_empty V → is_empty (ends G Gpc) :=
begin
  rintros ⟨no_V⟩,
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨@finset.empty V,trivial⟩ with ⟨_,⟨b,_⟩,_⟩,
  exact no_V b,
end

lemma ends_finite_graph  (Gpc: G.preconnected) (Vfinite : (@set.univ V).finite) : is_empty (ends G Gpc) :=
begin
  apply is_empty.mk,
  rintros ⟨f,f_comm⟩,
  rcases f ⟨set.finite.to_finset Vfinite,trivial⟩ with ⟨C,⟨_,_⟩,C_inf⟩,
  exact C_inf (set.finite.subset Vfinite (set.subset_univ C)),
end


def eval_for (Gpc: G.preconnected) (ℱ : fam) (K : ℱ.fam):
  ends_for G Gpc ℱ → inf_ro_components G K := λ e, e.val K


def eval  (Gpc: G.preconnected) (K : finset V) : ends G Gpc → inf_ro_components G K := eval_for G Gpc fin_fam ⟨K,trivial⟩


def eval_comm  (Gpc: G.preconnected) (ℱ : fam) (K : ℱ.fam) (e : ends G Gpc) :
  eval_for G Gpc ℱ K (equiv_ends_for G Gpc ℱ e) = eval G Gpc K.val e :=
begin
  simp only [eval, eval_for, equiv_ends_for, equiv.coe_fn_mk],
  rw [←to_ends_for_def],
  simpa only,
end

def eval_comm'  (Gpc: G.preconnected) (ℱ : fam) (K : ℱ.fam) :
  (eval_for G Gpc ℱ K) ∘ (equiv_ends_for G Gpc ℱ) = eval G Gpc K.val := by {
  apply funext,
  rintros e, exact eval_comm G Gpc ℱ K e,}



lemma eval_injective_for_up  (Gpc: G.preconnected)
  (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G Gpc ‹K⊆L›)) :
  injective (eval_for G Gpc (fin_fam_up K) ⟨K,in_up K⟩) :=
begin
  rintros e₁ e₂,
  simp only [eval_for, subtype.val_eq_coe],
  rintro same,
  apply subtype.eq,
  ext1 L,
  simp only [subtype.val_eq_coe],
  apply inj_from_K L L.prop,
  rw [e₁.prop ⟨K,in_up K⟩ L L.prop, e₂.prop ⟨K,in_up K⟩ L L.prop],
  assumption,
end

lemma eval_bijective_for_up [locally_finite G] (Gpc: G.preconnected)
  (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G Gpc ‹K⊆L›)) :
  bijective (eval_for G Gpc (fin_fam_up K) ⟨K,in_up K⟩) :=
begin
  split,
  { exact eval_injective_for_up G Gpc K inj_from_K,},
  { rintros C,
    let f : Π (L : (fin_fam_up K).fam), inf_ro_components G L.val, by {
      rintro ⟨L,KL⟩,
      have : bijective (bwd_map G Gpc KL), from ⟨inj_from_K L KL,bwd_map_surjective G Gpc KL⟩,
      exact (equiv.of_bijective _ this).inv_fun C,
    },
    use f,
    { unfold ends_for,
      simp,
      rintros L KL M KM LM,
      sorry,
    },
    { unfold eval_for,
      simp only [*, equiv.inv_fun_as_coe],
      have bijK : bijective (bwd_map G Gpc (subset.refl K)), from ⟨inj_from_K K (subset.refl K),bwd_map_surjective G Gpc (subset.refl K)⟩,
      nth_rewrite_lhs 0 ←(bwd_map_refl' G Gpc K C),
      exact equiv.of_bijective_symm_apply_apply (bwd_map G Gpc _) bijK C,}
  }
end


/-
  This shows that if K is such that the "backward maps" to K are all injective, then so is
  the evaluation map.
  It should eventually be used to bound the number of ends from above in certain cases.
  Say, when G Gpc is the grid ℤ²,
-/
lemma eval_injective  (Gpc: G.preconnected)
  (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G Gpc ‹K⊆L›)) :
  injective (eval G Gpc K) :=
begin
  have eval_for_inj := eval_injective_for_up G Gpc K inj_from_K,
  rw (eval_comm' G Gpc (fin_fam_up K)  ⟨K,le_refl K⟩).symm,
  exact injective.comp eval_for_inj (equiv_ends_for G Gpc (fin_fam_up K)).bijective.injective,
end


lemma eval_bijective [locally_finite G] (Gpc: G.preconnected)
  (K : finset V)
  (inj_from_K : ∀ L : finset V, K ⊆ L → injective (bwd_map G Gpc ‹K⊆L›)) :
  bijective (eval G Gpc K) :=
begin
  have eval_for_bij := eval_bijective_for_up G Gpc K inj_from_K,
  rw (eval_comm' G Gpc (fin_fam_up K)  ⟨K,le_refl K⟩).symm,
  exact bijective.comp eval_for_bij (equiv_ends_for G Gpc (fin_fam_up K)).bijective,
end

lemma eval_bijective' [locally_finite G] [∀ K : finset V, fintype (inf_ro_components G K)] (Gpc: G.preconnected)
  (K : finset V)
  (card_eq_from_K : ∀ L : finset V, K ⊆ L → fintype.card (inf_ro_components G K) = fintype.card (inf_ro_components G L) ) :
  bijective (eval G Gpc K) :=
begin
  let inj_from_K := λ L KL, ((fintype.bijective_iff_surjective_and_card (bwd_map G Gpc KL)).mpr ⟨(bwd_map_surjective G Gpc KL),(card_eq_from_K L KL).symm⟩).1,
  exact eval_bijective G Gpc K inj_from_K,
end

private lemma inf_ro_component_to_preconnected (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components G K) : (G.induce C.val).preconnected :=
begin
  rintro ⟨x,xC⟩ ⟨y,yC⟩,
  obtain ⟨w,wC⟩ := to_subconnected G K C.val C.prop.1 x xC y yC,
  induction w with x x z y a u ih,
  { use nil, },
  { have uC : ↑(u.support.to_finset) ⊆ C.val, by
    { rw walk.support_cons at wC,
      simp at wC,
      exact (set.insert_subset.mp wC).2,},
    have zC : z ∈ C.val, by
    { rw walk.support_cons at wC,
      simp at wC,
      let lol2 := (set.insert_subset.mp wC).2,
      let lol3 := walk.start_mem_support u,
      rw ←list.mem_to_finset at lol3,
      exact lol2 lol3,
    },

    let u' := (ih zC yC uC).some,
    let adjC : (G.induce C.val).adj ⟨x,xC⟩ ⟨z,zC⟩, by { simp, exact a },
    exact ⟨walk.cons adjC u'⟩,
  }

end

private def finbwd (K : finset V) (C : inf_ro_components G K) (L : finset C.val) : finset V :=
  K ∪ (finset.map (function.embedding.subtype C.val) L)

private def as_set {V : Type*} {C D : set V} (h : C ⊆ D) : set D := {d : D | d.val ∈ C}
private def set_as {V : Type*} {D : set V} (C : set D) : set V := {v : V | ∃ (h : v ∈ D),  C ⟨v,h⟩}


private def inf_ro_comp_sub_iff  (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components G K) (L : finset C.val)
  (D : set V) (DC : D ⊆ C) :
  D ∈ inf_ro_components G (finbwd G K C L)  ↔  {d : C.val | d.val ∈ D ∧ d ∉ L} ∈ inf_ro_components (G.induce C.val) L :=
begin
  split,
  { sorry },
  { sorry },
end

lemma ends_decomposition [locally_finite G] (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components G K) :
  {e : ends_for G Gpc (fin_fam_up K) | eval_for G Gpc (fin_fam_up K)  ⟨K,in_up K⟩ e = C}
≃ ends (G.induce C.val) (inf_ro_component_to_preconnected G Gpc K C) :=
begin
  let GC := (G.induce C.val),
  let GCpc := (inf_ro_component_to_preconnected G Gpc K C),

  let φ : {e : ends_for G Gpc (fin_fam_up K) | eval_for G Gpc (fin_fam_up K)  ⟨K,in_up K⟩ e = C} →  (ends GC GCpc ), by {
    rintro ⟨e,eKC⟩,
    let f : Π (L : finset C.val), inf_ro_components GC L, by
    { rintro L,
      let L' : finset V := finbwd G K C L, --K ∪ L,
      have : K ⊆ L', from subset_union_left K _,
      obtain ⟨D',D'comp⟩ := e.val ⟨L',‹K⊆L'›⟩,
      refine ⟨{d : C.val | d.val ∈ D' ∧ d ∉ L},_⟩,
      refine (inf_ro_comp_sub_iff G Gpc K _ L _ _).mp D'comp,
      have : bwd_map G Gpc ‹K⊆L'› ⟨D',D'comp⟩ = C, by {
        --simp [e.prop], --or something
        sorry
      }, -- because eval commutes with bwd by def
      rw ←this,
      exact bwd_map_sub G Gpc ‹K⊆L'› ⟨D',D'comp⟩,
    },
    sorry,
  },
  let ψ : (ends GC GCpc ) → {e : ends_for G Gpc (fin_fam_up K) | eval_for G Gpc (fin_fam_up K)  ⟨K,in_up K⟩ e = C} , by {

  },
  sorry,

end

lemma end_from_component [locally_finite G] (Gpc : G.preconnected) (K : finset V) (C : inf_ro_components G K) :
  ∃ e : (ends G Gpc), e.val ⟨K,trivial⟩ = C := sorry


lemma eval_surjective[locally_finite G] (Gpc : G.preconnected) (K : finset V):
  surjective (eval G Gpc K) := end_from_component G Gpc K


lemma finite_ends_to_inj [locally_finite G] (Gpc : G.preconnected)  [fintype (ends G Gpc)] [Vnempty : nonempty V] :
  ∃ K : finset V, K.nonempty ∧ ∀ (L : finset V) (sub : K ⊆ L), injective (bwd_map G Gpc sub) :=
begin
  let v : V := Vnempty.some,
  let M := fintype.card (ends G Gpc),
  haveI all_fin : ∀ K : finset V, fintype (inf_ro_components G K), from λ K, inf_components_finite' G Gpc K,
  have all_le_M := λ K, fintype.card_le_of_surjective (eval G Gpc K) (eval_surjective G Gpc K),
  have  : ∃ K : finset V, ∀ K' : finset V, fintype.card (inf_ro_components G  K') ≤ fintype.card (inf_ro_components G K), by {
    let cards := set.range (λ K, fintype.card (inf_ro_components G K)),
    have : ∀ c ∈ cards, c ≤ M, by {rintros c ⟨K,rfl⟩, exact all_le_M K,},
    haveI : nonempty (finset V) := sorry,
    have : cards.nonempty := set.range_nonempty _,
    --let lol := finset.max,
    -- Want to have a max card!!
    sorry,
  },
  rcases this with ⟨K,Kmax⟩,
  let Kv := insert v K,
  let KsubKv := finset.subset_insert v K,
  use Kv,
  split,
  { exact finset.insert_nonempty v K, },
  { rintros L KvsubL,
    by_contradiction notinj,
    have Kv_lt_L := fintype.card_lt_of_surjective_not_injective (bwd_map G Gpc KvsubL) (bwd_map_surjective G Gpc KvsubL) notinj,
    have K_le_Kv := fintype.card_le_of_surjective (bwd_map G Gpc KsubKv) (bwd_map_surjective G Gpc KsubKv),
    have K_lt_L := lt_of_le_of_lt K_le_Kv Kv_lt_L,
    exact (Kmax L).not_lt K_lt_L,
  },

end



-- theorem `card_components_mon` sayinG Gpc htat `λ K, card (inf_ro_components G K)` is monotone
-- theorem `finite_ends_iff` sayinG Gpc that `ends` is finite iff the supremum `λ K, card (inf_ro_components G K)` is finite
-- theorem `finite_ends_card_eq` sayinG Gpc that if `ends` is finite, the cardinality is the sup
-- theorem `zero_ends_iff` sayinG Gpc that `ends = ∅` iff `V` is finite



-- need this ?


end ends

end simple_graph

/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl

Basic constructions for topological groups:

* `topological_add_group.to_uniform_space` and `topological_add_group_is_uniform` can be used to
  construct a canonical uniformity for a topological add group.

* `add_group_with_zero_nhd`: construct the topological structure from a group with a neighbourhood
  around zero. Then with `topological_add_group.to_uniform_space` one can derive a `uniform_space`.
-/
import data.set.basic data.set.function
import algebra.pi_instances
import analysis.topology.completion
noncomputable theory

open filter
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}

section topological_add_comm_group
variables {G : Type u} [add_comm_group G] [topological_space G] [topological_add_group G]

variable (G)
def topological_add_group.to_uniform_space : uniform_space G :=
{ uniformity          := comap (λp:G×G, p.2 - p.1) (nhds 0),
  refl                :=
    by refine map_le_iff_le_comap.1 (le_trans _ (pure_le_nhds 0));
      simp [set.subset_def] {contextual := tt},
  symm                :=
  begin
    suffices : tendsto ((λp, -p) ∘ (λp:G×G, p.2 - p.1)) (comap (λp:G×G, p.2 - p.1) (nhds 0)) (nhds (-0)),
    { simpa [(∘), tendsto_comap_iff] },
    exact tendsto.comp tendsto_comap (tendsto_neg tendsto_id)
  end,
  comp                :=
  begin
    intros D H,
    rw mem_lift'_sets,
    { rcases H with ⟨U, U_nhds, U_sub⟩,
      rcases exists_nhds_half U_nhds with ⟨V, ⟨V_nhds, V_sum⟩⟩,
      existsi ((λp:G×G, p.2 - p.1) ⁻¹' V),
      have H : (λp:G×G, p.2 - p.1) ⁻¹' V ∈ (comap (λp:G×G, p.2 - p.1) (nhds (0 : G))).sets,
        by existsi [V, V_nhds] ; refl,
      existsi H,
      have comp_rel_sub : comp_rel ((λp:G×G, p.2 - p.1) ⁻¹' V) ((λp:G×G, p.2 - p.1) ⁻¹' V) ⊆ (λp:G×G, p.2 - p.1) ⁻¹' U,
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa using V_sum _ _ Hz1 Hz2
      end,
      exact set.subset.trans comp_rel_sub U_sub },
    { exact monotone_comp_rel monotone_id monotone_id }
  end,
  is_open_uniformity  :=
  begin
    intro S,
    let S' := λ x, {p : G × G | p.1 = x → p.2 ∈ S},
    show is_open S ↔ ∀ (x : G), x ∈ S → S' x ∈ (comap (λp:G×G, p.2 - p.1) (nhds (0 : G))).sets,
    rw [is_open_iff_mem_nhds],
    refine forall_congr (assume a, forall_congr (assume ha, _)),
    rw [← nhds_translation a, mem_comap_sets, mem_comap_sets],
    refine exists_congr (assume t, exists_congr (assume ht, _)),
    show (λ (y : G), y - a) ⁻¹' t ⊆ S ↔ (λ (p : G × G), p.snd - p.fst) ⁻¹' t ⊆ S' a,
    split,
    { rintros h ⟨x, y⟩ hx rfl, exact h hx },
    { rintros h x hx, exact @h (a, x) hx rfl }
  end }

section
local attribute [instance] topological_add_group.to_uniform_space

lemma uniformity_eq_comap_nhds_zero' : uniformity = comap (λp:G×G, p.2 - p.1) (nhds (0 : G)) := rfl

variable {G}
lemma topological_add_group_is_uniform : uniform_add_group G :=
have tendsto
    ((λp:(G×G), p.1 - p.2) ∘ (λp:(G×G)×(G×G), (p.1.2 - p.1.1, p.2.2 - p.2.1)))
    (comap (λp:(G×G)×(G×G), (p.1.2 - p.1.1, p.2.2 - p.2.1)) ((nhds 0).prod (nhds 0)))
    (nhds (0 - 0)) :=
  tendsto_comap.comp (tendsto_sub tendsto_fst tendsto_snd),
begin
  constructor,
  rw [uniform_continuous, uniformity_prod_eq_prod, tendsto_map'_iff,
    uniformity_eq_comap_nhds_zero' G, tendsto_comap_iff, prod_comap_comap_eq],
  simpa [(∘)]
end
end

lemma to_uniform_space_eq [u : uniform_space α] [add_comm_group α] [uniform_add_group α]:
  topological_add_group.to_uniform_space α = u :=
begin
  ext : 1,
  show @uniformity α (topological_add_group.to_uniform_space α) = uniformity,
  rw [uniformity_eq_comap_nhds_zero' α, uniformity_eq_comap_nhds_zero α]
end

end topological_add_comm_group

/-- β additive group with a neighbourhood around 0.
Only used to construct a topology and uniform space.

This is currently only available for commutative groups, but it can be extended to
non-commutative groups too.
-/
class add_group_with_zero_nhd (α : Type u) extends add_comm_group α :=
(Z : filter α)
(zero_Z {} : pure 0 ≤ Z)
(sub_Z {} : tendsto (λp:α×α, p.1 - p.2) (Z.prod Z) Z)

namespace add_group_with_zero_nhd
variables (α) [add_group_with_zero_nhd α]

local notation `Z` := add_group_with_zero_nhd.Z

instance : topological_space α :=
topological_space.mk_of_nhds $ λa, map (λx, x + a) (Z α)

variables {α}

lemma neg_Z : tendsto (λa:α, - a) (Z α) (Z α) :=
have tendsto (λa, (0:α)) (Z α) (Z α),
  by refine le_trans (assume h, _) zero_Z; simp [univ_mem_sets'] {contextual := tt},
have tendsto (λa:α, 0 - a) (Z α) (Z α), from
  (tendsto.prod_mk this tendsto_id).comp sub_Z,
by simpa

lemma add_Z : tendsto (λp:α×α, p.1 + p.2) ((Z α).prod (Z α)) (Z α) :=
suffices tendsto (λp:α×α, p.1 - -p.2) ((Z α).prod (Z α)) (Z α),
  by simpa,
(tendsto.prod_mk tendsto_fst (tendsto_snd.comp neg_Z)).comp sub_Z

lemma exists_Z_half {s : set α} (hs : s ∈ (Z α).sets) : ∃ V ∈ (Z α).sets, ∀ v w ∈ V, v + w ∈ s :=
begin
  have : ((λa:α×α, a.1 + a.2) ⁻¹' s) ∈ ((Z α).prod (Z α)).sets := add_Z (by simpa using hs),
  rcases mem_prod_iff.1 this with ⟨V₁, H₁, V₂, H₂, H⟩,
  exact ⟨V₁ ∩ V₂, inter_mem_sets H₁ H₂, assume v w ⟨hv, _⟩ ⟨_, hw⟩, @H (v, w) ⟨hv, hw⟩⟩
end

lemma nhds_eq (a : α) : nhds a = map (λx, x + a) (Z α) :=
topological_space.nhds_mk_of_nhds _ _
  (assume a, calc pure a = map (λx, x + a) (pure 0) : by simp
    ... ≤ _ : map_mono zero_Z)
  (assume b s hs,
    let ⟨t, ht, eqt⟩ := exists_Z_half hs in
    have t0 : (0:α) ∈ t, by simpa using zero_Z ht,
    begin
      refine ⟨(λx:α, x + b) '' t, image_mem_map ht, _, _⟩,
      { refine set.image_subset_iff.2 (assume b hbt, _),
        simpa using eqt 0 b t0 hbt },
      { rintros _ ⟨c, hb, rfl⟩,
        refine (Z α).sets_of_superset ht (assume x hxt, _),
        simpa using eqt _ _ hxt hb }
    end)

lemma nhds_zero_eq_Z : nhds 0 = Z α := by simp [nhds_eq]; exact filter.map_id

instance : topological_add_monoid α :=
⟨ continuous_iff_tendsto.2 $ assume ⟨a, b⟩,
  begin
    rw [nhds_prod_eq, nhds_eq, nhds_eq, nhds_eq, filter.prod_map_map_eq,
      tendsto_map'_iff],
    suffices :  tendsto ((λx:α, (a + b) + x) ∘ (λp:α×α,p.1 + p.2)) (filter.prod (Z α) (Z α))
      (map (λx:α, (a + b) + x) (Z α)),
    { simpa [(∘)] },
    exact add_Z.comp tendsto_map
  end⟩

instance : topological_add_group α :=
⟨continuous_iff_tendsto.2 $ assume a,
  begin
    rw [nhds_eq, nhds_eq, tendsto_map'_iff],
    suffices : tendsto ((λx:α, x - a) ∘ (λx:α, -x)) (Z α) (map (λx:α, x - a) (Z α)),
    { simpa [(∘)] },
    exact neg_Z.comp tendsto_map
  end⟩

end add_group_with_zero_nhd

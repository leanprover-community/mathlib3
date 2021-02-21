import topology.algebra.ring
import topology.algebra.open_subgroup
import data.set.basic
import group_theory.subgroup

/--A topological group is non-archimedean if every neighborhood of 1 contains an open subgroup.-/
@[to_additive]
def topological_group.nonarchimedean (G : Type*)
  [group G] [topological_space G] [topological_group G] : Prop :=
∀ U ∈ nhds (1 : G), ∃ V : open_subgroup G, (V : set G) ⊆ U

namespace topological_group

variables {G₀ : Type*} [group G₀] [topological_space G₀] [topological_group G₀]
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables (f : G₀ →* G)

@[to_additive]
lemma nonarchimedean_of_nonarchimedean_open_embedding
  (emb : open_embedding f) (h : nonarchimedean G₀) : nonarchimedean G :=
λ U hU, have h₁ : (f ⁻¹' U) ∈ nhds (1 : G₀), from
  by {apply emb.continuous.tendsto, rwa is_group_hom.map_one f},
let ⟨V, hV⟩ := h (f ⁻¹' U) h₁ in
  ⟨{is_open' := emb.is_open_map _ V.is_open, ..subgroup.map f V},
    set.image_subset_iff.2 hV⟩

end topological_group

namespace topological_add_group
namespace nonarchimedean

open topological_ring
variables {R : Type*} [ring R] [topological_space R] [topological_ring R]
variables {S : Type*} [ring S] [topological_space S] [topological_ring S]

lemma left_mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) (r : R) :
  ∃ V : open_add_subgroup R, r • (V : set R) ⊆ U :=
⟨{is_open' := is_open.preimage (continuous_mul_left r) U.is_open,
    ..add_subgroup.comap (add_monoid_hom.mul_left r) U},
  set.image_preimage_subset (λ x, (add_monoid_hom.mul_left r) x) U⟩

lemma prod_subset (hR : nonarchimedean R) (hS : nonarchimedean S) :
  ∀ U ∈ nhds (0 : R × S), ∃ (V : open_add_subgroup R) (W : open_add_subgroup S),
    (V : set R).prod (W : set S) ⊆ U := λ U hU,
begin
  erw [nhds_prod_eq, filter.mem_prod_iff] at hU,
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩,
  cases hR _ hU₁ with V hV,
  cases hS _ hU₂ with W hW,
  use [V, W, set.subset.trans (set.prod_mono hV hW) h]
end

lemma prod_self_subset (hR : nonarchimedean R) :
  ∀ U ∈ nhds (0 : R × R), ∃ (V : open_add_subgroup R), (V : set R).prod (V : set R) ⊆ U :=
λ U hU, let ⟨V, W, h⟩ := prod_subset hR hR U hU in
  ⟨V ⊓ W, by {refine set.subset.trans (set.prod_mono _ _) ‹_›; simp}⟩

lemma prod (hR : nonarchimedean R) (hS : nonarchimedean S) :
  nonarchimedean (R × S) := λ U hU, let ⟨V, W, h⟩ := prod_subset hR hS U hU in ⟨V.sum W, ‹_›⟩

lemma mul_subset (h : nonarchimedean R) (U : open_add_subgroup R) :
  ∃ V : open_add_subgroup R, (V : set R) * V ⊆ U :=
let ⟨V, H⟩ := prod_self_subset h ((λ r : R × R, r.1 * r.2) ⁻¹' ↑U)
  (mem_nhds_sets (is_open.preimage continuous_mul U.is_open)
  begin
    simpa only [set.mem_preimage, open_add_subgroup.mem_coe, prod.snd_zero, mul_zero] using U.zero_mem,
  end) in begin
    use V,
    intros v hv,
    rcases hv with ⟨a, b, ha, hb, hv⟩,
    have hy := H (set.mk_mem_prod ha hb),
    simp only [set.mem_preimage, open_add_subgroup.mem_coe] at hy,
    rwa hv at hy,
  end

end nonarchimedean
end topological_add_group

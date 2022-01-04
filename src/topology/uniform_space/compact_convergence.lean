/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import topology.compact_open
import topology.uniform_space.uniform_convergence

/-!
# Compact convergence (uniform convergence on compact sets)

Given a topological space `α` and a uniform space `β` (e.g., a metric space or a topological group),
the space of continuous maps `C(α, β)` carries a natural uniform space structure. We define this
uniform space structure in this file and also prove the following properties of the topology it
induces on `C(α, β)`:

 1. Given a sequence of continuous functions `Fₙ : α → β` together with some continuous `f : α → β`,
    then `Fₙ` converges to `f` as a sequence in `C(α, β)` iff `Fₙ` converges to `f` uniformly on
    each compact subset `K` of `α`.
 2. The topology coincides with the compact-open topology.

Property 1 is essentially true by definition but 2 requires a little work and uses the Lebesgue
number lemma.

## The uniform space structure

Given subsets `K ⊆ α` and `V ⊆ β × β`, let `E(K, V) ⊆ C(α, β) × C(α, β)` be the set of pairs of
continuous functions `α → β` which are `V`-close on `K`:
$$
  E(K, V) = \{ (f, g) | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Fixing some `f ∈ C(α, β)`, let `N(K, V, f) ⊆ C(α, β)` be the set of continuous functions `α → β`
which are `V`-close to `f` on `K`:
$$
  N(K, V, f) = \{ g | ∀ (x ∈ K), (f x, g x) ∈ V \}.
$$
Using this notation we can describe the uniform space structure and the topology it induces.
Specifically:
 *  A subset `X ⊆ C(α, β) × C(α, β)` is an entourage for the uniform space structure on `C(α, β)`
    iff there exists a compact `K` and entourage `V` such that `E(K, V) ⊆ X`.
 *  A subset `Y ⊆ C(α, β)` is a neighbourhood of `f` iff there exists a compact `K` and entourage
    `V` such that `N(K, V, f) ⊆ Y`.

The topology on `C(α, β)` thus has a natural subbasis (the compact-open subbasis) and a natural
neighbourhood basis (the compact-convergence neighbourhood basis).

## Main definitions / results

 * `compact_open_eq_compact_convergence`: the compact-open topology is equal to the
   compact-convergence topology.
 * `compact_convergence_uniform_space`: the uniform space structure on `C(α, β)`.
 * `mem_compact_convergence_entourage_iff`: a characterisation of the entourages of `C(α, β)`.
 * `tendsto_iff_forall_compact_tendsto_uniformly_on`: a sequence of functions `Fₙ` in `C(α, β)`
   converges to some `f` iff `Fₙ` converges to `f` uniformly on each compact subset `K` of `α`.

## Implementation details

We use the forgetful inheritance pattern (see Note [forgetful inheritance]) to make the topology
of the uniform space structure on `C(α, β)` definitionally equal to the compact-open topology.

## TODO

 * When `α` is compact, the compact-convergence topology (and thus also the compact-open topology)
   is just the uniform-convergence topology.
 * When `β` is a metric space, there is natural basis for the compact-convergence topology
   parameterised by triples `(K, V, ε)` for a real number `ε > 0`.
 * When `α` is compact and `β` is a metric space, the compact-convergence topology (and thus also
   the compact-open topology) is metrisable.
 * Results about uniformly continuous functions `γ → C(α, β)` and uniform limits of sequences
   `ι → γ → C(α, β)`.
-/

universes u₁ u₂ u₃

open_locale filter uniformity topological_space
open uniform_space set filter

variables {α : Type u₁} {β : Type u₂} [topological_space α] [uniform_space β]
variables (K : set α) (V : set (β × β)) (f : C(α, β))

namespace continuous_map

/-- Given `K ⊆ α`, `V ⊆ β × β`, and `f : C(α, β)`, we define `compact_conv_nhd K V f` to be the set
of `g : C(α, β)` that are `V`-close to `f` on `K`. -/
def compact_conv_nhd : set C(α, β) := { g | ∀ (x ∈ K), (f x, g x) ∈ V }

variables {K V}

lemma self_mem_compact_conv_nhd (hV : V ∈ 𝓤 β) : f ∈ compact_conv_nhd K V f :=
λ x hx, refl_mem_uniformity hV

@[mono] lemma compact_conv_nhd_mono {V' : set (β × β)} (hV' : V' ⊆ V) :
  compact_conv_nhd K V' f ⊆ compact_conv_nhd K V f :=
λ x hx a ha, hV' (hx a ha)

lemma compact_conv_nhd_mem_comp {g₁ g₂ : C(α, β)} {V' : set (β × β)}
  (hg₁ : g₁ ∈ compact_conv_nhd K V f) (hg₂ : g₂ ∈ compact_conv_nhd K V' g₁) :
  g₂ ∈ compact_conv_nhd K (V ○ V') f :=
λ x hx, ⟨g₁ x, hg₁ x hx, hg₂ x hx⟩

/-- A key property of `compact_conv_nhd`. It allows us to apply
`topological_space.nhds_mk_of_nhds_filter_basis` below. -/
lemma compact_conv_nhd_nhd_basis (hV : V ∈ 𝓤 β) :
  ∃ (V' ∈ 𝓤 β), V' ⊆ V ∧ ∀ (g ∈ compact_conv_nhd K V' f),
    compact_conv_nhd K V' g ⊆ compact_conv_nhd K V f :=
begin
  obtain ⟨V', h₁, h₂⟩ := comp_mem_uniformity_sets hV,
  exact ⟨V', h₁, subset.trans (subset_comp_self_of_mem_uniformity h₁) h₂, λ g hg g' hg',
    compact_conv_nhd_mono f h₂ (compact_conv_nhd_mem_comp f hg hg')⟩,
end

lemma compact_conv_nhd_subset_inter (K₁ K₂ : set α) (V₁ V₂ : set (β × β)) :
  compact_conv_nhd (K₁ ∪ K₂) (V₁ ∩ V₂) f ⊆
  compact_conv_nhd K₁ V₁ f ∩ compact_conv_nhd K₂ V₂ f :=
λ g hg, ⟨λ x hx, mem_of_mem_inter_left (hg x (mem_union_left K₂ hx)),
         λ x hx, mem_of_mem_inter_right (hg x (mem_union_right K₁ hx))⟩

lemma compact_conv_nhd_compact_entourage_nonempty :
  { KV : set α × set (β × β) | is_compact KV.1 ∧ KV.2 ∈ 𝓤 β }.nonempty :=
⟨⟨∅, univ⟩, is_compact_empty, filter.univ_mem⟩

lemma compact_conv_nhd_filter_is_basis : filter.is_basis
  (λ (KV : set α × set (β × β)), is_compact KV.1 ∧ KV.2 ∈ 𝓤 β)
  (λ KV, compact_conv_nhd KV.1 KV.2 f) :=
{ nonempty := compact_conv_nhd_compact_entourage_nonempty,
  inter    :=
    begin
      rintros ⟨K₁, V₁⟩ ⟨K₂, V₂⟩ ⟨hK₁, hV₁⟩ ⟨hK₂, hV₂⟩,
      exact ⟨⟨K₁ ∪ K₂, V₁ ∩ V₂⟩, ⟨hK₁.union hK₂, filter.inter_mem hV₁ hV₂⟩,
        compact_conv_nhd_subset_inter f K₁ K₂ V₁ V₂⟩,
    end, }

/-- A filter basis for the neighbourhood filter of a point in the compact-convergence topology. -/
def compact_convergence_filter_basis (f : C(α, β)) : filter_basis C(α, β) :=
(compact_conv_nhd_filter_is_basis f).filter_basis

lemma mem_compact_convergence_nhd_filter (Y : set C(α, β)) :
  Y ∈ (compact_convergence_filter_basis f).filter ↔
  ∃ (K : set α) (V : set (β × β)) (hK : is_compact K) (hV : V ∈ 𝓤 β), compact_conv_nhd K V f ⊆ Y :=
begin
  split,
  { rintros ⟨X, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hY⟩,
    exact ⟨K, V, hK, hV, hY⟩, },
  { rintros ⟨K, V, hK, hV, hY⟩,
    exact ⟨compact_conv_nhd K V f, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hY⟩, },
end

/-- The compact-convergence topology. In fact, see `compact_open_eq_compact_convergence` this is
the same as the compact-open topology. This definition is thus an auxiliary convenience definition
and is unlikely to be of direct use. -/
def compact_convergence_topology : topological_space C(α, β) :=
topological_space.mk_of_nhds $ λ f, (compact_convergence_filter_basis f).filter

lemma nhds_compact_convergence :
  @nhds _ compact_convergence_topology f = (compact_convergence_filter_basis f).filter :=
begin
  rw topological_space.nhds_mk_of_nhds_filter_basis;
  rintros g - ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩,
  { exact self_mem_compact_conv_nhd g hV, },
  { obtain ⟨V', hV', h₁, h₂⟩ := compact_conv_nhd_nhd_basis g hV,
    exact ⟨compact_conv_nhd K V' g, ⟨⟨K, V'⟩, ⟨hK, hV'⟩, rfl⟩, compact_conv_nhd_mono g h₁,
      λ g' hg', ⟨compact_conv_nhd K V' g', ⟨⟨K, V'⟩, ⟨hK, hV'⟩, rfl⟩, h₂ g' hg'⟩⟩, },
end

lemma has_basis_nhds_compact_convergence :
  has_basis (@nhds _ compact_convergence_topology f)
  (λ (p : set α × set (β × β)), is_compact p.1 ∧ p.2 ∈ 𝓤 β) (λ p, compact_conv_nhd p.1 p.2 f) :=
(nhds_compact_convergence f).symm ▸ (compact_conv_nhd_filter_is_basis f).has_basis

/-- This is an auxiliary lemma and is unlikely to be of direct use outside of this file. See
`tendsto_iff_forall_compact_tendsto_uniformly_on` below for the useful version where the topology
is picked up via typeclass inference. -/
lemma tendsto_iff_forall_compact_tendsto_uniformly_on'
  {ι : Type u₃} {p : filter ι} {F : ι → C(α, β)} :
  filter.tendsto F p (@nhds _ compact_convergence_topology f) ↔
  ∀ K, is_compact K → tendsto_uniformly_on (λ i a, F i a) f p K :=
begin
  simp only [(has_basis_nhds_compact_convergence f).tendsto_right_iff, tendsto_uniformly_on,
    and_imp, prod.forall],
  refine forall_congr (λ K, _),
  rw forall_swap,
  exact forall_congr (λ hK, forall_congr (λ V, forall_congr (λ hV, iff.rfl))),
end

/-- Any point of `compact_open.gen K U` is also an interior point wrt the topology of compact
convergence.

The topology of compact convergence is thus at least as fine as the compact-open topology. -/
lemma compact_conv_nhd_subset_compact_open (hK : is_compact K) {U : set β} (hU : is_open U)
  (hf : f ∈ compact_open.gen K U) :
  ∃ (V ∈ 𝓤 β), is_open V ∧ compact_conv_nhd K V f ⊆ compact_open.gen K U :=
begin
  obtain ⟨V, hV₁, hV₂, hV₃⟩ := lebesgue_number_of_compact_open (hK.image f.continuous) hU hf,
  refine ⟨V, hV₁, hV₂, _⟩,
  rintros g hg - ⟨x, hx, rfl⟩,
  exact hV₃ (f x) ⟨x, hx, rfl⟩ (hg x hx),
end

/-- The point `f` in `compact_conv_nhd K V f` is also an interior point wrt the compact-open
topology.

Since `compact_conv_nhd K V f` are a neighbourhood basis at `f` for each `f`, it follows that
the compact-open topology is at least as fine as the topology of compact convergence. -/
lemma Inter_compact_open_gen_subset_compact_conv_nhd (hK : is_compact K) (hV : V ∈ 𝓤 β) :
  ∃ (ι : Sort (u₁ + 1)) [fintype ι]
  (C : ι → set α) (hC : ∀ i, is_compact (C i))
  (U : ι → set β) (hU : ∀ i, is_open (U i)),
  (f ∈ ⋂ i, compact_open.gen (C i) (U i)) ∧
  (⋂ i, compact_open.gen (C i) (U i)) ⊆ compact_conv_nhd K V f :=
begin
  obtain ⟨W, hW₁, hW₄, hW₂, hW₃⟩ := comp_open_symm_mem_uniformity_sets hV,
  obtain ⟨Z, hZ₁, hZ₄, hZ₂, hZ₃⟩ := comp_open_symm_mem_uniformity_sets hW₁,
  let U : α → set α := λ x, f⁻¹' (ball (f x) Z),
  have hU : ∀ x, is_open (U x) := λ x, f.continuous.is_open_preimage _ (is_open_ball _ hZ₄),
  have hUK : K ⊆ ⋃ (x : K), U (x : K),
  { intros x hx,
    simp only [exists_prop, mem_Union, Union_coe_set, mem_preimage],
    exact ⟨(⟨x, hx⟩ : K), by simp [hx, mem_ball_self (f x) hZ₁]⟩, },
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover _ (λ (x : K), hU x.val) hUK,
  let C : t → set α := λ i, K ∩ closure (U ((i : K) : α)),
  have hC : K ⊆ ⋃ i, C i,
  { rw [← K.inter_Union, subset_inter_iff],
    refine ⟨rfl.subset, ht.trans _⟩,
    simp only [set_coe.forall, subtype.coe_mk, Union_subset_iff],
    exact λ x hx₁ hx₂, subset_subset_Union (⟨_, hx₂⟩ : t) (by simp [subset_closure]), },
  have hfC : ∀ (i : t), C i ⊆ f ⁻¹' ball (f ((i : K) : α)) W,
  { simp only [← image_subset_iff, ← mem_preimage],
    rintros ⟨⟨x, hx₁⟩, hx₂⟩,
    have hZW : closure (ball (f x) Z) ⊆ ball (f x) W,
    { intros y hy,
      obtain ⟨z, hz₁, hz₂⟩ := uniform_space.mem_closure_iff_ball.mp hy hZ₁,
      exact ball_mono hZ₃ _ (mem_ball_comp hz₂ ((mem_ball_symmetry hZ₂).mp hz₁)), },
    calc f '' (K ∩ closure (U x)) ⊆ f '' (closure (U x)) : image_subset _ (inter_subset_right _ _)
                              ... ⊆ closure (f '' (U x)) : f.continuous.continuous_on.image_closure
                              ... ⊆ closure (ball (f x) Z) : by { apply closure_mono, simp, }
                              ... ⊆ ball (f x) W : hZW, },
  refine ⟨t, t.fintype_coe_sort, C,
          λ i, hK.inter_right is_closed_closure,
          λ i, ball (f ((i : K) : α)) W,
          λ i, is_open_ball _ hW₄,
          by simp [compact_open.gen, hfC],
          λ g hg x hx, hW₃ (mem_comp_rel.mpr _)⟩,
  simp only [mem_Inter, compact_open.gen, mem_set_of_eq, image_subset_iff] at hg,
  obtain ⟨y, hy⟩ := mem_Union.mp (hC hx),
  exact ⟨f y, (mem_ball_symmetry hW₂).mp (hfC y hy), mem_preimage.mp (hg y hy)⟩,
end

/-- The compact-open topology is equal to the compact-convergence topology. -/
lemma compact_open_eq_compact_convergence :
  continuous_map.compact_open = (compact_convergence_topology : topological_space C(α, β)) :=
begin
  rw [compact_convergence_topology, continuous_map.compact_open],
  refine le_antisymm _ _,
  { refine λ X hX, is_open_iff_forall_mem_open.mpr (λ f hf, _),
    have hXf : X ∈ (compact_convergence_filter_basis f).filter,
    { rw ← nhds_compact_convergence,
      exact @is_open.mem_nhds C(α, β) compact_convergence_topology _ _ hX hf, },
    obtain ⟨-, ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩, hXf⟩ := hXf,
    obtain ⟨ι, hι, C, hC, U, hU, h₁, h₂⟩ := Inter_compact_open_gen_subset_compact_conv_nhd f hK hV,
    haveI := hι,
    exact ⟨⋂ i, compact_open.gen (C i) (U i), h₂.trans hXf,
      is_open_Inter (λ i, continuous_map.is_open_gen (hC i) (hU i)), h₁⟩, },
  { simp only [le_generate_from_iff_subset_is_open, and_imp, exists_prop, forall_exists_index,
      set_of_subset_set_of],
    rintros - K hK U hU rfl f hf,
    obtain ⟨V, hV, hV', hVf⟩ := compact_conv_nhd_subset_compact_open f hK hU hf,
    exact filter.mem_of_superset (filter_basis.mem_filter_of_mem _ ⟨⟨K, V⟩, ⟨hK, hV⟩, rfl⟩) hVf, },
end

/-- The filter on `C(α, β) × C(α, β)` which underlies the uniform space structure on `C(α, β)`. -/
def compact_convergence_uniformity : filter (C(α, β) × C(α, β)) :=
⨅ KV ∈ { KV : set α × set (β × β) | is_compact KV.1 ∧ KV.2 ∈ 𝓤 β },
𝓟 { fg : C(α, β) × C(α, β) | ∀ (x : α), x ∈ KV.1 → (fg.1 x, fg.2 x) ∈ KV.2 }

/-- An intermediate lemma. Usually `mem_compact_convergence_entourage_iff` is more useful. -/
lemma mem_compact_convergence_uniformity (X : set (C(α, β) × C(α, β))) :
  X ∈ @compact_convergence_uniformity α β _ _ ↔
  ∃ (K : set α) (V : set (β × β)) (hK : is_compact K) (hV : V ∈ 𝓤 β),
    { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X :=
begin
  rw [compact_convergence_uniformity,
    (filter.has_basis_binfi_principal _ compact_conv_nhd_compact_entourage_nonempty).mem_iff],
  { simp only [exists_prop, prod.forall, set_of_subset_set_of, mem_set_of_eq, prod.exists],
    exact exists_congr (λ K, exists_congr (λ V, by tauto)), },
  { rintros ⟨K₁, V₁⟩ ⟨hK₁, hV₁⟩ ⟨K₂, V₂⟩ ⟨hK₂, hV₂⟩,
    refine ⟨⟨K₁ ∪ K₂, V₁ ∩ V₂⟩, ⟨hK₁.union hK₂, filter.inter_mem hV₁ hV₂⟩, _⟩,
    simp only [le_eq_subset, prod.forall, set_of_subset_set_of, ge_iff_le, order.preimage,
      ← forall_and_distrib, mem_inter_eq, mem_union_eq],
    exact λ f g, forall_imp (λ x, by tauto!), },
end

/-- Note that we ensure the induced topology is definitionally the compact-open topology. -/
instance compact_convergence_uniform_space : uniform_space C(α, β) :=
{ uniformity := compact_convergence_uniformity,
  refl :=
    begin
      simp only [compact_convergence_uniformity, and_imp, filter.le_principal_iff, prod.forall,
        filter.mem_principal, mem_set_of_eq, le_infi_iff, id_rel_subset],
      exact λ K V hK hV f x hx, refl_mem_uniformity hV,
    end,
  symm :=
    begin
      simp only [compact_convergence_uniformity, and_imp, prod.forall, mem_set_of_eq, prod.fst_swap,
        filter.tendsto_principal, prod.snd_swap, filter.tendsto_infi],
      intros K V hK hV,
      obtain ⟨V', hV', hsymm, hsub⟩ := symm_of_uniformity hV,
      let X := { fg : C(α, β) × C(α, β) | ∀ (x : α), x ∈ K → (fg.1 x, fg.2 x) ∈ V' },
      have hX : X ∈ compact_convergence_uniformity :=
        (mem_compact_convergence_uniformity X).mpr ⟨K, V', hK, hV', by simp⟩,
      exact filter.eventually_of_mem hX (λ fg hfg x hx, hsub (hsymm _ _ (hfg x hx))),
    end,
  comp := λ X hX,
    begin
      obtain ⟨K, V, hK, hV, hX⟩ := (mem_compact_convergence_uniformity X).mp hX,
      obtain ⟨V', hV', hcomp⟩ := comp_mem_uniformity_sets hV,
      let h := λ (s : set (C(α, β) × C(α, β))), s ○ s,
      suffices : h {fg : C(α, β) × C(α, β) | ∀ (x ∈ K), (fg.1 x, fg.2 x) ∈ V'} ∈
                 compact_convergence_uniformity.lift' h,
      { apply filter.mem_of_superset this,
        rintros ⟨f, g⟩ ⟨z, hz₁, hz₂⟩,
        refine hX (λ x hx, hcomp _),
        exact ⟨z x, hz₁ x hx, hz₂ x hx⟩, },
      apply filter.mem_lift',
      exact (mem_compact_convergence_uniformity _).mpr ⟨K, V', hK, hV', subset.refl _⟩,
    end,
  is_open_uniformity :=
    begin
      rw compact_open_eq_compact_convergence,
      refine λ Y, forall_congr (λ f, forall_congr (λ hf, _)),
      simp only [mem_compact_convergence_nhd_filter, mem_compact_convergence_uniformity,
        prod.forall, set_of_subset_set_of, compact_conv_nhd],
      refine exists_congr (λ K, exists_congr (λ V, exists_congr (λ hK, exists_congr (λ hV, _)))),
      refine ⟨_, λ hY g hg, hY f g hg rfl⟩,
      rintros hY g₁ g₂ hg₁ rfl,
      exact hY hg₁,
    end }

lemma mem_compact_convergence_entourage_iff (X : set (C(α, β) × C(α, β))) :
  X ∈ 𝓤 C(α, β) ↔ ∃ (K : set α) (V : set (β × β)) (hK : is_compact K) (hV : V ∈ 𝓤 β),
    { fg : C(α, β) × C(α, β) | ∀ x ∈ K, (fg.1 x, fg.2 x) ∈ V } ⊆ X :=
mem_compact_convergence_uniformity X

lemma has_basis_compact_convergence_uniformity :
  has_basis (𝓤 C(α, β)) (λ p : set α × set (β × β), is_compact p.1 ∧ p.2 ∈ 𝓤 β)
            (λ p, { fg : C(α, β) × C(α, β) | ∀ x ∈ p.1, (fg.1 x, fg.2 x) ∈ p.2 }) :=
⟨λ t, by { simp only [mem_compact_convergence_entourage_iff, prod.exists], tauto, }⟩

lemma tendsto_iff_forall_compact_tendsto_uniformly_on
  {ι : Type u₃} {p : filter ι} {F : ι → C(α, β)} :
  filter.tendsto F p (𝓝 f) ↔ ∀ K, is_compact K → tendsto_uniformly_on (λ i a, F i a) f p K :=
by rw [compact_open_eq_compact_convergence, tendsto_iff_forall_compact_tendsto_uniformly_on']

end continuous_map

/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import topology.subset_properties
import topology.metric_space.basic

/-!
# Sequences in topological spaces

In this file we define sequences in topological spaces and show how they are related to
filters and the topology. In particular, we
* define the sequential closure of a set and prove that it's contained in the closure,
* define a type class "sequential_space" in which closure and sequential closure agree,
* define sequential continuity and show that it coincides with continuity in sequential spaces,
* provide an instance that shows that every first-countable (and in particular metric) space is
  a sequential space.
* define sequential compactness, prove that compactness implies sequential compactness in first
  countable spaces, and prove they are equivalent for uniform spaces having a countable uniformity
  basis (in particular metric spaces).
-/

open set function filter bornology
open_locale topological_space filter

variables {α : Type*} {β : Type*}

local notation x ` ⟶ ` p := tendsto x at_top (𝓝 p)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space α] [topological_space β]

/-- The sequential closure of a set `s : set α` in a topological space `α` is the set of all `p ∈ α`
which arise as limit of sequences in `s`. Note that it does not need to be sequentially closed. -/
def seq_closure (s : set α) : set α :=
{p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ (x ⟶ p)}

lemma subset_seq_closure {s : set α} : s ⊆ seq_closure s :=
λ p hp, ⟨const ℕ p, λ _, hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma seq_closure_subset_closure {s : set α} : seq_closure s ⊆ closure s :=
λ p ⟨x, xM, xp⟩, mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set α) : Prop :=
∀ ⦃x : ℕ → α⦄ ⦃p : α⦄, (∀ n, x n ∈ s) → (x ⟶ p) → p ∈ s

/-- The sequential closure of a sequentially closed set is the set itself. -/
lemma is_seq_closed.seq_closure_eq {s : set α} (hs : is_seq_closed s) :
  seq_closure s = s :=
subset.antisymm (λ p ⟨x, hx, hp⟩, hs hx hp) subset_seq_closure

/-- A set is sequentially closed if it is closed. -/
protected lemma is_closed.is_seq_closed {s : set α} (hc : is_closed s) : is_seq_closed s :=
λ u x hu hx, hc.mem_of_tendsto hx (eventually_of_forall hu)

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type*) [topological_space α] : Prop :=
(is_closed_of_seq : ∀ s : set α, is_seq_closed s → is_closed s)

/-- In a sequential space, a sequentially closed set is closed. -/
protected lemma is_seq_closed.is_closed [sequential_space α] {s : set α} (hs : is_seq_closed s) :
  is_closed s :=
sequential_space.is_closed_of_seq s hs

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space α] {M : set α} :
  is_seq_closed M ↔ is_closed M :=
⟨is_seq_closed.is_closed, is_closed.is_seq_closed⟩

/-
TODO: add Fréchet-Urysohn spaces and this lemma?
lemma tendsto_nhds_iff_seq_tendsto [frechet_urysohn_space α] {f : α → β} {a : α} {b : β} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → α, (u ⟶ a) → (f ∘ u ⟶ b) :=
begin
  refine ⟨λ hf u hu, hf.comp hu,
    λ h, ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 _⟩,
  rintro s ⟨hbs, hsc⟩,
  refine ⟨closure (f ⁻¹' s), ⟨mt _ hbs, is_closed_closure⟩, λ x, mt $ λ hx, subset_closure hx⟩,
  rw [← sequential_space.sequential_closure_eq_closure],
  rintro ⟨u, hus, hu⟩,
  exact hsc.mem_of_tendsto (h u hu) (eventually_of_forall hus)
end
-/

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def seq_continuous (f : α → β) : Prop :=
∀ ⦃x : ℕ → α⦄ ⦃p : α⦄, (x ⟶ p) → (f ∘ x ⟶ f p)

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
lemma is_seq_closed.preimage {f : α → β} {s : set β} (hs : is_seq_closed s)
  (hf : seq_continuous f) :
  is_seq_closed (f ⁻¹' s) :=
λ x p hx hp, hs hx (hf hp)

/- A continuous function is sequentially continuous. -/
protected lemma continuous.seq_continuous {f : α → β} (hf : continuous f) :
  seq_continuous f :=
λ x p hx, (hf.tendsto p).comp hx

/-- A sequentially continuous function defined on a sequential space is continuous. -/
protected lemma seq_continuous.continuous [sequential_space α] {f : α → β} (hf : seq_continuous f) :
  continuous f :=
continuous_iff_is_closed.mpr $ λ s hs, (hs.is_seq_closed.preimage hf).is_closed

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
lemma continuous_iff_seq_continuous [sequential_space α] {f : α → β} :
  continuous f ↔ seq_continuous f :=
⟨continuous.seq_continuous, seq_continuous.continuous⟩

end topological_space

namespace topological_space

namespace first_countable_topology

variables [topological_space α] [first_countable_topology α]

/-- Every first-countable space is sequential. -/
@[priority 100] -- see Note [lower instance priority]
instance : sequential_space α :=
begin
  -- Consider a closed set `s`
  refine ⟨λ s hs, _⟩,
  -- It suffices to show that `s` contains every cluster point of `𝓟 s`.
  -- Consider a cluster point `p` of `s`.
  refine is_closed_iff_cluster_pt.mpr (λ p hp, _),
  haveI := hp.ne_bot,
  -- Fix an antitone basis `U : ℕ → set α` of `𝓝 p`, then choose a sequence `x : ℕ → α` such that
  -- `x n ∈ U n ∩ s`.
  rcases exists_antitone_basis (𝓝 p) with ⟨U, hU⟩,
  have : ∀ n, (U n ∩ s).nonempty,
    from λ n, filter.nonempty_of_mem ((hU.to_has_basis.inf_principal _).mem_of_mem trivial),
  choose x hxU hxs,
  -- Then `x ⟶ p`, thus `p ∈ s`
  exact hs hxs (hU.tendsto hxU)
end


end first_countable_topology

end topological_space

section seq_compact
open topological_space topological_space.first_countable_topology
variables [topological_space α]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def is_seq_compact (s : set α) :=
∀ ⦃u : ℕ → α⦄, (∀ n, u n ∈ s) → ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x)

/-- A space `α` is sequentially compact if every sequence in `α` has a
converging subsequence. -/
class seq_compact_space (α : Type*) [topological_space α] : Prop :=
(seq_compact_univ : is_seq_compact (univ : set α))

lemma is_seq_compact.subseq_of_frequently_in {s : set α} (hs : is_seq_compact s) {u : ℕ → α}
  (hu : ∃ᶠ n in at_top, u n ∈ s) :
  ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hu, ⟨x, x_in, φ, hφ, h⟩ := hs huψ in
⟨x, x_in, ψ ∘ φ, hψ.comp hφ, h⟩

lemma seq_compact_space.tendsto_subseq [seq_compact_space α] (u : ℕ → α) :
  ∃ x (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
let ⟨x, _, φ, mono, h⟩ := seq_compact_space.seq_compact_univ (λ n, mem_univ (u n)) in
⟨x, φ, mono, h⟩

section first_countable_topology
variables [first_countable_topology α]
open topological_space.first_countable_topology

protected lemma is_compact.is_seq_compact {s : set α} (hs : is_compact s) : is_seq_compact s :=
λ u u_in,
let ⟨x, x_in, hx⟩ := @hs (map u at_top) _ (le_principal_iff.mpr (mem_map.2 $ univ_mem' u_in))
in ⟨x, x_in, tendsto_subseq hx⟩

lemma is_compact.tendsto_subseq' {s : set α} {u : ℕ → α} (hs : is_compact s)
  (hu : ∃ᶠ n in at_top, u n ∈ s) :
  ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
hs.is_seq_compact.subseq_of_frequently_in hu

lemma is_compact.tendsto_subseq {s : set α} {u : ℕ → α} (hs : is_compact s) (hu : ∀ n, u n ∈ s) :
  ∃ (x ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
hs.is_seq_compact hu

@[priority 100] -- see Note [lower instance priority]
instance first_countable_topology.seq_compact_of_compact [compact_space α] : seq_compact_space α :=
⟨compact_univ.is_seq_compact⟩

lemma compact_space.tendsto_subseq [compact_space α] (u : ℕ → α) :
  ∃ x (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 x) :=
seq_compact_space.tendsto_subseq u

end first_countable_topology
end seq_compact

section uniform_space_seq_compact

open_locale uniformity
open uniform_space prod

variables [uniform_space β] {s : set β}

lemma is_seq_compact.exists_tendsto_of_frequently_mem (hs : is_seq_compact s) {u : ℕ → β}
  (hu : ∃ᶠ n in at_top, u n ∈ s) (huc : cauchy_seq u) :
  ∃ x ∈ s, u ⟶ x :=
begin
  rcases hs.subseq_of_frequently_in hu with ⟨x, hxs, φ, φ_mono, hx⟩,
  refine ⟨x, hxs, le_nhds_of_cauchy_adhp huc ((cluster_pt.of_le_nhds hx).mono _)⟩,
  rw [← filter.map_map],
  exact map_mono φ_mono.tendsto_at_top
end

lemma is_seq_compact.exists_tendsto (hs : is_seq_compact s) {u : ℕ → β} (hu : ∀ n, u n ∈ s)
  (huc : cauchy_seq u) : ∃ x ∈ s, u ⟶ x :=
hs.exists_tendsto_of_frequently_mem (frequently_of_forall hu) huc

/-- A sequentially compact set in a uniform space is totally bounded. -/
protected lemma is_seq_compact.totally_bounded (h : is_seq_compact s) : totally_bounded s :=
begin
  intros V V_in,
  unfold is_seq_compact at h,
  contrapose! h,
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → β, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V,
  { simp only [not_subset, mem_Union₂, not_exists, exists_prop] at h,
    simpa only [forall_and_distrib, ball_image_iff, not_and] using seq_of_forall_finite_exists h },
  refine ⟨u, u_in, λ x x_in φ hφ huφ, _⟩,
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V,
    from huφ.cauchy_seq.mem_entourage V_in,
  exact hu (φ $ N + 1) (φ N) (hφ $ lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)
end

variables [is_countably_generated (𝓤 β)]

/-- A sequentially compact set in a uniform set with countably generated uniformity filter
is complete. -/
protected lemma is_seq_compact.is_complete (hs : is_seq_compact s) : is_complete s :=
begin
  intros l hl hls,
  haveI := hl.1,
  have H₂ : l ×ᶠ l ≤ 𝓤 β ⊓ 𝓟 (s ×ˢ s),
  { rw ← prod_principal_principal,
    exact le_inf hl.2 (prod_mono hls hls) },
  rcases exists_antitone_basis (𝓤 β) with ⟨V, hV⟩,
  choose W hW hWV using λ n, comp_mem_uniformity_sets (hV.mem n),
  obtain ⟨t, ht_anti, htl, htW, htV, hts⟩ : ∃ t : ℕ → set β, antitone t ∧ (∀ n, t n ∈ l) ∧
    (∀ n, t n ×ˢ t n ⊆ W n) ∧ (∀ n, t n ×ˢ t n ⊆ V n) ∧ (∀ n, t n ⊆ s),
  { have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ×ˢ t ⊆ V n ∧ t ⊆ s,
    { simpa only [l.basis_sets.prod_self.mem_iff, true_implies_iff, subset_inter_iff,
        prod_self_subset_prod_self, and.assoc]
        using λ n, H₂ (inter_mem_inf (inter_mem (hW n) (hV.mem n)) subset.rfl) },
    choose t htl htW htV hts,
    have : ∀ n, (⋂ k ≤ n, t k) ⊆ t n, from λ n, Inter₂_subset _ le_rfl,
    exact ⟨λ n, ⋂ k ≤ n, t k, λ m n h, bInter_subset_bInter_left (λ k (hk : k ≤ m), hk.trans h),
      λ n, (bInter_mem (finite_le_nat n)).2 (λ k hk, htl k),
      λ n, (prod_mono (this n) (this n)).trans (htW n),
      λ n, (prod_mono (this n) (this n)).trans (htV n), λ n, (this n).trans (hts n)⟩ },
  choose u hu using λ n, filter.nonempty_of_mem (htl n),
  have huc : cauchy_seq u,
    from hV.to_has_basis.cauchy_seq_iff.2
      (λ N hN, ⟨N, λ m hm n hn, htV N (mk_mem_prod (ht_anti hm (hu _)) (ht_anti hn (hu _)))⟩),
  rcases hs.exists_tendsto (λ n, hts n (hu n)) huc with ⟨x, hxs, hx⟩,
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.to_has_basis).ge_iff.2 $ λ N hN, _⟩,
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N),
    from ((eventually_ge_at_top N).and (hx $ ball_mem_nhds x (hW N))).exists,
  refine mem_of_superset (htl n) (λ y hy, hWV N ⟨u n, _, htW N ⟨_, _⟩⟩),
  exacts [hn, ht_anti hNn (hu n), ht_anti hNn hy]
end

/-- If `𝓤 β` is countably generated, then any sequentially compact set is compact. -/
protected lemma is_seq_compact.is_compact (hs : is_seq_compact s) : is_compact s :=
compact_iff_totally_bounded_complete.2 ⟨hs.totally_bounded, hs.is_complete⟩

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected lemma uniform_space.compact_iff_seq_compact : is_compact s ↔ is_seq_compact s :=
⟨λ H, H.is_seq_compact, λ H, H.is_compact⟩

lemma uniform_space.compact_space_iff_seq_compact_space : compact_space β ↔ seq_compact_space β :=
have key : is_compact (univ : set β) ↔ is_seq_compact univ := uniform_space.compact_iff_seq_compact,
⟨λ ⟨h⟩, ⟨key.mp h⟩, λ ⟨h⟩, ⟨key.mpr h⟩⟩

end uniform_space_seq_compact

section metric_seq_compact

variables [metric_space β] {s : set β}
open metric

/-- A version of **Bolzano-Weistrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
lemma tendsto_subseq_of_frequently_bounded [proper_space β] (hs : bounded s)
  {u : ℕ → β} (hu : ∃ᶠ n in at_top, u n ∈ s) :
  ∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
have hcs : is_seq_compact (closure s), from hs.is_compact_closure.is_seq_compact,
have hu' : ∃ᶠ n in at_top, u n ∈ closure s, from hu.mono (λ n hn, subset_closure hn),
hcs.subseq_of_frequently_in hu'

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
lemma tendsto_subseq_of_bounded [proper_space β] (hs : bounded s)
  {u : ℕ → β} (hu : ∀ n, u n ∈ s) :
  ∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
tendsto_subseq_of_frequently_bounded hs $ frequently_of_forall hu

end metric_seq_compact

/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot
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

open set filter bornology
open_locale topological_space filter

variables {α : Type*} {β : Type*}

local notation f ` ⟶ ` limit := tendsto f at_top (𝓝 limit)

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space α] [topological_space β]

/-- A sequence converges in the sence of topological spaces iff the associated statement for filter
holds. -/
lemma topological_space.seq_tendsto_iff {x : ℕ → α} {limit : α} :
  tendsto x at_top (𝓝 limit) ↔
    ∀ U : set α, limit ∈ U → is_open U → ∃ N, ∀ n ≥ N, (x n) ∈ U :=
(at_top_basis.tendsto_iff (nhds_basis_opens limit)).trans $
  by simp only [and_imp, exists_prop, true_and, set.mem_Ici, ge_iff_le, id]

/-- The sequential closure of a subset M ⊆ α of a topological space α is
the set of all p ∈ α which arise as limit of sequences in M. -/
def sequential_closure (M : set α) : set α :=
{p | ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ M) ∧ (x ⟶ p)}

lemma subset_sequential_closure (M : set α) : M ⊆ sequential_closure M :=
assume p (_ : p ∈ M), show p ∈ sequential_closure M, from
  ⟨λ n, p, assume n, ‹p ∈ M›, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set α) : Prop := s = sequential_closure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {A : set α}
  (h : ∀(x : ℕ → α) (p : α), (∀ n : ℕ, x n ∈ A) → (x ⟶ p) → p ∈ A) : is_seq_closed A :=
show A = sequential_closure A, from subset.antisymm
  (subset_sequential_closure A)
  (show ∀ p, p ∈ sequential_closure A → p ∈ A, from
    (assume p ⟨x, _, _⟩, show p ∈ A, from h x p ‹∀ n : ℕ, ((x n) ∈ A)› ‹(x ⟶ p)›))

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma sequential_closure_subset_closure (M : set α) : sequential_closure M ⊆ closure M :=
assume p ⟨x, xM, xp⟩,
mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set is sequentially closed if it is closed. -/
lemma is_seq_closed_of_is_closed (M : set α) (_ : is_closed M) : is_seq_closed M :=
suffices sequential_closure M ⊆ M, from
  set.eq_of_subset_of_subset (subset_sequential_closure M) this,
calc sequential_closure M ⊆ closure M : sequential_closure_subset_closure M
  ... = M : is_closed.closure_eq ‹is_closed M›

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma mem_of_is_seq_closed {A : set α} (_ : is_seq_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : (x ⟶ limit)) : limit ∈ A :=
have limit ∈ sequential_closure A, from
  show ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ A) ∧ (x ⟶ limit), from ⟨x, ‹∀ n, x n ∈ A›, ‹(x ⟶ limit)›⟩,
eq.subst (eq.symm ‹is_seq_closed A›) ‹limit ∈ sequential_closure A›

/-- The limit of a convergent sequence in a closed set is in that set.-/
lemma mem_of_is_closed_sequential {A : set α} (_ : is_closed A) {x : ℕ → α}
  (_ : ∀ n, x n ∈ A) {limit : α} (_ : x ⟶ limit) : limit ∈ A :=
mem_of_is_seq_closed (is_seq_closed_of_is_closed A ‹is_closed A›) ‹∀ n, x n ∈ A› ‹(x ⟶ limit)›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (α : Type*) [topological_space α] : Prop :=
(sequential_closure_eq_closure : ∀ M : set α, sequential_closure M = closure M)

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space α] {M : set α} :
  is_seq_closed M ↔ is_closed M :=
iff.intro
  (assume _, closure_eq_iff_is_closed.mp (eq.symm
    (calc M = sequential_closure M : by assumption
        ... = closure M            : sequential_space.sequential_closure_eq_closure M)))
  (is_seq_closed_of_is_closed M)

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
lemma mem_closure_iff_seq_limit [sequential_space α] {s : set α} {a : α} :
  a ∈ closure s ↔ ∃ x : ℕ → α, (∀ n : ℕ, x n ∈ s) ∧ (x ⟶ a) :=
by { rw ← sequential_space.sequential_closure_eq_closure, exact iff.rfl }

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def sequentially_continuous (f : α → β) : Prop :=
∀ (x : ℕ → α), ∀ {limit : α}, (x ⟶ limit) → (f∘x ⟶ f limit)

/- A continuous function is sequentially continuous. -/
lemma continuous.to_sequentially_continuous {f : α → β} (_ : continuous f) :
  sequentially_continuous f :=
assume x limit (_ : x ⟶ limit),
have tendsto f (𝓝 limit) (𝓝 (f limit)), from continuous.tendsto ‹continuous f› limit,
show (f ∘ x) ⟶ (f limit), from tendsto.comp this ‹(x ⟶ limit)›

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma continuous_iff_sequentially_continuous {f : α → β} [sequential_space α] :
  continuous f ↔ sequentially_continuous f :=
iff.intro
  (assume _, ‹continuous f›.to_sequentially_continuous)
  (assume : sequentially_continuous f, show continuous f, from
    suffices h : ∀ {A : set β}, is_closed A → is_seq_closed (f ⁻¹' A), from
      continuous_iff_is_closed.mpr (assume A _, is_seq_closed_iff_is_closed.mp $ h ‹is_closed A›),
    assume A (_ : is_closed A),
      is_seq_closed_of_def $
        assume (x : ℕ → α) p (_ : ∀ n, f (x n) ∈ A) (_ : x ⟶ p),
        have (f ∘ x) ⟶ (f p), from ‹sequentially_continuous f› x ‹(x ⟶ p)›,
        show f p ∈ A, from
          mem_of_is_closed_sequential ‹is_closed A› ‹∀ n, f (x n) ∈ A› ‹(f∘x ⟶ f p)›)

end topological_space

namespace topological_space

namespace first_countable_topology

variables [topological_space α] [first_countable_topology α]

/-- Every first-countable space is sequential. -/
@[priority 100] -- see Note [lower instance priority]
instance : sequential_space α :=
⟨show ∀ M, sequential_closure M = closure M, from assume M,
  suffices closure M ⊆ sequential_closure M,
    from set.subset.antisymm (sequential_closure_subset_closure M) this,
  -- For every p ∈ closure M, we need to construct a sequence x in M that converges to p:
  assume (p : α) (hp : p ∈ closure M),
  -- Since we are in a first-countable space, the neighborhood filter around `p` has a decreasing
  -- basis `U` indexed by `ℕ`.
  let ⟨U, hU⟩ := (𝓝 p).exists_antitone_basis in
  -- Since `p ∈ closure M`, there is an element in each `M ∩ U i`
  have hp : ∀ (i : ℕ), ∃ (y : α), y ∈ M ∧ y ∈ U i,
    by simpa using (mem_closure_iff_nhds_basis hU.1).mp hp,
  begin
    -- The axiom of (countable) choice builds our sequence from the later fact
    choose u hu using hp,
    rw forall_and_distrib at hu,
    -- It clearly takes values in `M`
    use [u, hu.1],
    -- and converges to `p` because the basis is decreasing.
    apply hU.tendsto hu.2,
  end⟩


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

lemma is_seq_compact.exists_tendsto_of_frequently_mem {s : set β} (hs : is_seq_compact s)
  {u : ℕ → β} (hu : ∃ᶠ n in at_top, u n ∈ s) (huc : cauchy_seq u) :
  ∃ x ∈ s, u ⟶ x :=
begin
  rcases hs.subseq_of_frequently_in hu with ⟨x, hxs, φ, φ_mono, hx⟩,
  refine ⟨x, hxs, le_nhds_of_cauchy_adhp huc ((cluster_pt.of_le_nhds hx).mono _)⟩,
  rw [← filter.map_map],
  exact map_mono φ_mono.tendsto_at_top
end

lemma is_seq_compact.exists_tendsto {s : set β} (hs : is_seq_compact s) {u : ℕ → β}
  (hu : ∀ n, u n ∈ s) (huc : cauchy_seq u) :
  ∃ x ∈ s, u ⟶ x :=
hs.exists_tendsto_of_frequently_mem (frequently_of_forall hu) huc

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

protected lemma is_seq_compact.is_complete [is_countably_generated $ 𝓤 β] (hs : is_seq_compact s) :
  is_complete s :=
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


protected lemma is_seq_compact.is_compact [is_countably_generated $ 𝓤 β] (hs : is_seq_compact s) :
  is_compact s :=
compact_iff_totally_bounded_complete.2 ⟨hs.totally_bounded, hs.is_complete⟩

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected lemma uniform_space.compact_iff_seq_compact [is_countably_generated $ 𝓤 β] :
 is_compact s ↔ is_seq_compact s :=
⟨λ H, H.is_seq_compact, λ H, H.is_compact⟩

lemma uniform_space.compact_space_iff_seq_compact_space [is_countably_generated $ 𝓤 β] :
  compact_space β ↔ seq_compact_space β :=
have key : is_compact (univ : set β) ↔ is_seq_compact univ := uniform_space.compact_iff_seq_compact,
⟨λ ⟨h⟩, ⟨key.mp h⟩, λ ⟨h⟩, ⟨key.mpr h⟩⟩

end uniform_space_seq_compact

section metric_seq_compact

variables [metric_space β] {s : set β}
open metric

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
lemma tendsto_subseq_of_frequently_bounded [proper_space β] (hs : is_bounded s)
  {u : ℕ → β} (hu : ∃ᶠ n in at_top, u n ∈ s) :
  ∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
begin
  have hcs : is_compact (closure s) :=
    compact_iff_closed_bounded.mpr ⟨is_closed_closure, hs.closure⟩,
  replace hcs : is_seq_compact (closure s), from hcs.is_seq_compact,
  have hu' : ∃ᶠ n in at_top, u n ∈ closure s,
    from hu.mono (λ n hn, subset_closure hn),
  exact hcs.subseq_of_frequently_in hu',
end

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
lemma tendsto_subseq_of_bounded [proper_space β] (hs : is_bounded s)
  {u : ℕ → β} (hu : ∀ n, u n ∈ s) :
  ∃ b ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 b) :=
tendsto_subseq_of_frequently_bounded hs $ frequently_of_forall hu

lemma seq_compact.lebesgue_number_lemma_of_metric
  {ι : Type*} {c : ι → set β} (hs : is_seq_compact s)
  (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ x ∈ s, ∃ i, ball x δ ⊆ c i :=
lebesgue_number_lemma_of_metric hs.is_compact hc₁ hc₂

end metric_seq_compact

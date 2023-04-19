/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
import topology.subset_properties
import topology.metric_space.basic

/-!
# Sequences in topological spaces

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define sequences in topological spaces and show how they are related to
filters and the topology.

## Main definitions

### Set operation
* `seq_closure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `is_seq_closed s`: predicate saying that a set is sequentially closed, i.e., `seq_closure s ⊆ s`;
* `seq_continuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `is_seq_compact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `frechet_urysohn_space X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `sequential_space X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `seq_compact_space X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seq_closure_subset_closure`: closure of a set includes its sequential closure;
* `is_closed.is_seq_closed`: a closed set is sequentially closed;
* `is_seq_closed.seq_closure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seq_closure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `frechet_urysohn_space.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `topological_space.first_countable_topology.frechet_urysohn_space`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `frechet_urysohn_space.to_sequential_space`: every Fréchet-Urysohn space is a sequential space;
* `is_seq_compact.is_compact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/

open set function filter topological_space
open_locale topology filter

variables {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space X] [topological_space Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is the set of all `a : X`
which arise as limit of sequences in `s`. Note that the sequential closure of a set is not
guaranteed to be sequentially closed. -/
def seq_closure (s : set X) : set X :=
{a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ tendsto x at_top (𝓝 a)}

lemma subset_seq_closure {s : set X} : s ⊆ seq_closure s :=
λ p hp, ⟨const ℕ p, λ _, hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma seq_closure_subset_closure {s : set X} : seq_closure s ⊆ closure s :=
λ p ⟨x, xM, xp⟩, mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`, the
limit belongs to `s` as well. Note that the sequential closure of a set is not guaranteed to be
sequentially closed. -/
def is_seq_closed (s : set X) : Prop :=
∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → tendsto x at_top (𝓝 p) → p ∈ s

/-- The sequential closure of a sequentially closed set is the set itself. -/
lemma is_seq_closed.seq_closure_eq {s : set X} (hs : is_seq_closed s) :
  seq_closure s = s :=
subset.antisymm (λ p ⟨x, hx, hp⟩, hs hx hp) subset_seq_closure

/-- If a set is equal to its sequential closure, then it is sequentially closed. -/
lemma is_seq_closed_of_seq_closure_eq {s : set X} (hs : seq_closure s = s) :
  is_seq_closed s :=
λ x p hxs hxp, hs ▸ ⟨x, hxs, hxp⟩

/-- A set is sequentially closed iff it is equal to its sequential closure. -/
lemma is_seq_closed_iff {s : set X} :
  is_seq_closed s ↔ seq_closure s = s :=
⟨is_seq_closed.seq_closure_eq, is_seq_closed_of_seq_closure_eq⟩

/-- A set is sequentially closed if it is closed. -/
protected lemma is_closed.is_seq_closed {s : set X} (hc : is_closed s) : is_seq_closed s :=
λ u x hu hx, hc.mem_of_tendsto hx (eventually_of_forall hu)

/-- A topological space is called a *Fréchet-Urysohn space*, if the sequential closure of any set
is equal to its closure. Since one of the inclusions is trivial, we require only the non-trivial one
in the definition. -/
class frechet_urysohn_space (X : Type*) [topological_space X] : Prop :=
(closure_subset_seq_closure : ∀ s : set X, closure s ⊆ seq_closure s)

lemma seq_closure_eq_closure [frechet_urysohn_space X] (s : set X) :
  seq_closure s = closure s :=
seq_closure_subset_closure.antisymm $ frechet_urysohn_space.closure_subset_seq_closure s

/-- In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a limit
of a sequence taking values in this set. -/
lemma mem_closure_iff_seq_limit [frechet_urysohn_space X] {s : set X} {a : X} :
  a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ tendsto x at_top (𝓝 a) :=
by { rw [← seq_closure_eq_closure], refl }

/-- If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then convergence
is equivalent to sequential convergence. See also `filter.tendsto_iff_seq_tendsto` for a version
that works for any pair of filters assuming that the filter in the domain is countably generated.

This property is equivalent to the definition of `frechet_urysohn_space`, see
`frechet_urysohn_space.of_seq_tendsto_imp_tendsto`. -/
lemma tendsto_nhds_iff_seq_tendsto [frechet_urysohn_space X] {f : X → Y} {a : X} {b : Y} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, tendsto u at_top (𝓝 a) → tendsto (f ∘ u) at_top (𝓝 b) :=
begin
  refine ⟨λ hf u hu, hf.comp hu,
    λ h, ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 _⟩,
  rintro s ⟨hbs, hsc⟩,
  refine ⟨closure (f ⁻¹' s), ⟨mt _ hbs, is_closed_closure⟩, λ x, mt $ λ hx, subset_closure hx⟩,
  rw [← seq_closure_eq_closure],
  rintro ⟨u, hus, hu⟩,
  exact hsc.mem_of_tendsto (h u hu) (eventually_of_forall hus)
end

/-- An alternative construction for `frechet_urysohn_space`: if sequential convergence implies
convergence, then the space is a Fréchet-Urysohn space. -/
lemma frechet_urysohn_space.of_seq_tendsto_imp_tendsto
  (h : ∀ (f : X → Prop) (a : X),
    (∀ u : ℕ → X, tendsto u at_top (𝓝 a) → tendsto (f ∘ u) at_top (𝓝 (f a))) → continuous_at f a) :
  frechet_urysohn_space X :=
begin
  refine ⟨λ s x hcx, _⟩,
  specialize h (∉ s) x,
  by_cases hx : x ∈ s, { exact subset_seq_closure hx },
  simp_rw [(∘), continuous_at, hx, not_false_iff, nhds_true, tendsto_pure, eq_true_iff,
    ← mem_compl_iff, eventually_mem_set, ← mem_interior_iff_mem_nhds, interior_compl] at h,
  rw [mem_compl_iff, imp_not_comm] at h,
  simp only [not_forall, not_eventually, mem_compl_iff, not_not] at h,
  rcases h hcx with ⟨u, hux, hus⟩,
  rcases extraction_of_frequently_at_top hus with ⟨φ, φ_mono, hφ⟩,
  exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_at_top⟩
end

/-- Every first-countable space is a Fréchet-Urysohn space. -/
@[priority 100] -- see Note [lower instance priority]
instance topological_space.first_countable_topology.frechet_urysohn_space
  [first_countable_topology X] : frechet_urysohn_space X :=
frechet_urysohn_space.of_seq_tendsto_imp_tendsto $ λ f a, tendsto_iff_seq_tendsto.2

/-- A topological space is said to be a *sequential space* if any sequentially closed set in this
space is closed. This condition is weaker than being a Fréchet-Urysohn space. -/
class sequential_space (X : Type*) [topological_space X] : Prop :=
(is_closed_of_seq : ∀ s : set X, is_seq_closed s → is_closed s)

/-- Every Fréchet-Urysohn space is a sequential space. -/
@[priority 100] -- see Note [lower instance priority]
instance frechet_urysohn_space.to_sequential_space [frechet_urysohn_space X] :
  sequential_space X :=
⟨λ s hs, by rw [← closure_eq_iff_is_closed, ← seq_closure_eq_closure, hs.seq_closure_eq]⟩

/-- In a sequential space, a sequentially closed set is closed. -/
protected lemma is_seq_closed.is_closed [sequential_space X] {s : set X} (hs : is_seq_closed s) :
  is_closed s :=
sequential_space.is_closed_of_seq s hs

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space X] {M : set X} :
  is_seq_closed M ↔ is_closed M :=
⟨is_seq_closed.is_closed, is_closed.is_seq_closed⟩

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def seq_continuous (f : X → Y) : Prop :=
∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, tendsto x at_top (𝓝 p) → tendsto (f ∘ x) at_top (𝓝 (f p))

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
lemma is_seq_closed.preimage {f : X → Y} {s : set Y} (hs : is_seq_closed s)
  (hf : seq_continuous f) :
  is_seq_closed (f ⁻¹' s) :=
λ x p hx hp, hs hx (hf hp)

/- A continuous function is sequentially continuous. -/
protected lemma continuous.seq_continuous {f : X → Y} (hf : continuous f) :
  seq_continuous f :=
λ x p hx, (hf.tendsto p).comp hx

/-- A sequentially continuous function defined on a sequential space is continuous. -/
protected lemma seq_continuous.continuous [sequential_space X] {f : X → Y} (hf : seq_continuous f) :
  continuous f :=
continuous_iff_is_closed.mpr $ λ s hs, (hs.is_seq_closed.preimage hf).is_closed

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
lemma continuous_iff_seq_continuous [sequential_space X] {f : X → Y} :
  continuous f ↔ seq_continuous f :=
⟨continuous.seq_continuous, seq_continuous.continuous⟩

lemma quotient_map.sequential_space [sequential_space X] {f : X → Y} (hf : quotient_map f) :
  sequential_space Y :=
⟨λ s hs, hf.is_closed_preimage.mp $ (hs.preimage $ hf.continuous.seq_continuous).is_closed⟩

/-- The quotient of a sequential space is a sequential space. -/
instance [sequential_space X] {s : setoid X} : sequential_space (quotient s) :=
quotient_map_quot_mk.sequential_space

end topological_space

section seq_compact
open topological_space topological_space.first_countable_topology
variables [topological_space X]

/-- A set `s` is sequentially compact if every sequence taking values in `s` has a
converging subsequence. -/
def is_seq_compact (s : set X) :=
∀ ⦃x : ℕ → X⦄, (∀ n, x n ∈ s) → ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a)

/-- A space `X` is sequentially compact if every sequence in `X` has a
converging subsequence. -/
@[mk_iff] class seq_compact_space (X : Type*) [topological_space X] : Prop :=
(seq_compact_univ : is_seq_compact (univ : set X))

export seq_compact_space (seq_compact_univ)

lemma is_seq_compact.subseq_of_frequently_in {s : set X} (hs : is_seq_compact s) {x : ℕ → X}
  (hx : ∃ᶠ n in at_top, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hx, ⟨a, a_in, φ, hφ, h⟩ := hs huψ in
⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

lemma seq_compact_space.tendsto_subseq [seq_compact_space X] (x : ℕ → X) :
  ∃ a (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
let ⟨a, _, φ, mono, h⟩ := seq_compact_univ (λ n, mem_univ (x n)) in ⟨a, φ, mono, h⟩

section first_countable_topology
variables [first_countable_topology X]
open topological_space.first_countable_topology

protected lemma is_compact.is_seq_compact {s : set X} (hs : is_compact s) : is_seq_compact s :=
λ x x_in, let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (eventually_of_forall x_in))
in ⟨a, a_in, tendsto_subseq ha⟩

lemma is_compact.tendsto_subseq' {s : set X} {x : ℕ → X} (hs : is_compact s)
  (hx : ∃ᶠ n in at_top, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
hs.is_seq_compact.subseq_of_frequently_in hx

lemma is_compact.tendsto_subseq {s : set X} {x : ℕ → X} (hs : is_compact s) (hx : ∀ n, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
hs.is_seq_compact hx

@[priority 100] -- see Note [lower instance priority]
instance first_countable_topology.seq_compact_of_compact [compact_space X] : seq_compact_space X :=
⟨is_compact_univ.is_seq_compact⟩

lemma compact_space.tendsto_subseq [compact_space X] (x : ℕ → X) :
  ∃ a (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
seq_compact_space.tendsto_subseq x

end first_countable_topology
end seq_compact

section uniform_space_seq_compact

open_locale uniformity
open uniform_space prod

variables [uniform_space X] {s : set X}

lemma is_seq_compact.exists_tendsto_of_frequently_mem (hs : is_seq_compact s) {u : ℕ → X}
  (hu : ∃ᶠ n in at_top, u n ∈ s) (huc : cauchy_seq u) :
  ∃ x ∈ s, tendsto u at_top (𝓝 x) :=
let ⟨x, hxs, φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
in ⟨x, hxs, tendsto_nhds_of_cauchy_seq_of_subseq huc φ_mono.tendsto_at_top hx⟩

lemma is_seq_compact.exists_tendsto (hs : is_seq_compact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s)
  (huc : cauchy_seq u) : ∃ x ∈ s, tendsto u at_top (𝓝 x) :=
hs.exists_tendsto_of_frequently_mem (frequently_of_forall hu) huc

/-- A sequentially compact set in a uniform space is totally bounded. -/
protected lemma is_seq_compact.totally_bounded (h : is_seq_compact s) : totally_bounded s :=
begin
  intros V V_in,
  unfold is_seq_compact at h,
  contrapose! h,
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V,
  { simp only [not_subset, mem_Union₂, not_exists, exists_prop] at h,
    simpa only [forall_and_distrib, ball_image_iff, not_and] using seq_of_forall_finite_exists h },
  refine ⟨u, u_in, λ x x_in φ hφ huφ, _⟩,
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V,
    from huφ.cauchy_seq.mem_entourage V_in,
  exact hu (φ $ N + 1) (φ N) (hφ $ lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)
end

variables [is_countably_generated (𝓤 X)]

/-- A sequentially compact set in a uniform set with countably generated uniformity filter
is complete. -/
protected lemma is_seq_compact.is_complete (hs : is_seq_compact s) : is_complete s :=
begin
  intros l hl hls,
  haveI := hl.1,
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩,
  choose W hW hWV using λ n, comp_mem_uniformity_sets (hV.mem n),
  have hWV' : ∀ n, W n ⊆ V n, from λ n ⟨x, y⟩ hx, @hWV n (x, y) ⟨x, refl_mem_uniformity $ hW _, hx⟩,
  obtain ⟨t, ht_anti, htl, htW, hts⟩ : ∃ t : ℕ → set X, antitone t ∧ (∀ n, t n ∈ l) ∧
    (∀ n, t n ×ˢ t n ⊆ W n) ∧ (∀ n, t n ⊆ s),
  { have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ⊆ s,
    { rw [le_principal_iff] at hls,
      have : ∀ n, W n ∩ s ×ˢ s ∈ l ×ᶠ l := λ n, inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls),
      simpa only [l.basis_sets.prod_self.mem_iff, true_implies_iff, subset_inter_iff,
        prod_self_subset_prod_self, and.assoc] using this },
    choose t htl htW hts,
    have : ∀ n, (⋂ k ≤ n, t k) ⊆ t n, from λ n, Inter₂_subset _ le_rfl,
    exact ⟨λ n, ⋂ k ≤ n, t k, λ m n h, bInter_subset_bInter_left (λ k (hk : k ≤ m), hk.trans h),
      λ n, (bInter_mem (finite_le_nat n)).2 (λ k hk, htl k),
      λ n, (prod_mono (this n) (this n)).trans (htW n), λ n, (this n).trans (hts n)⟩ },
  choose u hu using λ n, filter.nonempty_of_mem (htl n),
  have huc : cauchy_seq u := hV.to_has_basis.cauchy_seq_iff.2
    (λ N hN, ⟨N, λ m hm n hn, hWV' _ $ @htW N (_, _) ⟨ht_anti hm (hu _), (ht_anti hn (hu _))⟩⟩),
  rcases hs.exists_tendsto (λ n, hts n (hu n)) huc with ⟨x, hxs, hx⟩,
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.to_has_basis).ge_iff.2 $ λ N hN, _⟩,
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N),
    from ((eventually_ge_at_top N).and (hx $ ball_mem_nhds x (hW N))).exists,
  refine mem_of_superset (htl n) (λ y hy, hWV N ⟨u n, _, htW N ⟨_, _⟩⟩),
  exacts [hn, ht_anti hNn (hu n), ht_anti hNn hy]
end

/-- If `𝓤 β` is countably generated, then any sequentially compact set is compact. -/
protected lemma is_seq_compact.is_compact (hs : is_seq_compact s) : is_compact s :=
is_compact_iff_totally_bounded_is_complete.2 ⟨hs.totally_bounded, hs.is_complete⟩

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected lemma uniform_space.is_compact_iff_is_seq_compact : is_compact s ↔ is_seq_compact s :=
⟨λ H, H.is_seq_compact, λ H, H.is_compact⟩

lemma uniform_space.compact_space_iff_seq_compact_space : compact_space X ↔ seq_compact_space X :=
by simp only [← is_compact_univ_iff, seq_compact_space_iff,
  uniform_space.is_compact_iff_is_seq_compact]

end uniform_space_seq_compact

section metric_seq_compact

variables [pseudo_metric_space X]
open metric

lemma seq_compact.lebesgue_number_lemma_of_metric {ι : Sort*} {c : ι → set X}
  {s : set X} (hs : is_seq_compact s) (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ δ > 0, ∀ a ∈ s, ∃ i, ball a δ ⊆ c i :=
lebesgue_number_lemma_of_metric hs.is_compact hc₁ hc₂

variables [proper_space X] {s : set X}

/-- A version of **Bolzano-Weistrass**: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
lemma tendsto_subseq_of_frequently_bounded (hs : bounded s)
  {x : ℕ → X} (hx : ∃ᶠ n in at_top, x n ∈ s) :
  ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
have hcs : is_seq_compact (closure s), from hs.is_compact_closure.is_seq_compact,
have hu' : ∃ᶠ n in at_top, x n ∈ closure s, from hx.mono (λ n hn, subset_closure hn),
hcs.subseq_of_frequently_in hu'

/-- A version of Bolzano-Weistrass: in a proper metric space (eg. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
lemma tendsto_subseq_of_bounded (hs : bounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
  ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
tendsto_subseq_of_frequently_bounded hs $ frequently_of_forall hx

end metric_seq_compact

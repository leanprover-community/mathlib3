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

open set function filter bornology topological_space
open_locale topological_space filter

variables {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space X] [topological_space Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is
the set of all `a : X` which arise as limit of sequences in `s`. -/
def seq_closure (s : set X) : set X :=
{a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ tendsto x at_top (𝓝 a)}

lemma subset_seq_closure {s : set X} : s ⊆ seq_closure s :=
λ p hp, ⟨const ℕ p, λ _, hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma seq_closure_subset_closure {s : set X} : seq_closure s ⊆ closure s :=
λ p ⟨x, xM, xp⟩, mem_closure_of_tendsto xp (univ_mem' xM)

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set X) : Prop :=
∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ s) → (tendsto x at_top (𝓝 p)) → p ∈ s

/-- The sequential closure of a sequentially closed set is the set itself. -/
lemma is_seq_closed.seq_closure_eq {s : set X} (hs : is_seq_closed s) :
  seq_closure s = s :=
subset.antisymm (λ p ⟨x, hx, hp⟩, hs hx hp) subset_seq_closure

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
  simp_rw [(∘), continuous_at, hx, not_false_iff, nhds_true, tendsto_pure, eq_true,
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

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
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
class seq_compact_space (X : Type*) [topological_space X] : Prop :=
(seq_compact_univ : is_seq_compact (univ : set X))

lemma is_seq_compact.subseq_of_frequently_in {s : set X} (hs : is_seq_compact s) {x : ℕ → X}
  (hx : ∃ᶠ n in at_top, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_at_top hx, ⟨a, a_in, φ, hφ, h⟩ := hs huψ in
⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩

lemma seq_compact_space.tendsto_subseq [seq_compact_space X] (x : ℕ → X) :
  ∃ a (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
let ⟨a, _, φ, mono, h⟩ := seq_compact_space.seq_compact_univ (λ n, mem_univ (x n)) in
⟨a, φ, mono, h⟩

section first_countable_topology
variables [first_countable_topology X]
open topological_space.first_countable_topology

lemma is_compact.is_seq_compact {s : set X} (hs : is_compact s) : is_seq_compact s :=
λ x x_in,
let ⟨a, a_in, ha⟩ := @hs (map x at_top) _
  (le_principal_iff.mpr (univ_mem' x_in : _)) in ⟨a, a_in, tendsto_subseq ha⟩

lemma is_compact.tendsto_subseq' {s : set X} {x : ℕ → X} (hs : is_compact s)
  (hx : ∃ᶠ n in at_top, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
hs.is_seq_compact.subseq_of_frequently_in hx

lemma is_compact.tendsto_subseq {s : set X} {x : ℕ → X} (hs : is_compact s) (hx : ∀ n, x n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
hs.is_seq_compact hx

@[priority 100] -- see Note [lower instance priority]
instance first_countable_topology.seq_compact_of_compact [compact_space X] : seq_compact_space X :=
⟨compact_univ.is_seq_compact⟩

lemma compact_space.tendsto_subseq [compact_space X] (x : ℕ → X) :
  ∃ a (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 a) :=
seq_compact_space.tendsto_subseq x

end first_countable_topology
end seq_compact

section uniform_space_seq_compact

open_locale uniformity
open uniform_space prod

variables [uniform_space X] {s : set X}

lemma lebesgue_number_lemma_seq {ι : Type*} [is_countably_generated (𝓤 X)] {c : ι → set X}
  (hs : is_seq_compact s) (hc₁ : ∀ i, is_open (c i)) (hc₂ : s ⊆ ⋃ i, c i) :
  ∃ V ∈ 𝓤 X, symmetric_rel V ∧ ∀ x ∈ s, ∃ i, ball x V ⊆ c i :=
begin
  classical,
  obtain ⟨V, hV, Vsymm⟩ :
    ∃ V : ℕ → set (X × X), (𝓤 X).has_antitone_basis V ∧ ∀ n, swap ⁻¹' V n = V n,
      from uniform_space.has_seq_basis X,
  suffices : ∃ n, ∀ x ∈ s, ∃ i, ball x (V n) ⊆ c i,
  { cases this with n hn,
    exact ⟨V n, hV.to_has_basis.mem_of_mem trivial, Vsymm n, hn⟩ },
  by_contradiction H,
  obtain ⟨x, x_in, hx⟩ : ∃ x : ℕ → X, (∀ n, x n ∈ s) ∧ ∀ n i, ¬ ball (x n) (V n) ⊆ c i,
  { push_neg at H,
    choose x hx using H,
    exact ⟨x, forall_and_distrib.mp hx⟩ }, clear H,
  obtain ⟨x₀, x₀_in, φ, φ_mono, hlim⟩ :
    ∃ (x₀ ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (x ∘ φ) at_top (𝓝 x₀),
    from hs x_in, clear hs,
  obtain ⟨i₀, x₀_in⟩ : ∃ i₀, x₀ ∈ c i₀,
  { rcases hc₂ x₀_in with ⟨_, ⟨i₀, rfl⟩, x₀_in_c⟩,
    exact ⟨i₀, x₀_in_c⟩ }, clear hc₂,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ball x₀ (V n₀) ⊆ c i₀,
  { rcases (nhds_basis_uniformity hV.to_has_basis).mem_iff.mp
      (is_open_iff_mem_nhds.mp (hc₁ i₀) _ x₀_in) with ⟨n₀, _, h⟩,
    use n₀,
    rwa ← ball_eq_of_symmetry (Vsymm n₀) at h }, clear hc₁,
  obtain ⟨W, W_in, hWW⟩ : ∃ W ∈ 𝓤 X, W ○ W ⊆ V n₀,
    from comp_mem_uniformity_sets (hV.to_has_basis.mem_of_mem trivial),
  obtain ⟨N, x_φ_N_in, hVNW⟩ : ∃ N, x (φ N) ∈ ball x₀ W ∧ V (φ N) ⊆ W,
  { obtain ⟨N₁, h₁⟩ : ∃ N₁, ∀ n ≥ N₁, x (φ n) ∈ ball x₀ W,
      from tendsto_at_top'.mp hlim _ (mem_nhds_left x₀ W_in),
    obtain ⟨N₂, h₂⟩ : ∃ N₂, V (φ N₂) ⊆ W,
    { rcases hV.to_has_basis.mem_iff.mp W_in with ⟨N, _, hN⟩,
      use N,
      exact subset.trans (hV.antitone $ φ_mono.id_le _) hN },
    have : φ N₂ ≤ φ (max N₁ N₂),
      from φ_mono.le_iff_le.mpr (le_max_right _ _),
    exact ⟨max N₁ N₂, h₁ _ (le_max_left _ _), trans (hV.antitone this) h₂⟩ },
  suffices : ball (x (φ N)) (V (φ N)) ⊆ c i₀,
    from hx (φ N) i₀ this,
  calc
    ball (x $ φ N) (V $ φ N) ⊆ ball (x $ φ N) W : preimage_mono hVNW
                         ... ⊆ ball x₀ (V n₀)   : ball_subset_of_comp_subset x_φ_N_in hWW
                         ... ⊆ c i₀             : hn₀,
end

lemma is_seq_compact.totally_bounded (h : is_seq_compact s) : totally_bounded s :=
begin
  classical,
  apply totally_bounded_of_forall_symm,
  unfold is_seq_compact at h,
  contrapose! h,
  rcases h with ⟨V, V_in, V_symm, h⟩,
  simp_rw [not_subset] at h,
  have : ∀ (t : set X), t.finite → ∃ a, a ∈ s ∧ a ∉ ⋃ y ∈ t, ball y V,
  { intros t ht,
    obtain ⟨a, a_in, H⟩ : ∃ a ∈ s, ∀ x ∈ t, (x, a) ∉ V,
      by simpa [ht] using h t,
    use [a, a_in],
    intro H',
    obtain ⟨x, x_in, hx⟩ := mem_Union₂.mp H',
    exact H x x_in hx },
  cases seq_of_forall_finite_exists this with u hu, clear h this,
  simp [forall_and_distrib] at hu,
  cases hu with u_in hu,
  use [u, u_in], clear u_in,
  intros x x_in φ,
  intros hφ huφ,
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V,
    from huφ.cauchy_seq.mem_entourage V_in,
  specialize hN N (N+1) (le_refl N) (nat.le_succ N),
  specialize hu (φ $ N+1) (φ N) (hφ $ lt_add_one N),
  exact hu hN,
end

protected lemma is_seq_compact.is_compact [is_countably_generated $ 𝓤 X] (hs : is_seq_compact s) :
  is_compact s :=
begin
  classical,
  rw is_compact_iff_finite_subcover,
  intros ι U Uop s_sub,
  rcases lebesgue_number_lemma_seq hs Uop s_sub with ⟨V, V_in, Vsymm, H⟩,
  rcases totally_bounded_iff_subset.mp hs.totally_bounded V V_in with ⟨t,t_sub, tfin,  ht⟩,
  have : ∀ x : t, ∃ (i : ι), ball x.val V ⊆ U i,
  { rintros ⟨x, x_in⟩,
    exact H x (t_sub x_in) },
  choose i hi using this,
  haveI : fintype t := tfin.fintype,
  use finset.image i finset.univ,
  transitivity ⋃ y ∈ t, ball y V,
  { intros x x_in,
    specialize ht x_in,
    rw mem_Union₂ at *,
    simp_rw ball_eq_of_symmetry Vsymm,
    exact ht },
  { refine Union₂_mono' (λ x x_in, _),
    exact ⟨i ⟨x, x_in⟩, finset.mem_image_of_mem _ (finset.mem_univ _), hi ⟨x, x_in⟩⟩ },
end

/-- A version of Bolzano-Weistrass: in a uniform space with countably generated uniformity filter
(e.g., in a metric space), a set is compact if and only if it is sequentially compact. -/
protected lemma uniform_space.compact_iff_seq_compact [is_countably_generated $ 𝓤 X] :
 is_compact s ↔ is_seq_compact s :=
⟨λ H, H.is_seq_compact, λ H, H.is_compact⟩

lemma uniform_space.compact_space_iff_seq_compact_space [is_countably_generated $ 𝓤 X] :
  compact_space X ↔ seq_compact_space X :=
have key : is_compact (univ : set X) ↔ is_seq_compact univ := uniform_space.compact_iff_seq_compact,
⟨λ ⟨h⟩, ⟨key.mp h⟩, λ ⟨h⟩, ⟨key.mpr h⟩⟩

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

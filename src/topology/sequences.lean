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

open set function filter
open_locale topological_space

variables {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/
section topological_space
variables [topological_space X] [topological_space Y]

/-- The sequential closure of a set `s : set X` in a topological space `X` is
the set of all `a : X` which arise as limit of sequences in `s`. -/
def seq_closure (s : set X) : set X :=
{a | ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ tendsto x at_top (𝓝 a)}

lemma subset_seq_closure (s : set X) : s ⊆ seq_closure s :=
λ a ha, ⟨const ℕ a, λ n, ha, tendsto_const_nhds⟩

/-- A set `s` is sequentially closed if for any converging sequence `x n` of elements of `s`,
the limit belongs to `s` as well. -/
def is_seq_closed (s : set X) : Prop := s = seq_closure s

/-- A convenience lemma for showing that a set is sequentially closed. -/
lemma is_seq_closed_of_def {s : set X}
  (h : ∀ (x : ℕ → X) (a : X), (∀ n : ℕ, x n ∈ s) → tendsto x at_top (𝓝 a) → a ∈ s) :
  is_seq_closed s :=
show s = seq_closure s, from subset.antisymm
  (subset_seq_closure s)
  (show ∀ a, a ∈ seq_closure s → a ∈ s, from
    (assume a ⟨x, hxs, hxa⟩, show a ∈ s, from h x a hxs hxa))

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
lemma seq_closure_subset_closure (s : set X) : seq_closure s ⊆ closure s :=
assume a ⟨x, xM, xa⟩,
mem_closure_of_tendsto xa (eventually_of_forall xM)

/-- A set is sequentially closed if it is closed. -/
lemma is_closed.is_seq_closed {s : set X} (hs : is_closed s) : is_seq_closed s :=
suffices seq_closure s ⊆ s, from (subset_seq_closure s).antisymm this,
calc seq_closure s ⊆ closure s : seq_closure_subset_closure s
               ... = s         : hs.closure_eq

/-- The limit of a convergent sequence in a sequentially closed set is in that set.-/
lemma is_seq_closed.mem_of_tendsto {s : set X} (hs : is_seq_closed s) {x : ℕ → X}
  (hmem : ∀ n, x n ∈ s) {a : X} (ha : tendsto x at_top (𝓝 a)) : a ∈ s :=
have a ∈ seq_closure s, from ⟨x, hmem, ha⟩,
eq.subst (eq.symm ‹is_seq_closed s›) ‹a ∈ seq_closure s›

/-- A sequential space is a space in which 'sequences are enough to probe the topology'. This can be
 formalised by demanding that the sequential closure and the closure coincide. The following
 statements show that other topological properties can be deduced from sequences in sequential
 spaces. -/
class sequential_space (X : Type*) [topological_space X] : Prop :=
(seq_closure_eq_closure : ∀ s : set X, seq_closure s = closure s)

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
lemma is_seq_closed_iff_is_closed [sequential_space X] {s : set X} :
  is_seq_closed s ↔ is_closed s :=
iff.intro
  (assume _, closure_eq_iff_is_closed.mp (eq.symm
    (calc s = seq_closure s : by assumption
        ... = closure s     : sequential_space.seq_closure_eq_closure s)))
  is_closed.is_seq_closed

alias is_seq_closed_iff_is_closed ↔ is_seq_closed.is_closed _

/-- In a sequential space, a point belongs to the closure of a set iff it is a limit of a sequence
taking values in this set. -/
lemma mem_closure_iff_seq_limit [sequential_space X] {s : set X} {a : X} :
  a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ tendsto x at_top (𝓝 a) :=
by { rw ← sequential_space.seq_closure_eq_closure, exact iff.rfl }

/-- A function between topological spaces is sequentially continuous if it commutes with limit of
 convergent sequences. -/
def seq_continuous (f : X → Y) : Prop :=
∀ (x : ℕ → X), ∀ {a : X}, tendsto x at_top (𝓝 a) → tendsto (f ∘ x) at_top (𝓝 (f a))

/- A continuous function is sequentially continuous. -/
protected lemma continuous.seq_continuous {f : X → Y} (hf : continuous f) : seq_continuous f :=
λ x a, (hf.tendsto _).comp

/-- In a sequential space, continuity and sequential continuity coincide. -/
lemma continuous_iff_seq_continuous {f : X → Y} [sequential_space X] :
  continuous f ↔ seq_continuous f :=
iff.intro
  continuous.seq_continuous
  (assume : seq_continuous f, show continuous f, from
    suffices h : ∀ {s : set Y}, is_closed s → is_seq_closed (f ⁻¹' s), from
      continuous_iff_is_closed.mpr (assume s _, is_seq_closed_iff_is_closed.mp $ h ‹is_closed s›),
    assume s (_ : is_closed s),
      is_seq_closed_of_def $
        assume (x : ℕ → X) a (_ : ∀ n, f (x n) ∈ s) (_ : tendsto x at_top (𝓝 a)),
        have tendsto (f ∘ x) at_top (𝓝 (f a)), from ‹seq_continuous f› x ‹_›,
        show f a ∈ s,
          from ‹is_closed s›.is_seq_closed.mem_of_tendsto ‹∀ n, f (x n) ∈ s› ‹_›)

alias continuous_iff_seq_continuous ↔ _ seq_continuous.continuous

end topological_space

namespace topological_space

namespace first_countable_topology

variables [topological_space X] [first_countable_topology X]

/-- Every first-countable space is sequential. -/
@[priority 100] -- see Note [lower instance priority]
instance : sequential_space X :=
⟨show ∀ s, seq_closure s = closure s, from assume s,
  suffices closure s ⊆ seq_closure s,
    from set.subset.antisymm (seq_closure_subset_closure s) this,
  -- For every a ∈ closure s, we need to construct a sequence `x` in `s` that converges to `a`:
  assume (a : X) (ha : a ∈ closure s),
  -- Since we are in a first-countable space, the neighborhood filter around `a` has a decreasing
  -- basis `U` indexed by `ℕ`.
  let ⟨U, hU⟩ := (𝓝 a).exists_antitone_basis in
  -- Since `p ∈ closure M`, there is an element in each `M ∩ U i`
  have ha : ∀ (i : ℕ), ∃ (y : X), y ∈ s ∧ y ∈ U i,
    by simpa using (mem_closure_iff_nhds_basis hU.1).mp ha,
  begin
    -- The axiom of (countable) choice builds our sequence from the later fact
    choose u hu using ha,
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

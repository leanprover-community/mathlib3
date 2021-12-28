/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.bases
import topology.uniform_space.basic
/-!
# Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/
universes u v

open filter topological_space set classical uniform_space
open_locale classical uniformity topological_space filter

variables {α : Type u} {β : Type v} [uniform_space α]

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def cauchy (f : filter α) := ne_bot f ∧ f ×ᶠ f ≤ (𝓤 α)

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def is_complete (s : set α) := ∀f, cauchy f → f ≤ 𝓟 s → ∃x∈s, f ≤ 𝓝 x

lemma filter.has_basis.cauchy_iff {ι} {p : ι → Prop} {s : ι → set (α × α)} (h : (𝓤 α).has_basis p s)
  {f : filter α} :
  cauchy f ↔ (ne_bot f ∧ (∀ i, p i → ∃ t ∈ f, ∀ x y ∈ t, (x, y) ∈ s i)) :=
and_congr iff.rfl $ (f.basis_sets.prod_self.le_basis_iff h).trans $
  by simp only [subset_def, prod.forall, mem_prod_eq, and_imp, id]

lemma cauchy_iff' {f : filter α} :
  cauchy f ↔ (ne_bot f ∧ (∀ s ∈ 𝓤 α, ∃t∈f, ∀ x y ∈ t, (x, y) ∈ s)) :=
(𝓤 α).basis_sets.cauchy_iff

lemma cauchy_iff {f : filter α} :
  cauchy f ↔ (ne_bot f ∧ (∀ s ∈ 𝓤 α, ∃t∈f, (set.prod t t) ⊆ s)) :=
cauchy_iff'.trans $ by simp only [subset_def, prod.forall, mem_prod_eq, and_imp, id]

lemma cauchy_map_iff {l : filter β} {f : β → α} :
  cauchy (l.map f) ↔ (ne_bot l ∧ tendsto (λp:β×β, (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α)) :=
by rw [cauchy, map_ne_bot_iff, prod_map_map_eq, tendsto]

lemma cauchy_map_iff' {l : filter β} [hl : ne_bot l] {f : β → α} :
  cauchy (l.map f) ↔ tendsto (λp:β×β, (f p.1, f p.2)) (l ×ᶠ l) (𝓤 α) :=
cauchy_map_iff.trans $ and_iff_right hl

lemma cauchy.mono {f g : filter α} [hg : ne_bot g] (h_c : cauchy f) (h_le : g ≤ f) : cauchy g :=
⟨hg, le_trans (filter.prod_mono h_le h_le) h_c.right⟩

lemma cauchy.mono' {f g : filter α} (h_c : cauchy f) (hg : ne_bot g) (h_le : g ≤ f) : cauchy g :=
h_c.mono h_le

lemma cauchy_nhds {a : α} : cauchy (𝓝 a) :=
⟨nhds_ne_bot, nhds_prod_eq.symm.trans_le (nhds_le_uniformity a)⟩

lemma cauchy_pure {a : α} : cauchy (pure a) :=
cauchy_nhds.mono (pure_le_nhds a)

lemma filter.tendsto.cauchy_map {l : filter β} [ne_bot l] {f : β → α} {a : α}
  (h : tendsto f l (𝓝 a)) :
  cauchy (map f l) :=
cauchy_nhds.mono h

lemma cauchy.prod [uniform_space β] {f : filter α} {g : filter β} (hf : cauchy f) (hg : cauchy g) :
  cauchy (f ×ᶠ g) :=
begin
  refine ⟨hf.1.prod hg.1, _⟩,
  simp only [uniformity_prod, le_inf_iff, ← map_le_iff_le_comap, ← prod_map_map_eq],
  exact ⟨le_trans (prod_mono tendsto_fst tendsto_fst) hf.2,
    le_trans (prod_mono tendsto_snd tendsto_snd) hg.2⟩
end

/-- The common part of the proofs of `le_nhds_of_cauchy_adhp` and
`sequentially_complete.le_nhds_of_seq_tendsto_nhds`: if for any entourage `s`
one can choose a set `t ∈ f` of diameter `s` such that it contains a point `y`
with `(x, y) ∈ s`, then `f` converges to `x`. -/
lemma le_nhds_of_cauchy_adhp_aux {f : filter α} {x : α}
  (adhs : ∀ s ∈ 𝓤 α, ∃ t ∈ f, (set.prod t t ⊆ s) ∧ ∃ y, (x, y) ∈ s ∧ y ∈ t) :
  f ≤ 𝓝 x :=
begin
  -- Consider a neighborhood `s` of `x`
  assume s hs,
  -- Take an entourage twice smaller than `s`
  rcases comp_mem_uniformity_sets (mem_nhds_uniformity_iff_right.1 hs) with ⟨U, U_mem, hU⟩,
  -- Take a set `t ∈ f`, `t × t ⊆ U`, and a point `y ∈ t` such that `(x, y) ∈ U`
  rcases adhs U U_mem with ⟨t, t_mem, ht, y, hxy, hy⟩,
  apply mem_of_superset t_mem,
  -- Given a point `z ∈ t`, we have `(x, y) ∈ U` and `(y, z) ∈ t × t ⊆ U`, hence `z ∈ s`
  exact (λ z hz, hU (prod_mk_mem_comp_rel hxy (ht $ mk_mem_prod hy hz)) rfl)
end

/-- If `x` is an adherent (cluster) point for a Cauchy filter `f`, then it is a limit point
for `f`. -/
lemma le_nhds_of_cauchy_adhp {f : filter α} {x : α} (hf : cauchy f)
  (adhs : cluster_pt x f) : f ≤ 𝓝 x :=
le_nhds_of_cauchy_adhp_aux
begin
  assume s hs,
  obtain ⟨t, t_mem, ht⟩ : ∃ t ∈ f, set.prod t t ⊆ s,
    from (cauchy_iff.1 hf).2 s hs,
  use [t, t_mem, ht],
  exact (forall_mem_nonempty_iff_ne_bot.2 adhs _
    (inter_mem_inf (mem_nhds_left x hs) t_mem ))
end

lemma le_nhds_iff_adhp_of_cauchy {f : filter α} {x : α} (hf : cauchy f) :
  f ≤ 𝓝 x ↔ cluster_pt x f :=
⟨assume h, cluster_pt.of_le_nhds' h hf.1, le_nhds_of_cauchy_adhp hf⟩

lemma cauchy.map [uniform_space β] {f : filter α} {m : α → β}
  (hf : cauchy f) (hm : uniform_continuous m) : cauchy (map m f) :=
⟨hf.1.map _,
  calc map m f ×ᶠ map m f = map (λp:α×α, (m p.1, m p.2)) (f ×ᶠ f) : filter.prod_map_map_eq
    ... ≤ map (λp:α×α, (m p.1, m p.2)) (𝓤 α) : map_mono hf.right
    ... ≤ 𝓤 β : hm⟩

lemma cauchy.comap [uniform_space β] {f : filter β} {m : α → β}
  (hf : cauchy f) (hm : comap (λp:α×α, (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
  [ne_bot (comap m f)] : cauchy (comap m f) :=
⟨‹_›,
  calc comap m f ×ᶠ comap m f = comap (λp:α×α, (m p.1, m p.2)) (f ×ᶠ f) : filter.prod_comap_comap_eq
    ... ≤ comap (λp:α×α, (m p.1, m p.2)) (𝓤 β) : comap_mono hf.right
    ... ≤ 𝓤 α : hm⟩

lemma cauchy.comap' [uniform_space β] {f : filter β} {m : α → β}
  (hf : cauchy f) (hm : comap (λp:α×α, (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
  (hb : ne_bot (comap m f)) : cauchy (comap m f) :=
hf.comap hm

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def cauchy_seq [semilattice_sup β] (u : β → α) := cauchy (at_top.map u)

lemma cauchy_seq.tendsto_uniformity [semilattice_sup β] {u : β → α} (h : cauchy_seq u) :
  tendsto (prod.map u u) at_top (𝓤 α) :=
by simpa only [tendsto, prod_map_map_eq', prod_at_top_at_top_eq] using h.right

lemma cauchy_seq.nonempty [semilattice_sup β] {u : β → α} (hu : cauchy_seq u) : nonempty β :=
@nonempty_of_ne_bot _ _ $ (map_ne_bot_iff _).1 hu.1

lemma cauchy_seq.mem_entourage {β : Type*} [semilattice_sup β] {u : β → α}
  (h : cauchy_seq u) {V : set (α × α)} (hV : V ∈ 𝓤 α) :
  ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V :=
begin
  haveI := h.nonempty,
  have := h.tendsto_uniformity, rw ← prod_at_top_at_top_eq at this,
  simpa [maps_to] using at_top_basis.prod_self.tendsto_left_iff.1 this V hV
end

lemma filter.tendsto.cauchy_seq [semilattice_sup β] [nonempty β] {f : β → α} {x}
  (hx : tendsto f at_top (𝓝 x)) :
  cauchy_seq f :=
hx.cauchy_map

lemma cauchy_seq_const (x : α) : cauchy_seq (λ n : ℕ, x) :=
tendsto_const_nhds.cauchy_seq

lemma cauchy_seq_iff_tendsto [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ tendsto (prod.map u u) at_top (𝓤 α) :=
cauchy_map_iff'.trans $ by simp only [prod_at_top_at_top_eq, prod.map_def]

lemma cauchy_seq.comp_tendsto {γ} [semilattice_sup β] [semilattice_sup γ] [nonempty γ]
  {f : β → α} (hf : cauchy_seq f) {g : γ → β} (hg : tendsto g at_top at_top) :
  cauchy_seq (f ∘ g) :=
cauchy_seq_iff_tendsto.2 $ hf.tendsto_uniformity.comp (hg.prod_at_top hg)

lemma cauchy_seq.subseq_subseq_mem {V : ℕ → set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α)
  {u : ℕ → α} (hu : cauchy_seq u)
  {f g : ℕ → ℕ} (hf : tendsto f at_top at_top) (hg : tendsto g at_top at_top) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, ((u ∘ f ∘ φ) n, (u ∘ g ∘ φ) n) ∈ V n :=
begin
  rw cauchy_seq_iff_tendsto at hu,
  exact ((hu.comp $ hf.prod_at_top hg).comp tendsto_at_top_diagonal).subseq_mem hV,
end

lemma cauchy_seq_iff' {u : ℕ → α} :
  cauchy_seq u ↔ ∀ V ∈ 𝓤 α, ∀ᶠ k in at_top, k ∈ (prod.map u u) ⁻¹' V :=
by simpa only [cauchy_seq_iff_tendsto]

lemma cauchy_seq_iff {u : ℕ → α} :
  cauchy_seq u ↔ ∀ V ∈ 𝓤 α, ∃ N, ∀ k ≥ N, ∀ l ≥ N, (u k, u l) ∈ V :=
by simp [cauchy_seq_iff', filter.eventually_at_top_prod_self', prod_map]

lemma cauchy_seq.cauchy_map_cofinite {u : ℕ → α} (hu : cauchy_seq u) :
  cauchy (filter.map u cofinite) :=
begin
  rw nat.cofinite_eq_at_top,
  exact hu,
end

lemma cauchy_seq.prod_map {γ δ} [uniform_space β] [semilattice_sup γ] [semilattice_sup δ]
  {u : γ → α} {v : δ → β}
  (hu : cauchy_seq u) (hv : cauchy_seq v) : cauchy_seq (prod.map u v) :=
by simpa only [cauchy_seq, prod_map_map_eq', prod_at_top_at_top_eq] using hu.prod hv

lemma cauchy_seq.prod {γ} [uniform_space β] [semilattice_sup γ] {u : γ → α} {v : γ → β}
  (hu : cauchy_seq u) (hv : cauchy_seq v) : cauchy_seq (λ x, (u x, v x)) :=
begin
  haveI := hu.nonempty,
  exact (hu.prod hv).mono (tendsto.prod_mk le_rfl le_rfl)
end

lemma cauchy_seq.eventually_eventually [semilattice_sup β] [nonempty β] {u : β → α}
  (hu : cauchy_seq u) {V : set (α × α)} (hV : V ∈ 𝓤 α) :
  ∀ᶠ k in at_top, ∀ᶠ l in at_top, (u k, u l) ∈ V :=
eventually_eventually_at_top $ hu.tendsto_uniformity hV

lemma uniform_continuous.comp_cauchy_seq {γ} [uniform_space β] [semilattice_sup γ]
  {f : α → β} (hf : uniform_continuous f) {u : γ → α} (hu : cauchy_seq u) :
  cauchy_seq (f ∘ u) :=
hu.map hf

lemma cauchy_seq.subseq_mem {V : ℕ → set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α)
  {u : ℕ → α} (hu : cauchy_seq u) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ ∀ n, (u $ φ (n + 1), u $ φ n) ∈ V n :=
begin
  have : ∀ n, ∃ N, ∀ k ≥ N, ∀ l ≥ k, (u l, u k) ∈ V n,
  { intro n,
    rw [cauchy_seq_iff] at hu,
    rcases hu _ (hV n) with ⟨N, H⟩,
    exact ⟨N, λ k hk l hl, H _ (le_trans hk hl) _ hk ⟩ },
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ, hφ : ∀ n, ∀ l ≥ φ n, (u l, u $ φ n) ∈ V n⟩ :=
    extraction_forall_of_eventually' this,
  exact ⟨φ, φ_extr, λ n, hφ _ _ (φ_extr $ lt_add_one n).le⟩,
end

lemma filter.tendsto.subseq_mem_entourage {V : ℕ → set (α × α)} (hV : ∀ n, V n ∈ 𝓤 α)
  {u : ℕ → α} {a : α} (hu : tendsto u at_top (𝓝 a)) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ (u (φ 0), a) ∈ V 0 ∧ ∀ n, (u $ φ (n + 1), u $ φ n) ∈ V (n + 1) :=
begin
  rcases mem_at_top_sets.1 (hu (ball_mem_nhds a (symm_le_uniformity $ hV 0))) with ⟨n, hn⟩,
  rcases (hu.comp (tendsto_add_at_top_nat n)).cauchy_seq.subseq_mem (λ n, hV (n + 1))
    with ⟨φ, φ_mono, hφV⟩,
  exact ⟨λ k, φ k + n, φ_mono.add_const _, hn _ le_add_self, hφV⟩
end

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
lemma tendsto_nhds_of_cauchy_seq_of_subseq
  [semilattice_sup β] {u : β → α} (hu : cauchy_seq u)
  {ι : Type*} {f : ι → β} {p : filter ι} [ne_bot p]
  (hf : tendsto f p at_top) {a : α} (ha : tendsto (u ∘ f) p (𝓝 a)) :
  tendsto u at_top (𝓝 a) :=
le_nhds_of_cauchy_adhp hu (map_cluster_pt_of_comp hf ha)

@[nolint ge_or_gt] -- see Note [nolint_ge]
lemma filter.has_basis.cauchy_seq_iff {γ} [nonempty β] [semilattice_sup β] {u : β → α}
  {p : γ → Prop} {s : γ → set (α × α)} (h : (𝓤 α).has_basis p s) :
  cauchy_seq u ↔ ∀ i, p i → ∃N, ∀m n≥N, (u m, u n) ∈ s i :=
begin
  rw [cauchy_seq_iff_tendsto, ← prod_at_top_at_top_eq],
  refine (at_top_basis.prod_self.tendsto_iff h).trans _,
  simp only [exists_prop, true_and, maps_to, preimage, subset_def, prod.forall,
    mem_prod_eq, mem_set_of_eq, mem_Ici, and_imp, prod.map]
end

lemma filter.has_basis.cauchy_seq_iff' {γ} [nonempty β] [semilattice_sup β] {u : β → α}
  {p : γ → Prop} {s : γ → set (α × α)} (H : (𝓤 α).has_basis p s) :
  cauchy_seq u ↔ ∀ i, p i → ∃N, ∀n≥N, (u n, u N) ∈ s i :=
begin
  refine H.cauchy_seq_iff.trans ⟨λ h i hi, _, λ h i hi, _⟩,
  { exact (h i hi).imp (λ N hN n hn, hN n N hn (le_refl N)) },
  { rcases comp_symm_of_uniformity (H.mem_of_mem hi) with ⟨t, ht, ht', hts⟩,
    rcases H.mem_iff.1 ht with ⟨j, hj, hjt⟩,
    refine (h j hj).imp (λ N hN m n hm hn, hts ⟨u N, hjt _, ht' $ hjt _⟩),
    { exact hN m hm },
    { exact hN n hn } }
end

lemma cauchy_seq_of_controlled [semilattice_sup β] [nonempty β]
  (U : β → set (α × α)) (hU : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s)
  {f : β → α} (hf : ∀ {N m n : β}, N ≤ m → N ≤ n → (f m, f n) ∈ U N) :
  cauchy_seq f :=
cauchy_seq_iff_tendsto.2
begin
  assume s hs,
  rw [mem_map, mem_at_top_sets],
  cases hU s hs with N hN,
  refine ⟨(N, N), λ mn hmn, _⟩,
  cases mn with m n,
  exact hN (hf hmn.1 hmn.2)
end

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class complete_space (α : Type u) [uniform_space α] : Prop :=
(complete : ∀{f:filter α}, cauchy f → ∃x, f ≤ 𝓝 x)

lemma complete_univ {α : Type u} [uniform_space α] [complete_space α] :
  is_complete (univ : set α) :=
begin
  assume f hf _,
  rcases complete_space.complete hf with ⟨x, hx⟩,
  exact ⟨x, mem_univ x, hx⟩
end

instance complete_space.prod [uniform_space β] [complete_space α] [complete_space β] :
  complete_space (α × β) :=
{ complete := λ f hf,
    let ⟨x1, hx1⟩ := complete_space.complete $ hf.map uniform_continuous_fst in
    let ⟨x2, hx2⟩ := complete_space.complete $ hf.map uniform_continuous_snd in
    ⟨(x1, x2), by rw [nhds_prod_eq, filter.prod_def];
      from filter.le_lift (λ s hs, filter.le_lift' $ λ t ht,
        have H1 : prod.fst ⁻¹' s ∈ f.sets := hx1 hs,
        have H2 : prod.snd ⁻¹' t ∈ f.sets := hx2 ht,
        filter.inter_mem H1 H2)⟩ }

/--If `univ` is complete, the space is a complete space -/
lemma complete_space_of_is_complete_univ (h : is_complete (univ : set α)) : complete_space α :=
⟨λ f hf, let ⟨x, _, hx⟩ := h f hf ((@principal_univ α).symm ▸ le_top) in ⟨x, hx⟩⟩

lemma complete_space_iff_is_complete_univ :
  complete_space α ↔ is_complete (univ : set α) :=
⟨@complete_univ α _, complete_space_of_is_complete_univ⟩

lemma cauchy_iff_exists_le_nhds [complete_space α] {l : filter α} [ne_bot l] :
  cauchy l ↔ (∃x, l ≤ 𝓝 x) :=
⟨complete_space.complete, assume ⟨x, hx⟩, cauchy_nhds.mono hx⟩

lemma cauchy_map_iff_exists_tendsto [complete_space α] {l : filter β} {f : β → α} [ne_bot l] :
  cauchy (l.map f) ↔ (∃x, tendsto f l (𝓝 x)) :=
cauchy_iff_exists_le_nhds

/-- A Cauchy sequence in a complete space converges -/
theorem cauchy_seq_tendsto_of_complete [semilattice_sup β] [complete_space α]
  {u : β → α} (H : cauchy_seq u) : ∃x, tendsto u at_top (𝓝 x) :=
complete_space.complete H

/-- If `K` is a complete subset, then any cauchy sequence in `K` converges to a point in `K` -/
lemma cauchy_seq_tendsto_of_is_complete [semilattice_sup β] {K : set α} (h₁ : is_complete K)
  {u : β → α} (h₂ : ∀ n, u n ∈ K) (h₃ : cauchy_seq u) : ∃ v ∈ K, tendsto u at_top (𝓝 v) :=
h₁ _ h₃ $ le_principal_iff.2 $ mem_map_iff_exists_image.2 ⟨univ, univ_mem,
  by { simp only [image_univ], rintros _ ⟨n, rfl⟩, exact h₂ n }⟩

theorem cauchy.le_nhds_Lim [complete_space α] [nonempty α] {f : filter α} (hf : cauchy f) :
  f ≤ 𝓝 (Lim f) :=
le_nhds_Lim (complete_space.complete hf)

theorem cauchy_seq.tendsto_lim [semilattice_sup β] [complete_space α] [nonempty α] {u : β → α}
  (h : cauchy_seq u) :
  tendsto u at_top (𝓝 $ lim at_top u) :=
h.le_nhds_Lim

lemma is_closed.is_complete [complete_space α] {s : set α}
  (h : is_closed s) : is_complete s :=
λ f cf fs, let ⟨x, hx⟩ := complete_space.complete cf in
⟨x, is_closed_iff_cluster_pt.mp h x (cf.left.mono (le_inf hx fs)), hx⟩

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def totally_bounded (s : set α) : Prop :=
∀d ∈ 𝓤 α, ∃t : set α, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d})

theorem totally_bounded_iff_subset {s : set α} : totally_bounded s ↔
  ∀d ∈ 𝓤 α, ∃t ⊆ s, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}) :=
⟨λ H d hd, begin
  rcases comp_symm_of_uniformity hd with ⟨r, hr, rs, rd⟩,
  rcases H r hr with ⟨k, fk, ks⟩,
  let u := k ∩ {y | ∃ x ∈ s, (x, y) ∈ r},
  choose hk f hfs hfr using λ x : u, x.coe_prop,
  refine ⟨range f, _, _, _⟩,
  { exact range_subset_iff.2 hfs },
  { haveI : fintype u := (fk.inter_of_left _).fintype,
    exact finite_range f },
  { intros x xs,
    obtain ⟨y, hy, xy⟩ : ∃ y ∈ k, (x, y) ∈ r, from mem_bUnion_iff.1 (ks xs),
    rw [bUnion_range, mem_Union],
    set z : ↥u := ⟨y, hy, ⟨x, xs, xy⟩⟩,
    exact ⟨z, rd $ mem_comp_rel.2 ⟨y, xy, rs (hfr z)⟩⟩ }
end,
λ H d hd, let ⟨t, _, ht⟩ := H d hd in ⟨t, ht⟩⟩

lemma totally_bounded_of_forall_symm {s : set α}
  (h : ∀ V ∈ 𝓤 α, symmetric_rel V → ∃ t : set α, finite t ∧ s ⊆ ⋃ y ∈ t, ball y V) :
totally_bounded s :=
begin
  intros V V_in,
  rcases h _ (symmetrize_mem_uniformity V_in) (symmetric_symmetrize_rel V) with ⟨t, tfin, h⟩,
  refine ⟨t, tfin, subset.trans h _⟩,
  mono,
  intros x x_in z z_in,
  exact z_in.right
end

lemma totally_bounded_subset {s₁ s₂ : set α} (hs : s₁ ⊆ s₂)
  (h : totally_bounded s₂) : totally_bounded s₁ :=
assume d hd, let ⟨t, ht₁, ht₂⟩ := h d hd in ⟨t, ht₁, subset.trans hs ht₂⟩

lemma totally_bounded_empty : totally_bounded (∅ : set α) :=
λ d hd, ⟨∅, finite_empty, empty_subset _⟩

/-- The closure of a totally bounded set is totally bounded. -/
lemma totally_bounded.closure {s : set α} (h : totally_bounded s) :
  totally_bounded (closure s) :=
assume t ht,
let ⟨t', ht', hct', htt'⟩ := mem_uniformity_is_closed ht, ⟨c, hcf, hc⟩ := h t' ht' in
⟨c, hcf,
  calc closure s ⊆ closure (⋃ (y : α) (H : y ∈ c), {x : α | (x, y) ∈ t'}) : closure_mono hc
    ... = _ : is_closed.closure_eq $ is_closed_bUnion hcf $ assume i hi,
      continuous_iff_is_closed.mp (continuous_id.prod_mk continuous_const) _ hct'
    ... ⊆ _ : bUnion_subset $ assume i hi, subset.trans (assume x, @htt' (x, i))
      (subset_bUnion_of_mem hi)⟩

/-- The image of a totally bounded set under a unifromly continuous map is totally bounded. -/
lemma totally_bounded.image [uniform_space β] {f : α → β} {s : set α}
  (hs : totally_bounded s) (hf : uniform_continuous f) : totally_bounded (f '' s) :=
assume t ht,
have {p:α×α | (f p.1, f p.2) ∈ t} ∈ 𝓤 α,
  from hf ht,
let ⟨c, hfc, hct⟩ := hs _ this in
⟨f '' c, hfc.image f,
  begin
    simp [image_subset_iff],
    simp [subset_def] at hct,
    intros x hx, simp,
    exact hct x hx
  end⟩

lemma ultrafilter.cauchy_of_totally_bounded {s : set α} (f : ultrafilter α)
  (hs : totally_bounded s) (h : ↑f ≤ 𝓟 s) : cauchy (f : filter α) :=
⟨f.ne_bot', assume t ht,
  let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht in
  let ⟨i, hi, hs_union⟩ := hs t' ht'₁ in
  have (⋃y∈i, {x | (x,y) ∈ t'}) ∈ f,
    from mem_of_superset (le_principal_iff.mp h) hs_union,
  have ∃y∈i, {x | (x,y) ∈ t'} ∈ f,
    from (ultrafilter.finite_bUnion_mem_iff hi).1 this,
  let ⟨y, hy, hif⟩ := this in
  have set.prod {x | (x,y) ∈ t'} {x | (x,y) ∈ t'} ⊆ comp_rel t' t',
    from assume ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩,
      ⟨y, h₁, ht'_symm h₂⟩,
  mem_of_superset (prod_mem_prod hif hif) (subset.trans this ht'_t)⟩

lemma totally_bounded_iff_filter {s : set α} :
  totally_bounded s ↔ (∀f, ne_bot f → f ≤ 𝓟 s → ∃c ≤ f, cauchy c) :=
begin
  split,
  { introsI H f hf hfs,
    exact ⟨ultrafilter.of f, ultrafilter.of_le f,
      (ultrafilter.of f).cauchy_of_totally_bounded H ((ultrafilter.of_le f).trans hfs)⟩ },
  { intros H d hd,
    contrapose! H with hd_cover,
    set f := ⨅ t : finset α, 𝓟 (s \ ⋃ y ∈ t, {x | (x, y) ∈ d}),
    have : ne_bot f,
    { refine infi_ne_bot_of_directed' (directed_of_sup _) _,
      { intros t₁ t₂ h,
        exact principal_mono.2 (diff_subset_diff_right $ bUnion_subset_bUnion_left h) },
      { intro t,
        simpa [nonempty_diff] using hd_cover t t.finite_to_set } },
    have : f ≤ 𝓟 s, from infi_le_of_le ∅ (by simp),
    refine ⟨f, ‹_›, ‹_›, λ c hcf hc, _⟩,
    rcases mem_prod_same_iff.1 (hc.2 hd) with ⟨m, hm, hmd⟩,
    have : m ∩ s ∈ c, from inter_mem hm (le_principal_iff.mp (hcf.trans ‹_›)),
    rcases hc.1.nonempty_of_mem this with ⟨y, hym, hys⟩,
    set ys := ⋃ y' ∈ ({y} : finset α), {x | (x, y') ∈ d},
    have : m ⊆ ys, by simpa [ys] using λ x hx, hmd (mk_mem_prod hx hym),
    have : c ≤ 𝓟 (s \ ys) := hcf.trans (infi_le_of_le {y} le_rfl),
    refine hc.1.ne (empty_mem_iff_bot.mp _),
    filter_upwards [le_principal_iff.1 this, hm],
    refine λ x hx hxm, hx.2 _,
    simpa [ys] using hmd (mk_mem_prod hxm hym) }
end

lemma totally_bounded_iff_ultrafilter {s : set α} :
  totally_bounded s ↔ (∀f : ultrafilter α, ↑f ≤ 𝓟 s → cauchy (f : filter α)) :=
begin
  refine ⟨λ hs f, f.cauchy_of_totally_bounded hs, λ H, totally_bounded_iff_filter.2 _⟩,
  introsI f hf hfs,
  exact ⟨ultrafilter.of f, ultrafilter.of_le f, H _ ((ultrafilter.of_le f).trans hfs)⟩
end

lemma compact_iff_totally_bounded_complete {s : set α} :
  is_compact s ↔ totally_bounded s ∧ is_complete s :=
⟨λ hs, ⟨totally_bounded_iff_ultrafilter.2 (λ f hf,
    let ⟨x, xs, fx⟩ := is_compact_iff_ultrafilter_le_nhds.1 hs f hf in cauchy_nhds.mono fx),
  λ f fc fs,
    let ⟨a, as, fa⟩ := @hs f fc.1 fs in
    ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
 λ ⟨ht, hc⟩, is_compact_iff_ultrafilter_le_nhds.2
   (λf hf, hc _ (totally_bounded_iff_ultrafilter.1 ht f hf) hf)⟩

lemma is_compact.totally_bounded {s : set α} (h : is_compact s) : totally_bounded s :=
(compact_iff_totally_bounded_complete.1 h).1

lemma is_compact.is_complete {s : set α} (h : is_compact s) : is_complete s :=
(compact_iff_totally_bounded_complete.1 h).2

@[priority 100] -- see Note [lower instance priority]
instance complete_of_compact {α : Type u} [uniform_space α] [compact_space α] : complete_space α :=
⟨λf hf, by simpa using (compact_iff_totally_bounded_complete.1 compact_univ).2 f hf⟩

lemma compact_of_totally_bounded_is_closed [complete_space α] {s : set α}
  (ht : totally_bounded s) (hc : is_closed s) : is_compact s :=
(@compact_iff_totally_bounded_complete α _ s).2 ⟨ht, hc.is_complete⟩

/-!
### Sequentially complete space

In this section we prove that a uniform space is complete provided that it is sequentially complete
(i.e., any Cauchy sequence converges) and its uniformity filter admits a countable generating set.
In particular, this applies to (e)metric spaces, see the files `topology/metric_space/emetric_space`
and `topology/metric_space/basic`.

More precisely, we assume that there is a sequence of entourages `U_n` such that any other
entourage includes one of `U_n`. Then any Cauchy filter `f` generates a decreasing sequence of
sets `s_n ∈ f` such that `s_n × s_n ⊆ U_n`. Choose a sequence `x_n∈s_n`. It is easy to show
that this is a Cauchy sequence. If this sequence converges to some `a`, then `f ≤ 𝓝 a`. -/

namespace sequentially_complete

variables {f : filter α} (hf : cauchy f) {U : ℕ → set (α × α)}
  (U_mem : ∀ n, U n ∈ 𝓤 α) (U_le : ∀ s ∈ 𝓤 α, ∃ n, U n ⊆ s)

open set finset

noncomputable theory

/-- An auxiliary sequence of sets approximating a Cauchy filter. -/
def set_seq_aux (n : ℕ) : {s : set α // ∃ (_ : s ∈ f), s.prod s ⊆ U n } :=
indefinite_description _ $ (cauchy_iff.1 hf).2 (U n) (U_mem n)

/-- Given a Cauchy filter `f` and a sequence `U` of entourages, `set_seq` provides
an antitone sequence of sets `s n ∈ f` such that `(s n).prod (s n) ⊆ U`. -/
def set_seq (n : ℕ) : set α :=  ⋂ m ∈ Iic n, (set_seq_aux hf U_mem m).val

lemma set_seq_mem (n : ℕ) : set_seq hf U_mem n ∈ f :=
(bInter_mem (finite_le_nat n)).2 (λ m _, (set_seq_aux hf U_mem m).2.fst)

lemma set_seq_mono ⦃m n : ℕ⦄ (h : m ≤ n) : set_seq hf U_mem n ⊆ set_seq hf U_mem m :=
bInter_subset_bInter_left (λ k hk, le_trans hk h)

lemma set_seq_sub_aux (n : ℕ) : set_seq hf U_mem n ⊆ set_seq_aux hf U_mem n :=
bInter_subset_of_mem right_mem_Iic

lemma set_seq_prod_subset {N m n} (hm : N ≤ m) (hn : N ≤ n) :
  (set_seq hf U_mem m).prod (set_seq hf U_mem n) ⊆ U N :=
begin
  assume p hp,
  refine (set_seq_aux hf U_mem N).2.snd ⟨_, _⟩;
    apply set_seq_sub_aux,
  exact set_seq_mono hf U_mem hm hp.1,
  exact set_seq_mono hf U_mem hn hp.2
end

/-- A sequence of points such that `seq n ∈ set_seq n`. Here `set_seq` is an antitone
sequence of sets `set_seq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq (n : ℕ) : α := some $ hf.1.nonempty_of_mem (set_seq_mem hf U_mem n)

lemma seq_mem (n : ℕ) : seq hf U_mem n ∈ set_seq hf U_mem n :=
some_spec $ hf.1.nonempty_of_mem (set_seq_mem hf U_mem n)

lemma seq_pair_mem ⦃N m n : ℕ⦄ (hm : N ≤ m) (hn : N ≤ n) :
  (seq hf U_mem m, seq hf U_mem n) ∈ U N :=
set_seq_prod_subset hf U_mem hm hn ⟨seq_mem hf U_mem m, seq_mem hf U_mem n⟩

include U_le

theorem seq_is_cauchy_seq : cauchy_seq $ seq hf U_mem :=
cauchy_seq_of_controlled U U_le $ seq_pair_mem hf U_mem

/-- If the sequence `sequentially_complete.seq` converges to `a`, then `f ≤ 𝓝 a`. -/
theorem le_nhds_of_seq_tendsto_nhds ⦃a : α⦄ (ha : tendsto (seq hf U_mem) at_top (𝓝 a)) :
  f ≤ 𝓝 a :=
le_nhds_of_cauchy_adhp_aux
begin
  assume s hs,
  rcases U_le s hs with ⟨m, hm⟩,
  rcases tendsto_at_top'.1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩,
  refine ⟨set_seq hf U_mem (max m n), set_seq_mem hf U_mem _, _,
          seq hf U_mem (max m n), _, seq_mem hf U_mem _⟩,
  { have := le_max_left m n,
    exact set.subset.trans (set_seq_prod_subset hf U_mem this this) hm },
  { exact hm (hn _ $ le_max_right m n) }
end

end sequentially_complete

namespace uniform_space

open sequentially_complete

variables [is_countably_generated (𝓤 α)]

/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences (U : ℕ → set (α × α)) (U_mem : ∀ n, U n ∈ 𝓤 α)
  (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, tendsto u at_top (𝓝 a)) :
  complete_space α :=
begin
  obtain ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq,
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α,
    from λ n, inter_mem (U_mem n) (hU'.2 ⟨n, subset.refl _⟩),
  refine ⟨λ f hf, (HU (seq hf Hmem) (λ N m n hm hn, _)).imp $
    le_nhds_of_seq_tendsto_nhds _ _ (λ s hs, _)⟩,
  { rcases (hU'.1 hs) with ⟨N, hN⟩,
    exact ⟨N, subset.trans (inter_subset_right _ _) hN⟩ },
  { exact inter_subset_left _ _ (seq_pair_mem hf Hmem hm hn) }
end

/-- A sequentially complete uniform space with a countable basis of the uniformity filter is
complete. -/
theorem complete_of_cauchy_seq_tendsto
  (H' : ∀ u : ℕ → α, cauchy_seq u → ∃a, tendsto u at_top (𝓝 a)) :
  complete_space α :=
let ⟨U', U'_mono, hU'⟩ := (𝓤 α).exists_antitone_seq in
complete_of_convergent_controlled_sequences U' (λ n, hU'.2 ⟨n, subset.refl _⟩)
  (λ u hu, H' u $ cauchy_seq_of_controlled U' (λ s hs, hU'.1 hs) hu)

variable (α)

@[priority 100]
instance first_countable_topology : first_countable_topology α :=
⟨λ a, by { rw nhds_eq_comap_uniformity, apply_instance }⟩

/-- A separable uniform space with countably generated uniformity filter is second countable:
one obtains a countable basis by taking the balls centered at points in a dense subset,
and with rational "radii" from a countable open symmetric antitone basis of `𝓤 α`. We do not
register this as an instance, as there is already an instance going in the other direction
from second countable spaces to separable spaces, and we want to avoid loops. -/
lemma second_countable_of_separable [separable_space α] : second_countable_topology α :=
begin
  rcases exists_countable_dense α with ⟨s, hsc, hsd⟩,
  obtain ⟨t : ℕ → set (α × α),
    hto : ∀ (i : ℕ), t i ∈ (𝓤 α).sets ∧ is_open (t i) ∧ symmetric_rel (t i),
      h_basis : (𝓤 α).has_antitone_basis t⟩ :=
    (@uniformity_has_basis_open_symmetric α _).exists_antitone_subbasis,
  choose ht_mem hto hts using hto,
  refine ⟨⟨⋃ (x ∈ s), range (λ k, ball x (t k)), hsc.bUnion (λ x hx, countable_range _), _⟩⟩,
  refine (is_topological_basis_of_open_of_nhds _ _).eq_generate_from,
  { simp only [mem_bUnion_iff, mem_range],
    rintros _ ⟨x, hxs, k, rfl⟩,
    exact is_open_ball x (hto k) },
  { intros x V hxV hVo,
    simp only [mem_bUnion_iff, mem_range, exists_prop],
    rcases uniform_space.mem_nhds_iff.1 (is_open.mem_nhds hVo hxV) with ⟨U, hU, hUV⟩,
    rcases comp_symm_of_uniformity hU with ⟨U', hU', hsymm, hUU'⟩,
    rcases h_basis.to_has_basis.mem_iff.1 hU' with ⟨k, -, hk⟩,
    rcases hsd.inter_open_nonempty (ball x $ t k) (is_open_ball x (hto k))
      ⟨x, uniform_space.mem_ball_self _ (ht_mem k)⟩ with ⟨y, hxy, hys⟩,
    refine ⟨_, ⟨y, hys, k, rfl⟩, (hts k).subset hxy, λ z hz, _⟩,
    exact hUV (ball_subset_of_comp_subset (hk hxy) hUU' (hk hz)) }
end

end uniform_space

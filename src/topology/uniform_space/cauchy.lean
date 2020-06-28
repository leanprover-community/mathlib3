/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import topology.uniform_space.basic
import topology.bases
import data.set.intervals
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
def cauchy (f : filter α) := f ≠ ⊥ ∧ filter.prod f f ≤ (𝓤 α)

/-- A set `s` is called *complete*, if any Cauchy filter `f` such that `s ∈ f`
has a limit in `s` (formally, it satisfies `f ≤ 𝓝 x` for some `x ∈ s`). -/
def is_complete (s : set α) := ∀f, cauchy f → f ≤ 𝓟 s → ∃x∈s, f ≤ 𝓝 x

lemma filter.has_basis.cauchy_iff {p : β → Prop} {s : β → set (α × α)} (h : (𝓤 α).has_basis p s)
  {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀ i, p i → ∃ t ∈ f, ∀ x y ∈ t, (x, y) ∈ s i)) :=
and_congr iff.rfl $ (f.basis_sets.prod_self.le_basis_iff h).trans $
  by simp only [subset_def, prod.forall, mem_prod_eq, and_imp, id]

lemma cauchy_iff' {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀ s ∈ 𝓤 α, ∃t∈f, ∀ x y ∈ t, (x, y) ∈ s)) :=
(𝓤 α).basis_sets.cauchy_iff

lemma cauchy_iff {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀ s ∈ 𝓤 α, ∃t∈f, (set.prod t t) ⊆ s)) :=
(𝓤 α).basis_sets.cauchy_iff.trans $
  by simp only [subset_def, prod.forall, mem_prod_eq, and_imp, id]

lemma cauchy_map_iff {l : filter β} {f : β → α} :
  cauchy (l.map f) ↔ (l ≠ ⊥ ∧ tendsto (λp:β×β, (f p.1, f p.2)) (l.prod l) (𝓤 α)) :=
by rw [cauchy, (≠), map_eq_bot_iff, prod_map_map_eq]; refl

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (hg : g ≠ ⊥) (h_le : g ≤ f) : cauchy g :=
⟨hg, le_trans (filter.prod_mono h_le h_le) h_c.right⟩

lemma cauchy_nhds {a : α} : cauchy (𝓝 a) :=
⟨nhds_ne_bot,
  calc filter.prod (𝓝 a) (𝓝 a) =
    (𝓤 α).lift (λs:set (α×α), (𝓤 α).lift' (λt:set(α×α),
      set.prod {y : α | (y, a) ∈ s} {y : α | (a, y) ∈ t})) : nhds_nhds_eq_uniformity_uniformity_prod
    ... ≤ (𝓤 α).lift' (λs:set (α×α), comp_rel s s) :
      le_infi $ assume s, le_infi $ assume hs,
      infi_le_of_le s $ infi_le_of_le hs $ infi_le_of_le s $ infi_le_of_le hs $
      principal_mono.mpr $
      assume ⟨x, y⟩ ⟨(hx : (x, a) ∈ s), (hy : (a, y) ∈ s)⟩, ⟨a, hx, hy⟩
    ... ≤ 𝓤 α : comp_le_uniformity⟩

lemma cauchy_pure {a : α} : cauchy (pure a) :=
cauchy_downwards cauchy_nhds pure_ne_bot (pure_le_nhds a)

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
  apply mem_sets_of_superset t_mem,
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
  obtain ⟨t, t_mem, ht⟩ : ∃ (t : set α) (h : t ∈ f), t.prod t ⊆ s,
    from (cauchy_iff.1 hf).2 s hs,
  use [t, t_mem, ht],
  exact (forall_sets_nonempty_iff_ne_bot.2 adhs _
    (inter_mem_inf_sets (mem_nhds_left x hs) t_mem ))
end

lemma le_nhds_iff_adhp_of_cauchy {f : filter α} {x : α} (hf : cauchy f) :
  f ≤ 𝓝 x ↔ cluster_pt x f :=
⟨assume h, cluster_pt.of_le_nhds h hf.1, le_nhds_of_cauchy_adhp hf⟩

lemma cauchy_map [uniform_space β] {f : filter α} {m : α → β}
  (hm : uniform_continuous m) (hf : cauchy f) : cauchy (map m f) :=
⟨have f ≠ ⊥, from hf.left, by simp; assumption,
  calc filter.prod (map m f) (map m f) =
          map (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_map_map_eq
    ... ≤ map (λp:α×α, (m p.1, m p.2)) (𝓤 α) : map_mono hf.right
    ... ≤ 𝓤 β : hm⟩

lemma cauchy_comap [uniform_space β] {f : filter β} {m : α → β}
  (hm : comap (λp:α×α, (m p.1, m p.2)) (𝓤 β) ≤ 𝓤 α)
  (hf : cauchy f) (hb : comap m f ≠ ⊥) : cauchy (comap m f) :=
⟨hb,
  calc filter.prod (comap m f) (comap m f) =
          comap (λp:α×α, (m p.1, m p.2)) (filter.prod f f) : filter.prod_comap_comap_eq
    ... ≤ comap (λp:α×α, (m p.1, m p.2)) (𝓤 β) : comap_mono hf.right
    ... ≤ 𝓤 α : hm⟩

/-- Cauchy sequences. Usually defined on ℕ, but often it is also useful to say that a function
defined on ℝ is Cauchy at +∞ to deduce convergence. Therefore, we define it in a type class that
is general enough to cover both ℕ and ℝ, which are the main motivating examples. -/
def cauchy_seq [semilattice_sup β] (u : β → α) := cauchy (at_top.map u)

lemma cauchy_seq.mem_entourage {ι : Type*} [nonempty ι] [decidable_linear_order ι] {u : ι → α}
(h : cauchy_seq u) {V : set (α × α)} (hV : V ∈ 𝓤 α) : ∃ k₀, ∀ i j, k₀ ≤ i → k₀ ≤ j → (u i, u j) ∈ V :=
begin
  have := h.right hV,
  obtain ⟨⟨i₀, j₀⟩, H⟩ : ∃ a, ∀ b : ι × ι, b ≥ a → prod.map u u b ∈ V,
    by rwa [prod_map_at_top_eq, mem_map, mem_at_top_sets] at this,
  refine ⟨max i₀ j₀, _⟩,
  intros i j hi hj,
  exact H (i, j) ⟨le_of_max_le_left  hi, le_of_max_le_right hj⟩,
end

lemma cauchy_seq_of_tendsto_nhds [semilattice_sup β] [nonempty β] (f : β → α) {x}
  (hx : tendsto f at_top (𝓝 x)) :
  cauchy_seq f :=
cauchy_downwards cauchy_nhds (map_ne_bot at_top_ne_bot) hx

lemma cauchy_seq_iff_tendsto [nonempty β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ tendsto (prod.map u u) at_top (𝓤 α) :=
cauchy_map_iff.trans $ (and_iff_right at_top_ne_bot).trans $
  by simp only [prod_at_top_at_top_eq, prod.map_def]

/-- If a Cauchy sequence has a convergent subsequence, then it converges. -/
lemma tendsto_nhds_of_cauchy_seq_of_subseq
  [semilattice_sup β] {u : β → α} (hu : cauchy_seq u)
  {ι : Type*} {f : ι → β} {p : filter ι} (hp : p ≠ ⊥)
  (hf : tendsto f p at_top) {a : α} (ha : tendsto (u ∘ f) p (𝓝 a)) :
  tendsto u at_top (𝓝 a) :=
le_nhds_of_cauchy_adhp hu (map_cluster_pt_of_comp hp hf ha)

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

@[nolint ge_or_gt] -- see Note [nolint_ge]
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

lemma cauchy_prod [uniform_space β] {f : filter α} {g : filter β} :
  cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_ne_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).comap p_α ⊓ (g.prod g).comap p_β ≤ (𝓤 α).comap p_α ⊓ (𝓤 β).comap p_β,
    by simpa [uniformity_prod, filter.prod, filter.comap_inf, filter.comap_comap_comp, (∘),
        inf_assoc, inf_comm, inf_left_comm],
  inf_le_inf (filter.comap_mono hf) (filter.comap_mono hg)⟩

instance complete_space.prod [uniform_space β] [complete_space α] [complete_space β] :
  complete_space (α × β) :=
{ complete := λ f hf,
    let ⟨x1, hx1⟩ := complete_space.complete $ cauchy_map uniform_continuous_fst hf in
    let ⟨x2, hx2⟩ := complete_space.complete $ cauchy_map uniform_continuous_snd hf in
    ⟨(x1, x2), by rw [nhds_prod_eq, filter.prod_def];
      from filter.le_lift (λ s hs, filter.le_lift' $ λ t ht,
        have H1 : prod.fst ⁻¹' s ∈ f.sets := hx1 hs,
        have H2 : prod.snd ⁻¹' t ∈ f.sets := hx2 ht,
        filter.inter_mem_sets H1 H2)⟩ }

/--If `univ` is complete, the space is a complete space -/
lemma complete_space_of_is_complete_univ (h : is_complete (univ : set α)) : complete_space α :=
⟨λ f hf, let ⟨x, _, hx⟩ := h f hf ((@principal_univ α).symm ▸ le_top) in ⟨x, hx⟩⟩

lemma complete_space_iff_is_complete_univ :
  complete_space α ↔ is_complete (univ : set α) :=
⟨@complete_univ α _, complete_space_of_is_complete_univ⟩

lemma cauchy_iff_exists_le_nhds [complete_space α] {l : filter α} (hl : l ≠ ⊥) :
  cauchy l ↔ (∃x, l ≤ 𝓝 x) :=
⟨complete_space.complete, assume ⟨x, hx⟩, cauchy_downwards cauchy_nhds hl hx⟩

lemma cauchy_map_iff_exists_tendsto [complete_space α] {l : filter β} {f : β → α}
  (hl : l ≠ ⊥) : cauchy (l.map f) ↔ (∃x, tendsto f l (𝓝 x)) :=
cauchy_iff_exists_le_nhds (map_ne_bot hl)

/-- A Cauchy sequence in a complete space converges -/
theorem cauchy_seq_tendsto_of_complete [semilattice_sup β] [complete_space α]
  {u : β → α} (H : cauchy_seq u) : ∃x, tendsto u at_top (𝓝 x) :=
complete_space.complete H

/-- If `K` is a complete subset, then any cauchy sequence in `K` converges to a point in `K` -/
lemma cauchy_seq_tendsto_of_is_complete [semilattice_sup β] {K : set α} (h₁ : is_complete K)
  {u : β → α} (h₂ : ∀ n, u n ∈ K) (h₃ : cauchy_seq u) : ∃ v ∈ K, tendsto u at_top (𝓝 v) :=
h₁ _ h₃ $ le_principal_iff.2 $ mem_map_sets_iff.2 ⟨univ, univ_mem_sets,
  by { simp only [image_univ], rintros _ ⟨n, rfl⟩, exact h₂ n }⟩

theorem cauchy.le_nhds_Lim [complete_space α] [nonempty α] {f : filter α} (hf : cauchy f) :
  f ≤ 𝓝 (Lim f) :=
Lim_spec (complete_space.complete hf)

theorem cauchy_seq.tendsto_lim [semilattice_sup β] [complete_space α] [nonempty α] {u : β → α}
  (h : cauchy_seq u) :
  tendsto u at_top (𝓝 $ lim at_top u) :=
h.le_nhds_Lim

lemma is_complete_of_is_closed [complete_space α] {s : set α}
  (h : is_closed s) : is_complete s :=
λ f cf fs, let ⟨x, hx⟩ := complete_space.complete cf in
⟨x, is_closed_iff_nhds.mp h x (ne_bot_of_le_ne_bot cf.left (le_inf hx fs)), hx⟩

/-- A set `s` is totally bounded if for every entourage `d` there is a finite
  set of points `t` such that every element of `s` is `d`-near to some element of `t`. -/
def totally_bounded (s : set α) : Prop :=
∀d ∈ 𝓤 α, ∃t : set α, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d})

theorem totally_bounded_iff_subset {s : set α} : totally_bounded s ↔
  ∀d ∈ 𝓤 α, ∃t ⊆ s, finite t ∧ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}) :=
⟨λ H d hd, begin
  rcases comp_symm_of_uniformity hd with ⟨r, hr, rs, rd⟩,
  rcases H r hr with ⟨k, fk, ks⟩,
  let u := {y ∈ k | ∃ x, x ∈ s ∧ (x, y) ∈ r},
  let f : u → α := λ x, classical.some x.2.2,
  have : ∀ x : u, f x ∈ s ∧ (f x, x.1) ∈ r := λ x, classical.some_spec x.2.2,
  refine ⟨range f, _, _, _⟩,
  { exact range_subset_iff.2 (λ x, (this x).1) },
  { have : finite u := fk.subset (λ x h, h.1),
    exact ⟨@set.fintype_range _ _ _ _ this.fintype⟩ },
  { intros x xs,
    have := ks xs, simp at this,
    rcases this with ⟨y, hy, xy⟩,
    let z : coe_sort u := ⟨y, hy, x, xs, xy⟩,
    exact mem_bUnion_iff.2 ⟨_, ⟨z, rfl⟩, rd $ mem_comp_rel.2 ⟨_, xy, rs (this z).2⟩⟩ }
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

lemma totally_bounded_closure {s : set α} (h : totally_bounded s) :
  totally_bounded (closure s) :=
assume t ht,
let ⟨t', ht', hct', htt'⟩ := mem_uniformity_is_closed ht, ⟨c, hcf, hc⟩ := h t' ht' in
⟨c, hcf,
  calc closure s ⊆ closure (⋃ (y : α) (H : y ∈ c), {x : α | (x, y) ∈ t'}) : closure_mono hc
    ... = _ : closure_eq_of_is_closed $ is_closed_bUnion hcf $ assume i hi,
      continuous_iff_is_closed.mp (continuous_id.prod_mk continuous_const) _ hct'
    ... ⊆ _ : bUnion_subset $ assume i hi, subset.trans (assume x, @htt' (x, i))
      (subset_bUnion_of_mem hi)⟩

lemma totally_bounded_image [uniform_space β] {f : α → β} {s : set α}
  (hf : uniform_continuous f) (hs : totally_bounded s) : totally_bounded (f '' s) :=
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

lemma cauchy_of_totally_bounded_of_ultrafilter {s : set α} {f : filter α}
  (hs : totally_bounded s) (hf : is_ultrafilter f) (h : f ≤ 𝓟 s) : cauchy f :=
⟨hf.left, assume t ht,
  let ⟨t', ht'₁, ht'_symm, ht'_t⟩ := comp_symm_of_uniformity ht in
  let ⟨i, hi, hs_union⟩ := hs t' ht'₁ in
  have (⋃y∈i, {x | (x,y) ∈ t'}) ∈ f.sets,
    from mem_sets_of_superset (le_principal_iff.mp h) hs_union,
  have ∃y∈i, {x | (x,y) ∈ t'} ∈ f.sets,
    from mem_of_finite_Union_ultrafilter hf hi this,
  let ⟨y, hy, hif⟩ := this in
  have set.prod {x | (x,y) ∈ t'} {x | (x,y) ∈ t'} ⊆ comp_rel t' t',
    from assume ⟨x₁, x₂⟩ ⟨(h₁ : (x₁, y) ∈ t'), (h₂ : (x₂, y) ∈ t')⟩,
      ⟨y, h₁, ht'_symm h₂⟩,
  (filter.prod f f).sets_of_superset (prod_mem_prod hif hif) (subset.trans this ht'_t)⟩

lemma totally_bounded_iff_filter {s : set α} :
  totally_bounded s ↔ (∀f, f ≠ ⊥ → f ≤ 𝓟 s → ∃c ≤ f, cauchy c) :=
⟨assume : totally_bounded s, assume f hf hs,
  ⟨ultrafilter_of f, ultrafilter_of_le,
    cauchy_of_totally_bounded_of_ultrafilter this
      (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hs)⟩,

  assume h : ∀f, f ≠ ⊥ → f ≤ 𝓟 s → ∃c ≤ f, cauchy c, assume d hd,
  classical.by_contradiction $ assume hs,
  have hd_cover : ∀{t:set α}, finite t → ¬ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}),
    by simpa using hs,
  let
    f := ⨅t:{t : set α // finite t}, 𝓟 (s \ (⋃y∈t.val, {x | (x,y) ∈ d})),
    ⟨a, ha⟩ := (@ne_empty_iff_nonempty α s).1
      (assume h, hd_cover finite_empty $ h.symm ▸ empty_subset _)
  in
  have f ≠ ⊥,
    from infi_ne_bot_of_directed ⟨a⟩
      (assume ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩, ⟨⟨t₁ ∪ t₂, ht₁.union ht₂⟩,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inl,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inr⟩)
      (assume ⟨t, ht⟩, by simp [diff_eq_empty]; exact hd_cover ht),
  have f ≤ 𝓟 s, from infi_le_of_le ⟨∅, finite_empty⟩ $ by simp; exact subset.refl s,
  let
    ⟨c, (hc₁ : c ≤ f), (hc₂ : cauchy c)⟩ := h f ‹f ≠ ⊥› this,
    ⟨m, hm, (hmd : set.prod m m ⊆ d)⟩ := (@mem_prod_same_iff α c d).mp $ hc₂.right hd
  in
  have c ≤ 𝓟 s, from le_trans ‹c ≤ f› this,
  have m ∩ s ∈ c.sets, from inter_mem_sets hm $ le_principal_iff.mp this,
  let ⟨y, hym, hys⟩ := nonempty_of_mem_sets hc₂.left this in
  let ys := (⋃y'∈({y}:set α), {x | (x, y') ∈ d}) in
  have m ⊆ ys,
    from assume y' hy',
      show  y' ∈ (⋃y'∈({y}:set α), {x | (x, y') ∈ d}),
        by simp; exact @hmd (y', y) ⟨hy', hym⟩,
  have c ≤ 𝓟 (s \ ys),
    from le_trans hc₁ $ infi_le_of_le ⟨{y}, finite_singleton _⟩ $ le_refl _,
  have (s \ ys) ∩ (m ∩ s) ∈ c.sets,
    from inter_mem_sets (le_principal_iff.mp this) ‹m ∩ s ∈ c.sets›,
  have ∅ ∈ c.sets,
    from c.sets_of_superset this $ assume x ⟨⟨hxs, hxys⟩, hxm, _⟩, hxys $ ‹m ⊆ ys› hxm,
  hc₂.left $ empty_in_sets_eq_bot.mp this⟩

lemma totally_bounded_iff_ultrafilter {s : set α} :
  totally_bounded s ↔ (∀f, is_ultrafilter f → f ≤ 𝓟 s → cauchy f) :=
⟨assume hs f, cauchy_of_totally_bounded_of_ultrafilter hs,
  assume h, totally_bounded_iff_filter.mpr $ assume f hf hfs,
  have cauchy (ultrafilter_of f),
    from h (ultrafilter_of f) (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hfs),
  ⟨ultrafilter_of f, ultrafilter_of_le, this⟩⟩

lemma compact_iff_totally_bounded_complete {s : set α} :
  compact s ↔ totally_bounded s ∧ is_complete s :=
⟨λ hs, ⟨totally_bounded_iff_ultrafilter.2 (λ f hf1 hf2,
    let ⟨x, xs, fx⟩ := compact_iff_ultrafilter_le_nhds.1 hs f hf1 hf2 in
    cauchy_downwards (cauchy_nhds) (hf1.1) fx),
  λ f fc fs,
    let ⟨a, as, fa⟩ := hs f fc.1 fs in
    ⟨a, as, le_nhds_of_cauchy_adhp fc fa⟩⟩,
λ ⟨ht, hc⟩, compact_iff_ultrafilter_le_nhds.2
  (λf hf hfs, hc _ (totally_bounded_iff_ultrafilter.1 ht _ hf hfs) hfs)⟩

@[priority 100] -- see Note [lower instance priority]
instance complete_of_compact {α : Type u} [uniform_space α] [compact_space α] : complete_space α :=
⟨λf hf, by simpa [principal_univ] using (compact_iff_totally_bounded_complete.1 compact_univ).2 f hf⟩

lemma compact_of_totally_bounded_is_closed [complete_space α] {s : set α}
  (ht : totally_bounded s) (hc : is_closed s) : compact s :=
(@compact_iff_totally_bounded_complete α _ s).2 ⟨ht, is_complete_of_is_closed hc⟩

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
a sequence of monotonically decreasing sets `s n ∈ f` such that `(s n).prod (s n) ⊆ U`. -/
def set_seq (n : ℕ) : set α :=  ⋂ m ∈ Iic n, (set_seq_aux hf U_mem m).val

lemma set_seq_mem (n : ℕ) : set_seq hf U_mem n ∈ f :=
Inter_mem_sets (finite_le_nat n) (λ m _, (set_seq_aux hf U_mem m).2.fst)

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

/-- A sequence of points such that `seq n ∈ set_seq n`. Here `set_seq` is a monotonically
decreasing sequence of sets `set_seq n ∈ f` with diameters controlled by a given sequence
of entourages. -/
def seq (n : ℕ) : α := some $ nonempty_of_mem_sets hf.1 (set_seq_mem hf U_mem n)

lemma seq_mem (n : ℕ) : seq hf U_mem n ∈ set_seq hf U_mem n :=
some_spec $ nonempty_of_mem_sets hf.1 (set_seq_mem hf U_mem n)

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
  rcases (tendsto_at_top' _ _).1 ha _ (mem_nhds_left a (U_mem m)) with ⟨n, hn⟩,
  refine ⟨set_seq hf U_mem (max m n), set_seq_mem hf U_mem _, _,
          seq hf U_mem (max m n), _, seq_mem hf U_mem _⟩,
  { have := le_max_left m n,
    exact set.subset.trans (set_seq_prod_subset hf U_mem this this) hm },
  { exact hm (hn _ $ le_max_right m n) }
end

end sequentially_complete

namespace uniform_space

open sequentially_complete

variables (H : is_countably_generated (𝓤 α))

include H

/-- A uniform space is complete provided that (a) its uniformity filter has a countable basis;
(b) any sequence satisfying a "controlled" version of the Cauchy condition converges. -/
theorem complete_of_convergent_controlled_sequences (U : ℕ → set (α × α)) (U_mem : ∀ n, U n ∈ 𝓤 α)
  (HU : ∀ u : ℕ → α, (∀ N m n, N ≤ m → N ≤ n → (u m, u n) ∈ U N) → ∃ a, tendsto u at_top (𝓝 a)) :
  complete_space α :=
begin
  rcases H.exists_antimono_seq' with ⟨U', U'_mono, hU'⟩,
  have Hmem : ∀ n, U n ∩ U' n ∈ 𝓤 α,
    from λ n, inter_mem_sets (U_mem n) (hU'.2 ⟨n, subset.refl _⟩),
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
let ⟨U', U'_mono, hU'⟩ := H.exists_antimono_seq' in
complete_of_convergent_controlled_sequences H U' (λ n, hU'.2 ⟨n, subset.refl _⟩)
  (λ u hu, H' u $ cauchy_seq_of_controlled U' (λ s hs, hU'.1 hs) hu)

protected lemma first_countable_topology : first_countable_topology α :=
⟨λ a, by { rw nhds_eq_comap_uniformity, exact H.comap (prod.mk a) }⟩

end uniform_space

/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Theory of Cauchy filters in uniform spaces. Complete uniform spaces. Totally bounded subsets.
-/
import topology.uniform_space.basic

open filter topological_space lattice set classical
open_locale classical
variables {α : Type*} {β : Type*} [uniform_space α]
universe u

open_locale uniformity topological_space

/-- A filter `f` is Cauchy if for every entourage `r`, there exists an
  `s ∈ f` such that `s × s ⊆ r`. This is a generalization of Cauchy
  sequences, because if `a : ℕ → α` then the filter of sets containing
  cofinitely many of the `a n` is Cauchy iff `a` is a Cauchy sequence. -/
def cauchy (f : filter α) := f ≠ ⊥ ∧ filter.prod f f ≤ (𝓤 α)

def is_complete (s : set α) := ∀f, cauchy f → f ≤ principal s → ∃x∈s, f ≤ 𝓝 x

lemma cauchy_iff {f : filter α} :
  cauchy f ↔ (f ≠ ⊥ ∧ (∀ s ∈ 𝓤 α, ∃t∈f.sets, set.prod t t ⊆ s)) :=
and_congr (iff.refl _) $ forall_congr $ assume s, forall_congr $ assume hs, mem_prod_same_iff

lemma cauchy_map_iff {l : filter β} {f : β → α} :
  cauchy (l.map f) ↔ (l ≠ ⊥ ∧ tendsto (λp:β×β, (f p.1, f p.2)) (l.prod l) (𝓤 α)) :=
by rw [cauchy, (≠), map_eq_bot_iff, prod_map_map_eq]; refl

lemma cauchy_downwards {f g : filter α} (h_c : cauchy f) (hg : g ≠ ⊥) (h_le : g ≤ f) : cauchy g :=
⟨hg, le_trans (filter.prod_mono h_le h_le) h_c.right⟩

lemma cauchy_nhds {a : α} : cauchy (𝓝 a) :=
⟨nhds_neq_bot,
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
cauchy_downwards cauchy_nhds
  (show principal {a} ≠ ⊥, by simp)
  (pure_le_nhds a)

lemma le_nhds_of_cauchy_adhp {f : filter α} {x : α} (hf : cauchy f)
  (adhs : f ⊓ 𝓝 x ≠ ⊥) : f ≤ 𝓝 x :=
have ∀s∈f.sets, x ∈ closure s,
begin
  intros s hs,
  simp [closure_eq_nhds, inf_comm],
  exact assume h', adhs $ bot_unique $ h' ▸ inf_le_inf (by simp; exact hs) (le_refl _)
end,
calc f ≤ f.lift' (λs:set α, {y | x ∈ closure s ∧ y ∈ closure s}) :
    le_infi $ assume s, le_infi $ assume hs,
    begin
      rw [←forall_sets_neq_empty_iff_neq_bot] at adhs,
      simp [this s hs],
      exact mem_sets_of_superset hs subset_closure
    end
  ... ≤ f.lift' (λs:set α, {y | (x, y) ∈ closure (set.prod s s)}) :
    by simp [closure_prod_eq]; exact le_refl _
  ... = (filter.prod f f).lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) :
  begin
    rw [prod_same_eq],
    rw [lift'_lift'_assoc],
    exact monotone_prod monotone_id monotone_id,
    exact monotone_preimage.comp (assume s t h x h', closure_mono h h')
  end
  ... ≤ (𝓤 α).lift' (λs:set (α×α), {y | (x, y) ∈ closure s}) : lift'_mono hf.right (le_refl _)
  ... = ((𝓤 α).lift' closure).lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
  begin
    rw [lift'_lift'_assoc],
    exact assume s t h, closure_mono h,
    exact monotone_preimage
  end
  ... = (𝓤 α).lift' (λs:set (α×α), {y | (x, y) ∈ s}) :
    by rw [←uniformity_eq_uniformity_closure]
  ... = 𝓝 x :
    by rw [nhds_eq_uniformity]

lemma le_nhds_iff_adhp_of_cauchy {f : filter α} {x : α} (hf : cauchy f) :
  f ≤ 𝓝 x ↔ f ⊓ 𝓝 x ≠ ⊥ :=
⟨assume h, (inf_of_le_left h).symm ▸ hf.left,
le_nhds_of_cauchy_adhp hf⟩

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

lemma cauchy_seq_iff_prod_map [inhabited β] [semilattice_sup β] {u : β → α} :
  cauchy_seq u ↔ map (prod.map u u) at_top ≤ 𝓤 α :=
iff.trans (and_iff_right (map_ne_bot at_top_ne_bot)) (prod_map_at_top_eq u u ▸ iff.rfl)

/-- A complete space is defined here using uniformities. A uniform space
  is complete if every Cauchy filter converges. -/
class complete_space (α : Type u) [uniform_space α] : Prop :=
(complete : ∀{f:filter α}, cauchy f → ∃x, f ≤ 𝓝 x)

lemma complete_univ {α : Type u} [uniform_space α] [complete_space α] :
  is_complete (univ : set α) :=
begin
  assume f hf _,
  rcases complete_space.complete hf with ⟨x, hx⟩,
  exact ⟨x, by simp, hx⟩
end

lemma cauchy_prod [uniform_space β] {f : filter α} {g : filter β} :
  cauchy f → cauchy g → cauchy (filter.prod f g)
| ⟨f_proper, hf⟩ ⟨g_proper, hg⟩ := ⟨filter.prod_neq_bot.2 ⟨f_proper, g_proper⟩,
  let p_α := λp:(α×β)×(α×β), (p.1.1, p.2.1), p_β := λp:(α×β)×(α×β), (p.1.2, p.2.2) in
  suffices (f.prod f).comap p_α ⊓ (g.prod g).comap p_β ≤ (𝓤 α).comap p_α ⊓ (𝓤 β).comap p_β,
    by simpa [uniformity_prod, filter.prod, filter.comap_inf, filter.comap_comap_comp, (∘),
        lattice.inf_assoc, lattice.inf_comm, lattice.inf_left_comm],
  lattice.inf_le_inf (filter.comap_mono hf) (filter.comap_mono hg)⟩

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

theorem le_nhds_lim_of_cauchy {α} [uniform_space α] [complete_space α]
  [inhabited α] {f : filter α} (hf : cauchy f) : f ≤ 𝓝 (lim f) :=
lim_spec (complete_space.complete hf)

lemma is_complete_of_is_closed [complete_space α] {s : set α}
  (h : is_closed s) : is_complete s :=
λ f cf fs, let ⟨x, hx⟩ := complete_space.complete cf in
⟨x, is_closed_iff_nhds.mp h x (neq_bot_of_le_neq_bot cf.left (le_inf hx fs)), hx⟩

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
  { have : finite u := finite_subset fk (λ x h, h.1),
    exact ⟨@set.fintype_range _ _ _ _ this.fintype⟩ },
  { intros x xs,
    have := ks xs, simp at this,
    rcases this with ⟨y, hy, xy⟩,
    let z : coe_sort u := ⟨y, hy, x, xs, xy⟩,
    exact mem_bUnion_iff.2 ⟨_, ⟨z, rfl⟩, rd $ mem_comp_rel.2 ⟨_, xy, rs (this z).2⟩⟩ }
end,
λ H d hd, let ⟨t, _, ht⟩ := H d hd in ⟨t, ht⟩⟩

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
⟨f '' c, finite_image f hfc,
  begin
    simp [image_subset_iff],
    simp [subset_def] at hct,
    intros x hx, simp [-mem_image],
    exact let ⟨i, hi, ht⟩ := hct x hx in ⟨f i, mem_image_of_mem f hi, ht⟩
  end⟩

lemma cauchy_of_totally_bounded_of_ultrafilter {s : set α} {f : filter α}
  (hs : totally_bounded s) (hf : is_ultrafilter f) (h : f ≤ principal s) : cauchy f :=
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
  totally_bounded s ↔ (∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c) :=
⟨assume : totally_bounded s, assume f hf hs,
  ⟨ultrafilter_of f, ultrafilter_of_le,
    cauchy_of_totally_bounded_of_ultrafilter this
      (ultrafilter_ultrafilter_of hf) (le_trans ultrafilter_of_le hs)⟩,

  assume h : ∀f, f ≠ ⊥ → f ≤ principal s → ∃c ≤ f, cauchy c, assume d hd,
  classical.by_contradiction $ assume hs,
  have hd_cover : ∀{t:set α}, finite t → ¬ s ⊆ (⋃y∈t, {x | (x,y) ∈ d}),
    by simpa using hs,
  let
    f := ⨅t:{t : set α // finite t}, principal (s \ (⋃y∈t.val, {x | (x,y) ∈ d})),
    ⟨a, ha⟩ := @exists_mem_of_ne_empty α s
      (assume h, hd_cover finite_empty $ h.symm ▸ empty_subset _)
  in
  have f ≠ ⊥,
    from infi_neq_bot_of_directed ⟨a⟩
      (assume ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩, ⟨⟨t₁ ∪ t₂, finite_union ht₁ ht₂⟩,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inl,
        principal_mono.mpr $ diff_subset_diff_right $ Union_subset_Union $
          assume t, Union_subset_Union_const or.inr⟩)
      (assume ⟨t, ht⟩, by simp [diff_eq_empty]; exact hd_cover ht),
  have f ≤ principal s, from infi_le_of_le ⟨∅, finite_empty⟩ $ by simp; exact subset.refl s,
  let
    ⟨c, (hc₁ : c ≤ f), (hc₂ : cauchy c)⟩ := h f ‹f ≠ ⊥› this,
    ⟨m, hm, (hmd : set.prod m m ⊆ d)⟩ := (@mem_prod_same_iff α c d).mp $ hc₂.right hd
  in
  have c ≤ principal s, from le_trans ‹c ≤ f› this,
  have m ∩ s ∈ c.sets, from inter_mem_sets hm $ le_principal_iff.mp this,
  let ⟨y, hym, hys⟩ := inhabited_of_mem_sets hc₂.left this in
  let ys := (⋃y'∈({y}:set α), {x | (x, y') ∈ d}) in
  have m ⊆ ys,
    from assume y' hy',
      show  y' ∈ (⋃y'∈({y}:set α), {x | (x, y') ∈ d}),
        by simp; exact @hmd (y', y) ⟨hy', hym⟩,
  have c ≤ principal (s - ys),
    from le_trans hc₁ $ infi_le_of_le ⟨{y}, finite_singleton _⟩ $ le_refl _,
  have (s - ys) ∩ (m ∩ s) ∈ c.sets,
    from inter_mem_sets (le_principal_iff.mp this) ‹m ∩ s ∈ c.sets›,
  have ∅ ∈ c.sets,
    from c.sets_of_superset this $ assume x ⟨⟨hxs, hxys⟩, hxm, _⟩, hxys $ ‹m ⊆ ys› hxm,
  hc₂.left $ empty_in_sets_eq_bot.mp this⟩

lemma totally_bounded_iff_ultrafilter {s : set α} :
  totally_bounded s ↔ (∀f, is_ultrafilter f → f ≤ principal s → cauchy f) :=
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

instance complete_of_compact {α : Type u} [uniform_space α] [compact_space α] : complete_space α :=
⟨λf hf, by simpa [principal_univ] using (compact_iff_totally_bounded_complete.1 compact_univ).2 f hf⟩

lemma compact_of_totally_bounded_is_closed [complete_space α] {s : set α}
  (ht : totally_bounded s) (hc : is_closed s) : compact s :=
(@compact_iff_totally_bounded_complete α _ s).2 ⟨ht, is_complete_of_is_closed hc⟩

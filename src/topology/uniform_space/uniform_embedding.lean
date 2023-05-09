/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel, Patrick Massot
-/
import topology.uniform_space.cauchy
import topology.uniform_space.separation
import topology.dense_embedding

/-!
# Uniform embeddings of uniform spaces.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Extension of uniform continuous functions.
-/

open filter topological_space set function classical
open_locale classical uniformity topology filter

section
variables {α : Type*} {β : Type*} {γ : Type*}
          [uniform_space α] [uniform_space β] [uniform_space γ]
universes u v

/-!
### Uniform inducing maps
-/

/-- A map `f : α → β` between uniform spaces is called *uniform inducing* if the uniformity filter
on `α` is the pullback of the uniformity filter on `β` under `prod.map f f`. If `α` is a separated
space, then this implies that `f` is injective, hence it is a `uniform_embedding`. -/
@[mk_iff]
structure uniform_inducing (f : α → β) : Prop :=
(comap_uniformity : comap (λx:α×α, (f x.1, f x.2)) (𝓤 β) = 𝓤 α)

protected lemma uniform_inducing.comap_uniform_space {f : α → β} (hf : uniform_inducing f) :
  ‹uniform_space β›.comap f = ‹uniform_space α› :=
uniform_space_eq hf.1

lemma uniform_inducing_iff' {f : α → β} :
  uniform_inducing f ↔ uniform_continuous f ∧ comap (prod.map f f) (𝓤 β) ≤ 𝓤 α :=
by rw [uniform_inducing_iff, uniform_continuous, tendsto_iff_comap, le_antisymm_iff, and_comm]; refl

protected lemma filter.has_basis.uniform_inducing_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
  (h : (𝓤 α).has_basis p s) (h' : (𝓤 β).has_basis p' s') {f : α → β} :
  uniform_inducing f ↔
    (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
      (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) :=
by simp [uniform_inducing_iff', h.uniform_continuous_iff h', (h'.comap _).le_basis_iff h,
  subset_def]

lemma uniform_inducing.mk' {f : α → β} (h : ∀ s, s ∈ 𝓤 α ↔
    ∃ t ∈ 𝓤 β, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s) : uniform_inducing f :=
⟨by simp [eq_comm, filter.ext_iff, subset_def, h]⟩

lemma uniform_inducing_id : uniform_inducing (@id α) :=
⟨by rw [← prod.map_def, prod.map_id, comap_id]⟩

lemma uniform_inducing.comp {g : β → γ} (hg : uniform_inducing g)
  {f : α → β} (hf : uniform_inducing f) : uniform_inducing (g ∘ f) :=
⟨by rw [← hf.1, ← hg.1, comap_comap]⟩

lemma uniform_inducing.basis_uniformity {f : α → β} (hf : uniform_inducing f)
  {ι : Sort*} {p : ι → Prop} {s : ι → set (β × β)} (H : (𝓤 β).has_basis p s) :
  (𝓤 α).has_basis p (λ i, prod.map f f ⁻¹' s i) :=
hf.1 ▸ H.comap _

lemma uniform_inducing.cauchy_map_iff {f : α → β} (hf : uniform_inducing f) {F : filter α} :
  cauchy (map f F) ↔ cauchy F :=
by simp only [cauchy, map_ne_bot_iff, prod_map_map_eq, map_le_iff_le_comap, ← hf.comap_uniformity]

lemma uniform_inducing_of_compose {f : α → β} {g : β → γ} (hf : uniform_continuous f)
  (hg : uniform_continuous g) (hgf : uniform_inducing (g ∘ f)) : uniform_inducing f :=
begin
  refine ⟨le_antisymm _ hf.le_comap⟩,
  rw [← hgf.1, ← prod.map_def, ← prod.map_def, ← prod.map_comp_map f f g g,
      ← @comap_comap _ _ _ _ (prod.map f f)],
  exact comap_mono hg.le_comap
end

lemma uniform_inducing.uniform_continuous {f : α → β}
  (hf : uniform_inducing f) : uniform_continuous f :=
(uniform_inducing_iff'.1 hf).1

lemma uniform_inducing.uniform_continuous_iff {f : α → β} {g : β → γ} (hg : uniform_inducing g) :
  uniform_continuous f ↔ uniform_continuous (g ∘ f) :=
by { dsimp only [uniform_continuous, tendsto],
  rw [← hg.comap_uniformity, ← map_le_iff_le_comap, filter.map_map] }

protected lemma uniform_inducing.inducing {f : α → β} (h : uniform_inducing f) : inducing f :=
begin
  unfreezingI { obtain rfl := h.comap_uniform_space },
  letI := uniform_space.comap f _,
  exact ⟨rfl⟩
end

lemma uniform_inducing.prod {α' : Type*} {β' : Type*} [uniform_space α'] [uniform_space β']
  {e₁ : α → α'} {e₂ : β → β'} (h₁ : uniform_inducing e₁) (h₂ : uniform_inducing e₂) :
  uniform_inducing (λp:α×β, (e₁ p.1, e₂ p.2)) :=
⟨by simp [(∘), uniformity_prod, h₁.comap_uniformity.symm, h₂.comap_uniformity.symm,
           comap_inf, comap_comap]⟩

lemma uniform_inducing.dense_inducing {f : α → β} (h : uniform_inducing f) (hd : dense_range f) :
  dense_inducing f :=
{ dense   := hd,
  induced := h.inducing.induced }

protected lemma uniform_inducing.injective [t0_space α] {f : α → β} (h : uniform_inducing f) :
  injective f :=
h.inducing.injective

/-- A map `f : α → β` between uniform spaces is a *uniform embedding* if it is uniform inducing and
injective. If `α` is a separated space, then the latter assumption follows from the former. -/
@[mk_iff]
structure uniform_embedding (f : α → β) extends uniform_inducing f : Prop :=
(inj : function.injective f)

theorem uniform_embedding_iff' {f : α → β} :
  uniform_embedding f ↔ injective f ∧ uniform_continuous f ∧ comap (prod.map f f) (𝓤 β) ≤ 𝓤 α :=
by rw [uniform_embedding_iff, and_comm, uniform_inducing_iff']

theorem filter.has_basis.uniform_embedding_iff' {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
  (h : (𝓤 α).has_basis p s) (h' : (𝓤 β).has_basis p' s') {f : α → β} :
  uniform_embedding f ↔ injective f ∧
    (∀ i, p' i → ∃ j, p j ∧ ∀ x y, (x, y) ∈ s j → (f x, f y) ∈ s' i) ∧
      (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) :=
by rw [uniform_embedding_iff, and_comm, h.uniform_inducing_iff h']

theorem filter.has_basis.uniform_embedding_iff {ι ι'} {p : ι → Prop} {p' : ι' → Prop} {s s'}
  (h : (𝓤 α).has_basis p s) (h' : (𝓤 β).has_basis p' s') {f : α → β} :
  uniform_embedding f ↔ injective f ∧ uniform_continuous f ∧
      (∀ j, p j → ∃ i, p' i ∧ ∀ x y, (f x, f y) ∈ s' i → (x, y) ∈ s j) :=
by simp only [h.uniform_embedding_iff' h', h.uniform_continuous_iff h', exists_prop]

lemma uniform_embedding_subtype_val {p : α → Prop} :
  uniform_embedding (subtype.val : subtype p → α) :=
{ comap_uniformity := rfl,
  inj := subtype.val_injective }

lemma uniform_embedding_subtype_coe {p : α → Prop} :
  uniform_embedding (coe : subtype p → α) :=
uniform_embedding_subtype_val

lemma uniform_embedding_set_inclusion {s t : set α} (hst : s ⊆ t) :
  uniform_embedding (inclusion hst) :=
{ comap_uniformity :=
    by { erw [uniformity_subtype, uniformity_subtype, comap_comap], congr },
  inj := inclusion_injective hst }

lemma uniform_embedding.comp {g : β → γ} (hg : uniform_embedding g)
  {f : α → β} (hf : uniform_embedding f) : uniform_embedding (g ∘ f) :=
{ inj := hg.inj.comp hf.inj,
  ..hg.to_uniform_inducing.comp hf.to_uniform_inducing }

lemma equiv.uniform_embedding {α β : Type*} [uniform_space α] [uniform_space β] (f : α ≃ β)
  (h₁ : uniform_continuous f) (h₂ : uniform_continuous f.symm) : uniform_embedding f :=
uniform_embedding_iff'.2 ⟨f.injective, h₁, by rwa [← equiv.prod_congr_apply, ← map_equiv_symm]⟩

theorem uniform_embedding_inl : uniform_embedding (sum.inl : α → α ⊕ β) :=
begin
  refine ⟨⟨_⟩, sum.inl_injective⟩,
  rw [sum.uniformity, comap_sup, comap_map, comap_eq_bot_iff_compl_range.2 _, sup_bot_eq],
  { refine mem_map.2 (univ_mem' _),
    simp },
  { exact sum.inl_injective.prod_map sum.inl_injective }
end

theorem uniform_embedding_inr : uniform_embedding (sum.inr : β → α ⊕ β) :=
begin
  refine ⟨⟨_⟩, sum.inr_injective⟩,
  rw [sum.uniformity, comap_sup, comap_eq_bot_iff_compl_range.2 _, comap_map, bot_sup_eq],
  { exact sum.inr_injective.prod_map sum.inr_injective },
  { refine mem_map.2 (univ_mem' _),
    simp },
end

/-- If the domain of a `uniform_inducing` map `f` is a `separated_space`, then `f` is injective,
hence it is a `uniform_embedding`. -/
protected theorem uniform_inducing.uniform_embedding [t0_space α] {f : α → β}
  (hf : uniform_inducing f) :
  uniform_embedding f :=
⟨hf, hf.injective⟩

theorem uniform_embedding_iff_uniform_inducing [t0_space α] {f : α → β} :
  uniform_embedding f ↔ uniform_inducing f :=
⟨uniform_embedding.to_uniform_inducing, uniform_inducing.uniform_embedding⟩

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is uniform inducing with respect to the discrete uniformity on `α`:
the preimage of `𝓤 β` under `prod.map f f` is the principal filter generated by the diagonal in
`α × α`. -/
lemma comap_uniformity_of_spaced_out {α} {f : α → β} {s : set (β × β)} (hs : s ∈ 𝓤 β)
  (hf : pairwise (λ x y, (f x, f y) ∉ s)) :
  comap (prod.map f f) (𝓤 β) = 𝓟 id_rel :=
begin
  refine le_antisymm _ (@refl_le_uniformity α (uniform_space.comap f ‹_›)),
  calc comap (prod.map f f) (𝓤 β) ≤ comap (prod.map f f) (𝓟 s) : comap_mono (le_principal_iff.2 hs)
  ... = 𝓟 (prod.map f f ⁻¹' s) : comap_principal
  ... ≤ 𝓟 id_rel : principal_mono.2 _,
  rintro ⟨x, y⟩, simpa [not_imp_not] using @hf x y
end

/-- If a map `f : α → β` sends any two distinct points to point that are **not** related by a fixed
`s ∈ 𝓤 β`, then `f` is a uniform embedding with respect to the discrete uniformity on `α`. -/
lemma uniform_embedding_of_spaced_out {α} {f : α → β} {s : set (β × β)} (hs : s ∈ 𝓤 β)
  (hf : pairwise (λ x y, (f x, f y) ∉ s)) :
  @uniform_embedding α β ⊥ ‹_› f :=
begin
  letI : uniform_space α := ⊥, haveI := discrete_topology_bot α,
  haveI : separated_space α := separated_iff_t2.2 infer_instance,
  exact uniform_inducing.uniform_embedding ⟨comap_uniformity_of_spaced_out hs hf⟩
end

protected lemma uniform_embedding.embedding {f : α → β} (h : uniform_embedding f) : embedding f :=
{ induced := h.to_uniform_inducing.inducing.induced,
  inj := h.inj }

lemma uniform_embedding.dense_embedding {f : α → β} (h : uniform_embedding f) (hd : dense_range f) :
  dense_embedding f :=
{ dense   := hd,
  inj     := h.inj,
  induced := h.embedding.induced }

lemma closed_embedding_of_spaced_out {α} [topological_space α] [discrete_topology α]
  [separated_space β] {f : α → β} {s : set (β × β)} (hs : s ∈ 𝓤 β)
  (hf : pairwise (λ x y, (f x, f y) ∉ s)) :
  closed_embedding f :=
begin
  unfreezingI { rcases (discrete_topology.eq_bot α) with rfl }, letI : uniform_space α := ⊥,
  exact { closed_range := is_closed_range_of_spaced_out hs hf,
          .. (uniform_embedding_of_spaced_out hs hf).embedding }
end

lemma closure_image_mem_nhds_of_uniform_inducing
  {s : set (α×α)} {e : α → β} (b : β)
  (he₁ : uniform_inducing e) (he₂ : dense_inducing e) (hs : s ∈ 𝓤 α) :
  ∃ a, closure (e '' {a' | (a, a') ∈ s}) ∈ 𝓝 b :=
have s ∈ comap (λp:α×α, (e p.1, e p.2)) (𝓤 β),
  from he₁.comap_uniformity.symm ▸ hs,
let ⟨t₁, ht₁u, ht₁⟩ := this in
have ht₁ : ∀p:α×α, (e p.1, e p.2) ∈ t₁ → p ∈ s, from ht₁,
let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u in
let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u in
have preimage e {b' | (b, b') ∈ t₂} ∈ comap e (𝓝 b),
  from preimage_mem_comap $ mem_nhds_left b ht₂u,
let ⟨a, (ha : (b, e a) ∈ t₂)⟩ := (he₂.comap_nhds_ne_bot _).nonempty_of_mem this in
have ∀b' (s' : set (β × β)), (b, b') ∈ t → s' ∈ 𝓤 β →
  ({y : β | (b', y) ∈ s'} ∩ e '' {a' : α | (a, a') ∈ s}).nonempty,
  from assume b' s' hb' hs',
  have preimage e {b'' | (b', b'') ∈ s' ∩ t} ∈ comap e (𝓝 b'),
    from preimage_mem_comap $ mem_nhds_left b' $ inter_mem hs' htu,
  let ⟨a₂, ha₂s', ha₂t⟩ := (he₂.comap_nhds_ne_bot _).nonempty_of_mem this in
  have (e a, e a₂) ∈ t₁,
    from ht₂c $ prod_mk_mem_comp_rel (ht₂s ha) $ htc $ prod_mk_mem_comp_rel hb' ha₂t,
  have e a₂ ∈ {b'':β | (b', b'') ∈ s'} ∩ e '' {a' | (a, a') ∈ s},
    from ⟨ha₂s', mem_image_of_mem _ $ ht₁ (a, a₂) this⟩,
  ⟨_, this⟩,
have ∀b', (b, b') ∈ t → ne_bot (𝓝 b' ⊓ 𝓟 (e '' {a' | (a, a') ∈ s})),
begin
  intros b' hb',
  rw [nhds_eq_uniformity, lift'_inf_principal_eq, lift'_ne_bot_iff],
  exact assume s, this b' s hb',
  exact monotone_preimage.inter monotone_const
end,
have ∀b', (b, b') ∈ t → b' ∈ closure (e '' {a' | (a, a') ∈ s}),
  from assume b' hb', by rw [closure_eq_cluster_pts]; exact this b' hb',
⟨a, (𝓝 b).sets_of_superset (mem_nhds_left b htu) this⟩

lemma uniform_embedding_subtype_emb (p : α → Prop) {e : α → β} (ue : uniform_embedding e)
  (de : dense_embedding e) : uniform_embedding (dense_embedding.subtype_emb p e) :=
{ comap_uniformity := by simp [comap_comap, (∘), dense_embedding.subtype_emb,
           uniformity_subtype, ue.comap_uniformity.symm],
  inj := (de.subtype p).inj }

lemma uniform_embedding.prod {α' : Type*} {β' : Type*} [uniform_space α'] [uniform_space β']
  {e₁ : α → α'} {e₂ : β → β'} (h₁ : uniform_embedding e₁) (h₂ : uniform_embedding e₂) :
  uniform_embedding (λp:α×β, (e₁ p.1, e₂ p.2)) :=
{ inj := h₁.inj.prod_map h₂.inj,
  ..h₁.to_uniform_inducing.prod h₂.to_uniform_inducing }

lemma is_complete_of_complete_image {m : α → β} {s : set α} (hm : uniform_inducing m)
  (hs : is_complete (m '' s)) : is_complete s :=
begin
  intros f hf hfs,
  rw le_principal_iff at hfs,
  obtain ⟨_, ⟨x, hx, rfl⟩, hyf⟩ : ∃ y ∈ m '' s, map m f ≤ 𝓝 y,
    from hs (f.map m) (hf.map hm.uniform_continuous)
      (le_principal_iff.2 (image_mem_map hfs)),
  rw [map_le_iff_le_comap, ← nhds_induced, ← hm.inducing.induced] at hyf,
  exact ⟨x, hx, hyf⟩
end

lemma is_complete.complete_space_coe {s : set α} (hs : is_complete s) :
  complete_space s :=
complete_space_iff_is_complete_univ.2 $
  is_complete_of_complete_image uniform_embedding_subtype_coe.to_uniform_inducing $ by simp [hs]

/-- A set is complete iff its image under a uniform inducing map is complete. -/
lemma is_complete_image_iff {m : α → β} {s : set α} (hm : uniform_inducing m) :
  is_complete (m '' s) ↔ is_complete s :=
begin
  refine ⟨is_complete_of_complete_image hm, λ c, _⟩,
  haveI : complete_space s := c.complete_space_coe,
  set m' : s → β := m ∘ coe,
  suffices : is_complete (range m'), by rwa [range_comp, subtype.range_coe] at this,
  have hm' : uniform_inducing m' := hm.comp uniform_embedding_subtype_coe.to_uniform_inducing,
  intros f hf hfm,
  rw filter.le_principal_iff at hfm,
  have cf' : cauchy (comap m' f) :=
    hf.comap' hm'.comap_uniformity.le (ne_bot.comap_of_range_mem hf.1 hfm),
  rcases complete_space.complete cf' with ⟨x, hx⟩,
  rw [hm'.inducing.nhds_eq_comap, comap_le_comap_iff hfm] at hx,
  use [m' x, mem_range_self _, hx]
end

lemma complete_space_iff_is_complete_range {f : α → β} (hf : uniform_inducing f) :
  complete_space α ↔ is_complete (range f) :=
by rw [complete_space_iff_is_complete_univ, ← is_complete_image_iff hf, image_univ]

lemma uniform_inducing.is_complete_range [complete_space α] {f : α → β}
  (hf : uniform_inducing f) :
  is_complete (range f) :=
(complete_space_iff_is_complete_range hf).1 ‹_›

lemma complete_space_congr {e : α ≃ β} (he : uniform_embedding e) :
  complete_space α ↔ complete_space β :=
by rw [complete_space_iff_is_complete_range he.to_uniform_inducing, e.range_eq_univ,
  complete_space_iff_is_complete_univ]

lemma complete_space_coe_iff_is_complete {s : set α} :
  complete_space s ↔ is_complete s :=
(complete_space_iff_is_complete_range uniform_embedding_subtype_coe.to_uniform_inducing).trans $
  by rw [subtype.range_coe]

lemma is_closed.complete_space_coe [complete_space α] {s : set α} (hs : is_closed s) :
  complete_space s :=
hs.is_complete.complete_space_coe

/-- The lift of a complete space to another universe is still complete. -/
instance ulift.complete_space [h : complete_space α] : complete_space (ulift α) :=
begin
  have : uniform_embedding (@equiv.ulift α), from ⟨⟨rfl⟩, ulift.down_injective⟩,
  exact (complete_space_congr this).2 h,
end

lemma complete_space_extension {m : β → α} (hm : uniform_inducing m) (dense : dense_range m)
  (h : ∀f:filter β, cauchy f → ∃x:α, map m f ≤ 𝓝 x) : complete_space α :=
⟨assume (f : filter α), assume hf : cauchy f,
let
  p : set (α × α) → set α → set α := λs t, {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s},
  g := (𝓤 α).lift (λs, f.lift' (p s))
in
have mp₀ : monotone p,
  from assume a b h t s ⟨x, xs, xa⟩, ⟨x, xs, h xa⟩,
have mp₁ : ∀{s}, monotone (p s),
  from assume s a b h x ⟨y, ya, yxs⟩, ⟨y, h ya, yxs⟩,

have f ≤ g, from
  le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
  le_principal_iff.mpr $
  mem_of_superset ht $ assume x hx, ⟨x, hx, refl_mem_uniformity hs⟩,

have ne_bot g, from hf.left.mono this,

have ne_bot (comap m g), from comap_ne_bot $ assume t ht,
  let ⟨t', ht', ht_mem⟩ := (mem_lift_sets $ monotone_lift' monotone_const mp₀).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem in
  let ⟨x, (hx : x ∈ t'')⟩ := hf.left.nonempty_of_mem ht'' in
  have h₀ : ne_bot (𝓝[range m] x),
    from dense.nhds_within_ne_bot x,
  have h₁ : {y | (x, y) ∈ t'} ∈ 𝓝[range m] x,
    from @mem_inf_of_left α (𝓝 x) (𝓟 (range m)) _ $ mem_nhds_left x ht',
  have h₂ : range m ∈ 𝓝[range m] x,
    from @mem_inf_of_right α (𝓝 x) (𝓟 (range m)) _ $ subset.refl _,
  have {y | (x, y) ∈ t'} ∩ range m ∈ 𝓝[range m] x,
    from @inter_mem α (𝓝[range m] x) _ _ h₁ h₂,
  let ⟨y, xyt', b, b_eq⟩ := h₀.nonempty_of_mem this in
  ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩,

have cauchy g, from
  ⟨‹ne_bot g›, assume s hs,
  let
    ⟨s₁, hs₁, (comp_s₁ : comp_rel s₁ s₁ ⊆ s)⟩ := comp_mem_uniformity_sets hs,
    ⟨s₂, hs₂, (comp_s₂ : comp_rel s₂ s₂ ⊆ s₁)⟩ := comp_mem_uniformity_sets hs₁,
    ⟨t, ht, (prod_t : t ×ˢ t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
  in
  have hg₁ : p (preimage prod.swap s₁) t ∈ g,
    from mem_lift (symm_le_uniformity hs₁) $ @mem_lift' α α f _ t ht,
  have hg₂ : p s₂ t ∈ g,
    from mem_lift hs₂ $ @mem_lift' α α f _ t ht,
  have hg : p (prod.swap ⁻¹' s₁) t ×ˢ p s₂ t ∈ g ×ᶠ g,
    from @prod_mem_prod α α _ _ g g hg₁ hg₂,
  (g ×ᶠ g).sets_of_superset hg
    (assume ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩,
      have (c₁, c₂) ∈ t ×ˢ t, from ⟨c₁t, c₂t⟩,
      comp_s₁ $ prod_mk_mem_comp_rel hc₁ $
      comp_s₂ $ prod_mk_mem_comp_rel (prod_t this) hc₂)⟩,

have cauchy (filter.comap m g),
  from ‹cauchy g›.comap' (le_of_eq hm.comap_uniformity) ‹_›,

let ⟨x, (hx : map m (filter.comap m g) ≤ 𝓝 x)⟩ := h _ this in
have cluster_pt x (map m (filter.comap m g)),
  from (le_nhds_iff_adhp_of_cauchy (this.map hm.uniform_continuous)).mp hx,
have cluster_pt x g,
  from  this.mono map_comap_le,

⟨x, calc f ≤ g : by assumption
  ... ≤ 𝓝 x : le_nhds_of_cauchy_adhp ‹cauchy g› this⟩⟩

lemma totally_bounded_preimage {f : α → β} {s : set β} (hf : uniform_embedding f)
  (hs : totally_bounded s) : totally_bounded (f ⁻¹' s) :=
λ t ht, begin
  rw ← hf.comap_uniformity at ht,
  rcases mem_comap.2 ht with ⟨t', ht', ts⟩,
  rcases totally_bounded_iff_subset.1
    (totally_bounded_subset (image_preimage_subset f s) hs) _ ht' with ⟨c, cs, hfc, hct⟩,
  refine ⟨f ⁻¹' c, hfc.preimage (hf.inj.inj_on _), λ x h, _⟩,
  have := hct (mem_image_of_mem f h), simp at this ⊢,
  rcases this with ⟨z, zc, zt⟩,
  rcases cs zc with ⟨y, yc, rfl⟩,
  exact ⟨y, zc, ts (by exact zt)⟩
end

instance complete_space.sum [complete_space α] [complete_space β] :
  complete_space (α ⊕ β) :=
begin
  rw [complete_space_iff_is_complete_univ, ← range_inl_union_range_inr],
  exact uniform_embedding_inl.to_uniform_inducing.is_complete_range.union
    uniform_embedding_inr.to_uniform_inducing.is_complete_range
end

end

lemma uniform_embedding_comap {α : Type*} {β : Type*} {f : α → β} [u : uniform_space β]
  (hf : function.injective f) : @uniform_embedding α β (uniform_space.comap f u) u f :=
@uniform_embedding.mk _ _ (uniform_space.comap f u) _ _
  (@uniform_inducing.mk _ _ (uniform_space.comap f u) _ _ rfl) hf

/-- Pull back a uniform space structure by an embedding, adjusting the new uniform structure to
make sure that its topology is defeq to the original one. -/
def embedding.comap_uniform_space {α β} [topological_space α] [u : uniform_space β] (f : α → β)
  (h : embedding f) : uniform_space α :=
(u.comap f).replace_topology h.induced

lemma embedding.to_uniform_embedding {α β} [topological_space α] [u : uniform_space β] (f : α → β)
  (h : embedding f) :
  @uniform_embedding α β (h.comap_uniform_space f) u f :=
{ comap_uniformity := rfl,
  inj := h.inj }

section uniform_extension

variables {α : Type*} {β : Type*} {γ : Type*}
          [uniform_space α] [uniform_space β] [uniform_space γ]
          {e : β → α}
          (h_e : uniform_inducing e)
          (h_dense : dense_range e)
          {f : β → γ}
          (h_f : uniform_continuous f)

local notation `ψ` := (h_e.dense_inducing h_dense).extend f

lemma uniformly_extend_exists [complete_space γ] (a : α) :
  ∃c, tendsto f (comap e (𝓝 a)) (𝓝 c) :=
let de := (h_e.dense_inducing h_dense) in
have cauchy (𝓝 a), from cauchy_nhds,
have cauchy (comap e (𝓝 a)), from
  this.comap' (le_of_eq h_e.comap_uniformity) (de.comap_nhds_ne_bot _),
have cauchy (map f (comap e (𝓝 a))), from this.map h_f,
complete_space.complete this

lemma uniform_extend_subtype [complete_space γ]
  {p : α → Prop} {e : α → β} {f : α → γ} {b : β} {s : set α}
  (hf : uniform_continuous (λx:subtype p, f x.val))
  (he : uniform_embedding e) (hd : ∀x:β, x ∈ closure (range e))
  (hb : closure (e '' s) ∈ 𝓝 b) (hs : is_closed s) (hp : ∀x∈s, p x) :
  ∃c, tendsto f (comap e (𝓝 b)) (𝓝 c) :=
have de : dense_embedding e,
  from he.dense_embedding hd,
have de' : dense_embedding (dense_embedding.subtype_emb p e),
  by exact de.subtype p,
have ue' : uniform_embedding (dense_embedding.subtype_emb p e),
  from uniform_embedding_subtype_emb _ he de,
have b ∈ closure (e '' {x | p x}),
  from (closure_mono $ monotone_image $ hp) (mem_of_mem_nhds hb),
let ⟨c, (hc : tendsto (f ∘ subtype.val)
     (comap (dense_embedding.subtype_emb p e) (𝓝 ⟨b, this⟩)) (𝓝 c))⟩ :=
  uniformly_extend_exists ue'.to_uniform_inducing de'.dense hf _ in
begin
  rw [nhds_subtype_eq_comap] at hc,
  simp [comap_comap] at hc,
  change (tendsto (f ∘ @subtype.val α p) (comap (e ∘ @subtype.val α p) (𝓝 b)) (𝓝 c)) at hc,
  rw [←comap_comap, tendsto_comap'_iff] at hc,
  exact ⟨c, hc⟩,
  exact ⟨_, hb, assume x,
    begin
      change e x ∈ (closure (e '' s)) → x ∈ range subtype.val,
      rw [← closure_induced, mem_closure_iff_cluster_pt, cluster_pt, ne_bot_iff,
          nhds_induced, ← de.to_dense_inducing.nhds_eq_comap,
          ← mem_closure_iff_nhds_ne_bot, hs.closure_eq],
      exact assume hxs, ⟨⟨x, hp x hxs⟩, rfl⟩,
    end⟩
end

include h_f

lemma uniformly_extend_spec [complete_space γ] (a : α) :
  tendsto f (comap e (𝓝 a)) (𝓝 (ψ a)) :=
by simpa only [dense_inducing.extend] using tendsto_nhds_lim (uniformly_extend_exists h_e ‹_› h_f _)

lemma uniform_continuous_uniformly_extend [cγ : complete_space γ] : uniform_continuous ψ :=
assume d hd,
let ⟨s, hs, hs_comp⟩ := (mem_lift'_sets $
  monotone_id.comp_rel $ monotone_id.comp_rel monotone_id).mp
    (comp_le_uniformity3 hd) in
have h_pnt : ∀{a m}, m ∈ 𝓝 a → ∃c, c ∈ f '' preimage e m ∧ (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s,
  from assume a m hm,
  have nb : ne_bot (map f (comap e (𝓝 a))),
    from ((h_e.dense_inducing h_dense).comap_nhds_ne_bot _).map _,
  have (f '' preimage e m) ∩ ({c | (c, ψ a) ∈ s } ∩ {c | (ψ a, c) ∈ s }) ∈ map f (comap e (𝓝 a)),
    from inter_mem (image_mem_map $ preimage_mem_comap $ hm)
      (uniformly_extend_spec h_e h_dense h_f _
        (inter_mem (mem_nhds_right _ hs) (mem_nhds_left _ hs))),
  nb.nonempty_of_mem this,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ 𝓤 β,
  from h_f hs,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ comap (λx:β×β, (e x.1, e x.2)) (𝓤 α),
  by rwa [h_e.comap_uniformity.symm] at this,
let ⟨t, ht, ts⟩ := this in
show preimage (λp:(α×α), (ψ p.1, ψ p.2)) d ∈ 𝓤 α,
  from (𝓤 α).sets_of_superset (interior_mem_uniformity ht) $
  assume ⟨x₁, x₂⟩ hx_t,
  have 𝓝 (x₁, x₂) ≤ 𝓟 (interior t),
    from is_open_iff_nhds.mp is_open_interior (x₁, x₂) hx_t,
  have interior t ∈ 𝓝 x₁ ×ᶠ 𝓝 x₂,
    by rwa [nhds_prod_eq, le_principal_iff] at this,
  let ⟨m₁, hm₁, m₂, hm₂, (hm : m₁ ×ˢ m₂ ⊆ interior t)⟩ := mem_prod_iff.mp this in
  let ⟨a, ha₁, _, ha₂⟩ := h_pnt hm₁ in
  let ⟨b, hb₁, hb₂, _⟩ := h_pnt hm₂ in
  have (e ⁻¹' m₁) ×ˢ (e ⁻¹' m₂) ⊆ (λ p : β × β, (f p.1, f p.2)) ⁻¹' s,
    from calc _ ⊆ preimage (λp:(β×β), (e p.1, e p.2)) (interior t) : preimage_mono hm
    ... ⊆ preimage (λp:(β×β), (e p.1, e p.2)) t : preimage_mono interior_subset
    ... ⊆ preimage (λp:(β×β), (f p.1, f p.2)) s : ts,
  have (f '' (e ⁻¹' m₁)) ×ˢ (f '' (e ⁻¹' m₂)) ⊆ s,
    from calc (f '' (e ⁻¹' m₁)) ×ˢ (f '' (e ⁻¹' m₂)) =
      (λp:(β×β), (f p.1, f p.2)) '' ((e ⁻¹' m₁) ×ˢ (e ⁻¹' m₂)) : prod_image_image_eq
    ... ⊆ (λp:(β×β), (f p.1, f p.2)) '' ((λp:(β×β), (f p.1, f p.2)) ⁻¹' s) : monotone_image this
    ... ⊆ s : image_preimage_subset _ _,
  have (a, b) ∈ s, from @this (a, b) ⟨ha₁, hb₁⟩,
  hs_comp $ show (ψ x₁, ψ x₂) ∈ comp_rel s (comp_rel s s),
    from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩

omit h_f

variables [separated_space γ]

lemma uniformly_extend_of_ind (b : β) : ψ (e b) = f b :=
dense_inducing.extend_eq_at _ h_f.continuous.continuous_at

lemma uniformly_extend_unique {g : α → γ} (hg : ∀ b, g (e b) = f b)
  (hc : continuous g) :
  ψ = g :=
dense_inducing.extend_unique _ hg hc

end uniform_extension

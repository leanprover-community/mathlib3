/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Sébastien Gouëzel

Uniform embeddings of uniform spaces. Extension of uniform continuous functions.
-/
import topology.uniform_space.cauchy

open filter topological_space lattice set classical
local attribute [instance, priority 0] prop_decidable
variables {α : Type*} {β : Type*} {γ : Type*} [uniform_space α]
universe u

def uniform_embedding [uniform_space β] (f : α → β) :=
function.injective f ∧
comap (λx:α×α, (f x.1, f x.2)) uniformity = uniformity

theorem uniform_embedding_def [uniform_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ ∀ s, s ∈ (@uniformity α _).sets ↔
    ∃ t ∈ (@uniformity β _).sets, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s :=
by rw [uniform_embedding, eq_comm, filter.ext_iff]; simp [subset_def]

theorem uniform_embedding_def' [uniform_space β] {f : α → β} :
  uniform_embedding f ↔ function.injective f ∧ uniform_continuous f ∧
    ∀ s, s ∈ (@uniformity α _).sets →
      ∃ t ∈ (@uniformity β _).sets, ∀ x y : α, (f x, f y) ∈ t → (x, y) ∈ s :=
by simp [uniform_embedding_def, uniform_continuous_def]; exact
⟨λ ⟨I, H⟩, ⟨I, λ s su, (H _).2 ⟨s, su, λ x y, id⟩, λ s, (H s).1⟩,
 λ ⟨I, H₁, H₂⟩, ⟨I, λ s, ⟨H₂ s,
   λ ⟨t, tu, h⟩, sets_of_superset _ (H₁ t tu) (λ ⟨a, b⟩, h a b)⟩⟩⟩

lemma uniform_embedding.uniform_continuous [uniform_space β] {f : α → β}
  (hf : uniform_embedding f) : uniform_continuous f :=
(uniform_embedding_def'.1 hf).2.1

lemma uniform_embedding.uniform_continuous_iff [uniform_space β] [uniform_space γ] {f : α → β}
  {g : β → γ} (hg : uniform_embedding g) : uniform_continuous f ↔ uniform_continuous (g ∘ f) :=
by simp [uniform_continuous, tendsto]; rw [← hg.2, ← map_le_iff_le_comap, filter.map_map]

lemma uniform_embedding.embedding [uniform_space β] {f : α → β} (h : uniform_embedding f) : embedding f :=
begin
  refine ⟨h.left, eq_of_nhds_eq_nhds $ assume a, _⟩,
  rw [nhds_induced_eq_comap, nhds_eq_uniformity, nhds_eq_uniformity, ← h.right,
    comap_lift'_eq, comap_lift'_eq2];
    { refl <|> exact monotone_preimage }
end

lemma uniform_embedding.dense_embedding [uniform_space β] {f : α → β}
  (h : uniform_embedding f) (hd : ∀x, x ∈ closure (range f)) : dense_embedding f :=
{ dense   := hd,
  inj     := h.left,
  induced := assume a, by rw [h.embedding.2, nhds_induced_eq_comap] }


lemma closure_image_mem_nhds_of_uniform_embedding
  [uniform_space α] [uniform_space β] {s : set (α×α)} {e : α → β} (b : β)
  (he₁ : uniform_embedding e) (he₂ : dense_embedding e) (hs : s ∈ (@uniformity α _).sets) :
  ∃a, closure (e '' {a' | (a, a') ∈ s}) ∈ (nhds b).sets :=
have s ∈ (comap (λp:α×α, (e p.1, e p.2)) $ uniformity).sets,
  from he₁.right.symm ▸ hs,
let ⟨t₁, ht₁u, ht₁⟩ := this in
have ht₁ : ∀p:α×α, (e p.1, e p.2) ∈ t₁ → p ∈ s, from ht₁,
let ⟨t₂, ht₂u, ht₂s, ht₂c⟩ := comp_symm_of_uniformity ht₁u in
let ⟨t, htu, hts, htc⟩ := comp_symm_of_uniformity ht₂u in
have preimage e {b' | (b, b') ∈ t₂} ∈ (comap e $ nhds b).sets,
  from preimage_mem_comap $ mem_nhds_left b ht₂u,
let ⟨a, (ha : (b, e a) ∈ t₂)⟩ := inhabited_of_mem_sets (he₂.comap_nhds_neq_bot) this in
have ∀b' (s' : set (β × β)), (b, b') ∈ t → s' ∈ (@uniformity β _).sets →
  {y : β | (b', y) ∈ s'} ∩ e '' {a' : α | (a, a') ∈ s} ≠ ∅,
  from assume b' s' hb' hs',
  have preimage e {b'' | (b', b'') ∈ s' ∩ t} ∈ (comap e $ nhds b').sets,
    from preimage_mem_comap $ mem_nhds_left b' $ inter_mem_sets hs' htu,
  let ⟨a₂, ha₂s', ha₂t⟩ := inhabited_of_mem_sets (he₂.comap_nhds_neq_bot) this in
  have (e a, e a₂) ∈ t₁,
    from ht₂c $ prod_mk_mem_comp_rel (ht₂s ha) $ htc $ prod_mk_mem_comp_rel hb' ha₂t,
  have e a₂ ∈ {b'':β | (b', b'') ∈ s'} ∩ e '' {a' | (a, a') ∈ s},
    from ⟨ha₂s', mem_image_of_mem _ $ ht₁ (a, a₂) this⟩,
  ne_empty_of_mem this,
have ∀b', (b, b') ∈ t → nhds b' ⊓ principal (e '' {a' | (a, a') ∈ s}) ≠ ⊥,
begin
  intros b' hb',
  rw [nhds_eq_uniformity, lift'_inf_principal_eq, lift'_neq_bot_iff],
  exact assume s, this b' s hb',
  exact monotone_inter monotone_preimage monotone_const
end,
have ∀b', (b, b') ∈ t → b' ∈ closure (e '' {a' | (a, a') ∈ s}),
  from assume b' hb', by rw [closure_eq_nhds]; exact this b' hb',
⟨a, (nhds b).sets_of_superset (mem_nhds_left b htu) this⟩

lemma uniform_embedding_comap {f : α → β} [u : uniform_space β] (hf : function.injective f) :
  @uniform_embedding α β (uniform_space.comap f u) u f :=
⟨hf, rfl⟩

lemma uniform_embedding_subtype_emb {α : Type*} {β : Type*} [uniform_space α] [uniform_space β]
  (p : α → Prop) {e : α → β} (ue : uniform_embedding e) (de : dense_embedding e) :
  uniform_embedding (de.subtype_emb p) :=
⟨(de.subtype p).inj,
  by simp [comap_comap_comp, (∘), dense_embedding.subtype_emb, uniformity_subtype, ue.right.symm]⟩

lemma uniform_embedding.prod {α' : Type*} {β' : Type*}
  [uniform_space α] [uniform_space β] [uniform_space α'] [uniform_space β']
  {e₁ : α → α'} {e₂ : β → β'} (h₁ : uniform_embedding e₁) (h₂ : uniform_embedding e₂) :
  uniform_embedding (λp:α×β, (e₁ p.1, e₂ p.2)) :=
⟨assume ⟨a₁, b₁⟩ ⟨a₂, b₂⟩,
  by simp [prod.mk.inj_iff]; exact assume eq₁ eq₂, ⟨h₁.left eq₁, h₂.left eq₂⟩,
  by simp [(∘), uniformity_prod, h₁.right.symm, h₂.right.symm, comap_inf, comap_comap_comp]⟩

/-- A set is complete iff its image under a uniform embedding is complete. -/
lemma is_complete_image_iff [uniform_space β] {m : α → β} {s : set α}
  (hm : uniform_embedding m) : is_complete (m '' s) ↔ is_complete s :=
begin
  refine ⟨λ c f hf fs, _, λ c f hf fs, _⟩,
  { let f' := map m f,
    have cf' : cauchy f' := cauchy_map (uniform_embedding.uniform_continuous hm) hf,
    have f's : f' ≤ principal (m '' s),
    { simp only [filter.le_principal_iff, set.mem_image, filter.mem_map],
      exact mem_sets_of_superset (filter.le_principal_iff.1 fs) (λx hx, ⟨x, hx, rfl⟩) },
    rcases c f' cf' f's with ⟨y, yms, hy⟩,
    rcases mem_image_iff_bex.1 yms with ⟨x, xs, rfl⟩,
    rw [map_le_iff_le_comap, ← nhds_induced_eq_comap, ← (uniform_embedding.embedding hm).2] at hy,
    exact ⟨x, xs, hy⟩ },
  { rw filter.le_principal_iff at fs,
    let f' := comap m f,
    have cf' : cauchy f',
    { have : comap m f ≠ ⊥,
      { refine comap_neq_bot (λt ht, _),
        have A : t ∩ m '' s ∈ f.sets := filter.inter_mem_sets ht fs,
        have : t ∩ m '' s ≠ ∅,
        { by_contradiction h,
          simp only [not_not, ne.def] at h,
          simpa [h, empty_in_sets_eq_bot, hf.1] using A },
        rcases ne_empty_iff_exists_mem.1 this with ⟨x, ⟨xt, xms⟩⟩,
        rcases mem_image_iff_bex.1 xms with ⟨y, ys, yx⟩,
        rw ← yx at xt,
        exact ⟨y, xt⟩ },
      apply cauchy_comap _ hf this,
      simp only [hm.2, le_refl] },
    have : f' ≤ principal s := by simp [f']; exact
      ⟨m '' s, by simpa using fs, by simp [preimage_image_eq s hm.1]⟩,
    rcases c f' cf' this with ⟨x, xs, hx⟩,
    existsi [m x, mem_image_of_mem m xs],
    rw [(uniform_embedding.embedding hm).2, nhds_induced_eq_comap] at hx,
    calc f = map m f' : (map_comap $ filter.mem_sets_of_superset fs $ image_subset_range _ _).symm
      ... ≤ map m (comap m (nhds (m x))) : map_mono hx
      ... ≤ nhds (m x) : map_comap_le }
end

lemma complete_space_extension [uniform_space β] {m : β → α}
  (hm : uniform_embedding m)
  (dense : ∀x, x ∈ closure (range m))
  (h : ∀f:filter β, cauchy f → ∃x:α, map m f ≤ nhds x) :
  complete_space α :=
⟨assume (f : filter α), assume hf : cauchy f,
let
  p : set (α × α) → set α → set α := λs t, {y : α| ∃x:α, x ∈ t ∧ (x, y) ∈ s},
  g := uniformity.lift (λs, f.lift' (p s))
in
have mp₀ : monotone p,
  from assume a b h t s ⟨x, xs, xa⟩, ⟨x, xs, h xa⟩,
have mp₁ : ∀{s}, monotone (p s),
  from assume s a b h x ⟨y, ya, yxs⟩, ⟨y, h ya, yxs⟩,

have f ≤ g, from
  le_infi $ assume s, le_infi $ assume hs, le_infi $ assume t, le_infi $ assume ht,
  le_principal_iff.mpr $
  mem_sets_of_superset ht $ assume x hx, ⟨x, hx, refl_mem_uniformity hs⟩,

have g ≠ ⊥, from neq_bot_of_le_neq_bot hf.left this,

have comap m g ≠ ⊥, from comap_neq_bot $ assume t ht,
  let ⟨t', ht', ht_mem⟩ := (mem_lift_sets $ monotone_lift' monotone_const mp₀).mp ht in
  let ⟨t'', ht'', ht'_sub⟩ := (mem_lift'_sets mp₁).mp ht_mem in
  let ⟨x, (hx : x ∈ t'')⟩ := inhabited_of_mem_sets hf.left ht'' in
  have h₀ : nhds x ⊓ principal (range m) ≠ ⊥,
    by simp [closure_eq_nhds] at dense; exact dense x,
  have h₁ : {y | (x, y) ∈ t'} ∈ (nhds x ⊓ principal (range m)).sets,
    from @mem_inf_sets_of_left α (nhds x) (principal (range m)) _ $ mem_nhds_left x ht',
  have h₂ : range m ∈ (nhds x ⊓ principal (range m)).sets,
    from @mem_inf_sets_of_right α (nhds x) (principal (range m)) _ $ subset.refl _,
  have {y | (x, y) ∈ t'} ∩ range m ∈ (nhds x ⊓ principal (range m)).sets,
    from @inter_mem_sets α (nhds x ⊓ principal (range m)) _ _ h₁ h₂,
  let ⟨y, xyt', b, b_eq⟩ := inhabited_of_mem_sets h₀ this in
  ⟨b, b_eq.symm ▸ ht'_sub ⟨x, hx, xyt'⟩⟩,

have cauchy g, from
  ⟨‹g ≠ ⊥›, assume s hs,
  let
    ⟨s₁, hs₁, (comp_s₁ : comp_rel s₁ s₁ ⊆ s)⟩ := comp_mem_uniformity_sets hs,
    ⟨s₂, hs₂, (comp_s₂ : comp_rel s₂ s₂ ⊆ s₁)⟩ := comp_mem_uniformity_sets hs₁,
    ⟨t, ht, (prod_t : set.prod t t ⊆ s₂)⟩ := mem_prod_same_iff.mp (hf.right hs₂)
  in
  have hg₁ : p (preimage prod.swap s₁) t ∈ g.sets,
    from mem_lift (symm_le_uniformity hs₁) $ @mem_lift' α α f _ t ht,
  have hg₂ : p s₂ t ∈ g.sets,
    from mem_lift hs₂ $ @mem_lift' α α f _ t ht,
  have hg : set.prod (p (preimage prod.swap s₁) t) (p s₂ t) ∈ (filter.prod g g).sets,
    from @prod_mem_prod α α _ _ g g hg₁ hg₂,
  (filter.prod g g).sets_of_superset hg
    (assume ⟨a, b⟩ ⟨⟨c₁, c₁t, hc₁⟩, ⟨c₂, c₂t, hc₂⟩⟩,
      have (c₁, c₂) ∈ set.prod t t, from ⟨c₁t, c₂t⟩,
      comp_s₁ $ prod_mk_mem_comp_rel hc₁ $
      comp_s₂ $ prod_mk_mem_comp_rel (prod_t this) hc₂)⟩,

have cauchy (filter.comap m g),
  from cauchy_comap (le_of_eq hm.right) ‹cauchy g› (by assumption),

let ⟨x, (hx : map m (filter.comap m g) ≤ nhds x)⟩ := h _ this in
have map m (filter.comap m g) ⊓ nhds x ≠ ⊥,
  from (le_nhds_iff_adhp_of_cauchy (cauchy_map hm.uniform_continuous this)).mp hx,
have g ⊓ nhds x ≠ ⊥,
  from neq_bot_of_le_neq_bot this (inf_le_inf (assume s hs, ⟨s, hs, subset.refl _⟩) (le_refl _)),

⟨x, calc f ≤ g : by assumption
  ... ≤ nhds x : le_nhds_of_cauchy_adhp ‹cauchy g› this⟩⟩

lemma totally_bounded_preimage [uniform_space α] [uniform_space β] {f : α → β} {s : set β}
  (hf : uniform_embedding f) (hs : totally_bounded s) : totally_bounded (f ⁻¹' s) :=
λ t ht, begin
  rw ← hf.2 at ht,
  rcases mem_comap_sets.2 ht with ⟨t', ht', ts⟩,
  rcases totally_bounded_iff_subset.1
    (totally_bounded_subset (image_preimage_subset f s) hs) _ ht' with ⟨c, cs, hfc, hct⟩,
  refine ⟨f ⁻¹' c, finite_preimage hf.1 hfc, λ x h, _⟩,
  have := hct (mem_image_of_mem f h), simp at this ⊢,
  rcases this with ⟨z, zc, zt⟩,
  rcases cs zc with ⟨y, yc, rfl⟩,
  exact ⟨y, zc, ts (by exact zt)⟩
end

section uniform_extension

variables
  [uniform_space β]
  [uniform_space γ]
  {e : β → α}
  (h_e : uniform_embedding e)
  (h_dense : ∀x, x ∈ closure (range e))
  {f : β → γ}
  (h_f : uniform_continuous f)

local notation `ψ` := (h_e.dense_embedding h_dense).extend f

lemma uniformly_extend_of_emb (b : β) : ψ (e b) = f b :=
dense_embedding.extend_e_eq _ b

lemma uniformly_extend_exists [complete_space γ] (a : α) :
  ∃c, tendsto f (comap e (nhds a)) (nhds c) :=
let de := (h_e.dense_embedding h_dense) in
have cauchy (nhds a), from cauchy_nhds,
have cauchy (comap e (nhds a)), from
  cauchy_comap (le_of_eq h_e.right) this de.comap_nhds_neq_bot,
have cauchy (map f (comap e (nhds a))), from
  cauchy_map h_f this,
complete_space.complete this

lemma uniformly_extend_spec [complete_space γ] (h_f : uniform_continuous f) (a : α) :
  tendsto f (comap e (nhds a)) (nhds (ψ a)) :=
let de := (h_e.dense_embedding h_dense) in
begin
  by_cases ha : a ∈ range e,
  { rcases ha with ⟨b, rfl⟩,
    rw [uniformly_extend_of_emb, de.induced],
    exact h_f.continuous.tendsto _ },
  { simp only [dense_embedding.extend, dif_neg ha],
    exact (@lim_spec _ _ (id _) _ $ uniformly_extend_exists h_e h_dense h_f _) }
end

lemma uniform_continuous_uniformly_extend [cγ : complete_space γ] : uniform_continuous ψ :=
assume d hd,
let ⟨s, hs, hs_comp⟩ := (mem_lift'_sets $
  monotone_comp_rel monotone_id $ monotone_comp_rel monotone_id monotone_id).mp (comp_le_uniformity3 hd) in
have h_pnt : ∀{a m}, m ∈ (nhds a).sets → ∃c, c ∈ f '' preimage e m ∧ (c, ψ a) ∈ s ∧ (ψ a, c) ∈ s,
  from assume a m hm,
  have nb : map f (comap e (nhds a)) ≠ ⊥,
    from map_ne_bot (h_e.dense_embedding h_dense).comap_nhds_neq_bot,
  have (f '' preimage e m) ∩ ({c | (c, ψ a) ∈ s } ∩ {c | (ψ a, c) ∈ s }) ∈ (map f (comap e (nhds a))).sets,
    from inter_mem_sets (image_mem_map $ preimage_mem_comap $ hm)
      (uniformly_extend_spec h_e h_dense h_f _ (inter_mem_sets (mem_nhds_right _ hs) (mem_nhds_left _ hs))),
  inhabited_of_mem_sets nb this,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (@uniformity β _).sets,
  from h_f hs,
have preimage (λp:β×β, (f p.1, f p.2)) s ∈ (comap (λx:β×β, (e x.1, e x.2)) uniformity).sets,
  by rwa [h_e.right.symm] at this,
let ⟨t, ht, ts⟩ := this in
show preimage (λp:(α×α), (ψ p.1, ψ p.2)) d ∈ uniformity.sets,
  from (@uniformity α _).sets_of_superset (interior_mem_uniformity ht) $
  assume ⟨x₁, x₂⟩ hx_t,
  have nhds (x₁, x₂) ≤ principal (interior t),
    from is_open_iff_nhds.mp is_open_interior (x₁, x₂) hx_t,
  have interior t ∈ (filter.prod (nhds x₁) (nhds x₂)).sets,
    by rwa [nhds_prod_eq, le_principal_iff] at this,
  let ⟨m₁, hm₁, m₂, hm₂, (hm : set.prod m₁ m₂ ⊆ interior t)⟩ := mem_prod_iff.mp this in
  let ⟨a, ha₁, _, ha₂⟩ := h_pnt hm₁ in
  let ⟨b, hb₁, hb₂, _⟩ := h_pnt hm₂ in
  have set.prod (preimage e m₁) (preimage e m₂) ⊆ preimage (λp:(β×β), (f p.1, f p.2)) s,
    from calc _ ⊆ preimage (λp:(β×β), (e p.1, e p.2)) (interior t) : preimage_mono hm
    ... ⊆ preimage (λp:(β×β), (e p.1, e p.2)) t : preimage_mono interior_subset
    ... ⊆ preimage (λp:(β×β), (f p.1, f p.2)) s : ts,
  have set.prod (f '' preimage e m₁) (f '' preimage e m₂) ⊆ s,
    from calc set.prod (f '' preimage e m₁) (f '' preimage e m₂) =
      (λp:(β×β), (f p.1, f p.2)) '' (set.prod (preimage e m₁) (preimage e m₂)) : prod_image_image_eq
    ... ⊆ (λp:(β×β), (f p.1, f p.2)) '' preimage (λp:(β×β), (f p.1, f p.2)) s : mono_image this
    ... ⊆ s : image_subset_iff.mpr $ subset.refl _,
  have (a, b) ∈ s, from @this (a, b) ⟨ha₁, hb₁⟩,
  hs_comp $ show (ψ x₁, ψ x₂) ∈ comp_rel s (comp_rel s s),
    from ⟨a, ha₂, ⟨b, this, hb₂⟩⟩

lemma uniform_extend_subtype {α : Type*} {β : Type*} {γ : Type*}
  [uniform_space α] [uniform_space β] [uniform_space γ] [complete_space γ]
  {p : α → Prop} {e : α → β} {f : α → γ} {b : β} {s : set α}
  (hf : uniform_continuous (λx:subtype p, f x.val))
  (he : uniform_embedding e) (hd : ∀x:β, x ∈ closure (range e))
  (hb : closure (e '' s) ∈ (nhds b).sets) (hs : is_closed s) (hp : ∀x∈s, p x) :
  ∃c, tendsto f (comap e (nhds b)) (nhds c) :=
have de : dense_embedding e,
  from he.dense_embedding hd,
have de' : dense_embedding (de.subtype_emb p),
  by exact de.subtype p,
have ue' : uniform_embedding (de.subtype_emb p),
  from uniform_embedding_subtype_emb _ he de,
have b ∈ closure (e '' {x | p x}),
  from (closure_mono $ mono_image $ hp) (mem_of_nhds hb),
let ⟨c, (hc : tendsto (f ∘ subtype.val) (comap (de.subtype_emb p) (nhds ⟨b, this⟩)) (nhds c))⟩ :=
  uniformly_extend_exists ue' de'.dense hf _ in
begin
  rw [nhds_subtype_eq_comap] at hc,
  simp [comap_comap_comp] at hc,
  change (tendsto (f ∘ @subtype.val α p) (comap (e ∘ @subtype.val α p) (nhds b)) (nhds c)) at hc,
  rw [←comap_comap_comp, tendsto_comap'_iff] at hc,
  exact ⟨c, hc⟩,
  exact ⟨_, hb, assume x,
    begin
      change e x ∈ (closure (e '' s)) → x ∈ range subtype.val,
      rw [←closure_induced, closure_eq_nhds, mem_set_of_eq, (≠), nhds_induced_eq_comap, de.induced],
      change x ∈ {x | nhds x ⊓ principal s ≠ ⊥} → x ∈ range subtype.val,
      rw [←closure_eq_nhds, closure_eq_of_is_closed hs],
      exact assume hxs, ⟨⟨x, hp x hxs⟩, rfl⟩,
      exact de.inj
    end⟩
end
end uniform_extension

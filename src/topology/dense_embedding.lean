/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.separation

/-!
# Dense embeddings

This file defines three properties of functions:

`dense_range f`      means `f` has dense image;
`dense_inducing i`   means `i` is also `inducing`;
`dense_embedding e`  means `e` is also an `embedding`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a regular (T₃) space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `dense_inducing` (not necessarily injective).

-/

noncomputable theory

open set filter lattice
open_locale classical topological_space

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

section dense_range
variables [topological_space β] [topological_space γ] (f : α → β) (g : β → γ)

/-- `f : α → β` has dense range if its range (image) is a dense subset of β. -/
def dense_range := ∀ x, x ∈ closure (range f)

lemma dense_range_iff_closure_eq : dense_range f ↔ closure (range f) = univ :=
eq_univ_iff_forall.symm

variables {f}

lemma dense_range.comp (hg : dense_range g) (hf : dense_range f) (cg : continuous g) :
  dense_range (g ∘ f) :=
begin
  have : g '' (closure $ range f) ⊆ closure (g '' range f),
    from image_closure_subset_closure_image cg,
  have : closure (g '' closure (range f)) ⊆ closure (g '' range f),
    by simpa [closure_closure] using (closure_mono this),
  intro c,
  rw range_comp,
  apply this,
  rw [(dense_range_iff_closure_eq f).1 hf, image_univ],
  exact hg c
end

/-- If `f : α → β` has dense range and `β` contains some element, then `α` must too. -/
def dense_range.inhabited (df : dense_range f) (b : β) : inhabited α :=
⟨begin
  have := exists_mem_of_ne_empty (mem_closure_iff.1 (df b) _ is_open_univ trivial),
  simp only [mem_range, univ_inter] at this,
  exact classical.some (classical.some_spec this),
 end⟩

lemma dense_range.nonempty (hf : dense_range f) : nonempty α ↔ nonempty β :=
⟨nonempty.map f, λ ⟨b⟩, @nonempty_of_inhabited _ (hf.inhabited b)⟩

lemma dense_range_prod {ι : Type*} {κ : Type*} {f : ι → β} {g : κ → γ}
  (hf : dense_range f) (hg : dense_range g) : dense_range (λ p : ι × κ, (f p.1, g p.2)) :=
have closure (range $ λ p : ι×κ, (f p.1, g p.2)) = set.prod (closure $ range f) (closure $ range g),
    by rw [←closure_prod_eq, prod_range_range_eq],
assume ⟨b, d⟩, this.symm ▸ mem_prod.2 ⟨hf _, hg _⟩
end dense_range

/-- `i : α → β` is "dense inducing" if it has dense range and the topology on `α`
  is the one induced by `i` from the topology on `β`. -/
structure dense_inducing [topological_space α] [topological_space β] (i : α → β)
  extends inducing i : Prop :=
(dense : dense_range i)

namespace dense_inducing
variables [topological_space α] [topological_space β]
variables {i : α → β} (di : dense_inducing i)

lemma nhds_eq_comap (di : dense_inducing i) :
  ∀ a : α, 𝓝 a = comap i (𝓝 $ i a) :=
di.to_inducing.nhds_eq_comap

protected lemma continuous (di : dense_inducing i) : continuous i :=
di.to_inducing.continuous

lemma closure_range : closure (range i) = univ :=
(dense_range_iff_closure_eq _).mp di.dense

lemma self_sub_closure_image_preimage_of_open {s : set β} (di : dense_inducing i) :
  is_open s → s ⊆ closure (i '' (i ⁻¹' s)) :=
begin
  intros s_op b b_in_s,
  rw [image_preimage_eq_inter_range, mem_closure_iff],
  intros U U_op b_in,
  rw ←inter_assoc,
  have ne_e : U ∩ s ≠ ∅ := ne_empty_of_mem ⟨b_in, b_in_s⟩,
  exact (dense_iff_inter_open.1 di.closure_range) _ (is_open_inter U_op s_op) ne_e
end

lemma closure_image_nhds_of_nhds {s : set α} {a : α} (di : dense_inducing i) :
  s ∈ 𝓝 a → closure (i '' s) ∈ 𝓝 (i a) :=
begin
  rw [di.nhds_eq_comap a, mem_comap_sets],
  intro h,
  rcases h with ⟨t, t_nhd, sub⟩,
  rw mem_nhds_sets_iff at t_nhd,
  rcases t_nhd with ⟨U, U_sub, ⟨U_op, e_a_in_U⟩⟩,
  have := calc i ⁻¹' U ⊆ i⁻¹' t : preimage_mono U_sub
                   ... ⊆ s      : sub,
  have := calc U ⊆ closure (i '' (i ⁻¹' U)) : self_sub_closure_image_preimage_of_open di U_op
             ... ⊆ closure (i '' s)         : closure_mono (image_subset i this),
  have U_nhd : U ∈ 𝓝 (i a) := mem_nhds_sets U_op e_a_in_U,
  exact (𝓝 (i a)).sets_of_superset U_nhd this
end

/-- The product of two dense inducings is a dense inducing -/
protected lemma prod [topological_space γ] [topological_space δ]
  {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_inducing e₁) (de₂ : dense_inducing e₂) :
  dense_inducing (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ induced := (de₁.to_inducing.prod_mk de₂.to_inducing).induced,
  dense := dense_range_prod de₁.dense de₂.dense }

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (di : dense_inducing i) (H : tendsto h (𝓝 d) (𝓝 (i a)))
  (comm : h ∘ g = i ∘ f) : tendsto f (comap g (𝓝 d)) (𝓝 a) :=
begin
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le,
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap i (map h (𝓝 d)) ≤  comap i  (𝓝 (i a)) := comap_mono H,
  rw ← di.nhds_eq_comap at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_inf_neq_bot (di : dense_inducing i) {b : β} : 𝓝 b ⊓ principal (range i) ≠ ⊥ :=
begin
  convert di.dense b,
  simp [closure_eq_nhds]
end

lemma comap_nhds_neq_bot (di : dense_inducing i) {b : β} : comap i (𝓝 b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : i ⁻¹' t ⊆ s)⟩,
have t ∩ range i ∈ 𝓝 b ⊓ principal (range i),
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets di.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend (di : dense_inducing i) (f : α → γ) (b : β) : γ :=
@lim _ _ ⟨f (dense_range.inhabited di.dense b).default⟩ (map f (comap i (𝓝 b)))

lemma extend_eq [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : map f (comap i (𝓝 b)) ≤ 𝓝 c) :
  di.extend f b = c :=
@lim_eq _ _ (id _) _ _ _ (by simp; exact comap_nhds_neq_bot di) hf

lemma extend_e_eq [t2_space γ] {f : α → γ} (a : α) (hf : continuous_at f a) :
  di.extend f (i a) = f a :=
extend_eq _ $ di.nhds_eq_comap a ▸ hf

lemma extend_eq_of_cont [t2_space γ] {f : α → γ} (hf : continuous f) (a : α) :
  di.extend f (i a) = f a :=
di.extend_e_eq a (continuous_iff_continuous_at.1 hf a)

lemma tendsto_extend [regular_space γ] {b : β} {f : α → γ} (di : dense_inducing i)
  (hf : {b | ∃c, tendsto f (comap i $ 𝓝 b) (𝓝 c)} ∈ 𝓝 b) :
  tendsto (di.extend f) (𝓝 b) (𝓝 (di.extend f b)) :=
let φ := {b | tendsto f (comap i $ 𝓝 b) (𝓝 $ di.extend f b)} in
have hφ : φ ∈ 𝓝 b,
  from (𝓝 b).sets_of_superset hf $ assume b ⟨c, hc⟩,
    show tendsto f (comap i (𝓝 b)) (𝓝 (di.extend f b)), from (di.extend_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : i ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (i ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)), from
  assume b' hb',
  have 𝓝 b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (comap i (𝓝 b')) ≤ 𝓝 (di.extend f b') ⊓ principal (f '' (i ⁻¹' t)),
    from calc _ ≤ map f (comap i (𝓝 b' ⊓ principal t)) : map_mono $ comap_mono $ le_inf (le_refl _) this
      ... ≤ map f (comap i (𝓝 b')) ⊓ map f (comap i (principal t)) :
        le_inf (map_mono $ comap_mono $ inf_le_left) (map_mono $ comap_mono $ inf_le_right)
      ... ≤ map f (comap i (𝓝 b')) ⊓ principal (f '' (i ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show di.extend f b' ∈ closure (f '' (i ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact di.comap_nhds_neq_bot
  end,
(𝓝 b).sets_of_superset
  (show t ∈ 𝓝 b, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)) : h₂
    ... ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ di.extend f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ di.extend f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_extend [regular_space γ] {f : α → γ} (di : dense_inducing i)
  (hf : ∀b, ∃c, tendsto f (comap i (𝓝 b)) (𝓝 c)) : continuous (di.extend f) :=
continuous_iff_continuous_at.mpr $ assume b, di.tendsto_extend $ univ_mem_sets' hf

lemma mk'
  (i : α → β)
  (c     : continuous i)
  (dense : ∀x, x ∈ closure (range i))
  (H     : ∀ (a:α) s ∈ 𝓝 a,
    ∃t ∈ 𝓝 (i a), ∀ b, i b ∈ t → b ∈ s) :
  dense_inducing i :=
{ induced := (induced_iff_nhds_eq i).2 $
    λ a, le_antisymm (tendsto_iff_comap.1 $ c.tendsto _) (by simpa [le_def] using H a),
  dense := dense }
end dense_inducing

/-- A dense embedding is an embedding with dense image. -/
structure dense_embedding [topological_space α] [topological_space β] (e : α → β)
  extends dense_inducing e : Prop :=
(inj : function.injective e)

theorem dense_embedding.mk'
  [topological_space α] [topological_space β] (e : α → β)
  (c     : continuous e)
  (dense : ∀x, x ∈ closure (range e))
  (inj   : function.injective e)
  (H     : ∀ (a:α) s ∈ 𝓝 a,
    ∃t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
{ inj := inj,
  ..dense_inducing.mk' e c dense H}

namespace dense_embedding
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
variables {e : α → β} (de : dense_embedding e)

lemma inj_iff {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma to_embedding : embedding e :=
{ induced := de.induced,
  inj := de.inj }

/-- The product of two dense embeddings is a dense embedding -/
protected lemma prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁) (de₂ : dense_embedding e₂) :
  dense_embedding (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by simp; exact assume h₁ h₂, ⟨de₁.inj h₁, de₂.inj h₂⟩,
  ..dense_inducing.prod de₁.to_dense_inducing de₂.to_dense_inducing }

def subtype_emb {α : Type*} (p : α → Prop) (e : α → β) (x : {x // p x}) :
  {x // x ∈ closure (e '' {x | p x})} :=
⟨e x.1, subset_closure $ mem_image_of_mem e x.2⟩

protected lemma subtype (p : α → Prop) : dense_embedding (subtype_emb p e) :=
{ dense_embedding .
  dense   := assume ⟨x, hx⟩, closure_subtype.mpr $
    have (λ (x : {x // p x}), e (x.val)) = e ∘ subtype.val, from rfl,
    begin
      rw ← image_univ,
      simp [(image_comp _ _ _).symm, (∘), subtype_emb, -image_univ],
      rw [this, image_comp, subtype.val_image],
      simp,
      assumption
    end,
  inj     := assume ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq $ de.inj $ @@congr_arg subtype.val h,
  induced := (induced_iff_nhds_eq _).2 (assume ⟨x, hx⟩,
    by simp [subtype_emb, nhds_subtype_eq_comap, de.to_inducing.nhds_eq_comap, comap_comap_comp, (∘)]) }

end dense_embedding

lemma is_closed_property [topological_space β] {e : α → β} {p : β → Prop}
  (he : closure (range e) = univ) (hp : is_closed {x | p x}) (h : ∀a, p (e a)) :
  ∀b, p b :=
have univ ⊆ {b | p b},
  from calc univ = closure (range e) : he.symm
    ... ⊆ closure {b | p b} : closure_mono $ range_subset_iff.mpr h
    ... = _ : closure_eq_of_is_closed hp,
assume b, this trivial

lemma is_closed_property2 [topological_space α] [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂)) :
  ∀b₁ b₂, p b₁ b₂ :=
have ∀q:β×β, p q.1 q.2,
  from is_closed_property (he.prod he).to_dense_inducing.closure_range hp $ assume a, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma is_closed_property3 [topological_space α] [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_embedding e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2}) (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from is_closed_property (he.prod $ he.prod he).to_dense_inducing.closure_range hp $
    assume ⟨a₁, a₂, a₃⟩, h _ _ _,
assume b₁ b₂ b₃, this ⟨b₁, b₂, b₃⟩

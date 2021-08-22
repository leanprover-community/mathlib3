/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.separation
import topology.bases

/-!
# Dense embeddings

This file defines three properties of functions:

* `dense_range f`      means `f` has dense image;
* `dense_inducing i`   means `i` is also `inducing`;
* `dense_embedding e`  means `e` is also an `embedding`.

The main theorem `continuous_extend` gives a criterion for a function
`f : X → Z` to a regular (T₃) space Z to extend along a dense embedding
`i : X → Y` to a continuous function `g : Y → Z`. Actually `i` only
has to be `dense_inducing` (not necessarily injective).

-/

noncomputable theory

open set filter
open_locale classical topological_space filter

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

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
di.dense.closure_range

lemma preconnected_space [preconnected_space α] (di : dense_inducing i) : preconnected_space β :=
di.dense.preconnected_space di.continuous

lemma closure_image_mem_nhds {s : set α} {a : α} (di : dense_inducing i) (hs : s ∈ 𝓝 a) :
  closure (i '' s) ∈ 𝓝 (i a) :=
begin
  rw [di.nhds_eq_comap a, ((nhds_basis_opens _).comap _).mem_iff] at hs,
  rcases hs with ⟨U, ⟨haU, hUo⟩, sub : i ⁻¹' U ⊆ s⟩,
  refine mem_of_superset (hUo.mem_nhds haU) _,
  calc U ⊆ closure (i '' (i ⁻¹' U)) : di.dense.subset_closure_image_preimage_of_is_open hUo
     ... ⊆ closure (i '' s)         : closure_mono (image_subset i sub)
end

/-- The product of two dense inducings is a dense inducing -/
protected lemma prod [topological_space γ] [topological_space δ]
  {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_inducing e₁) (de₂ : dense_inducing e₂) :
  dense_inducing (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ induced := (de₁.to_inducing.prod_mk de₂.to_inducing).induced,
  dense := de₁.dense.prod_map de₂.dense }

open topological_space

/-- If the domain of a `dense_inducing` map is a separable space, then so is the codomain. -/
protected lemma separable_space [separable_space α] : separable_space β :=
di.dense.separable_space di.continuous

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (di : dense_inducing i)
  (H : tendsto h (𝓝 d) (𝓝 (i a))) (comm : h ∘ g = i ∘ f) : tendsto f (comap g (𝓝 d)) (𝓝 a) :=
begin
  have lim1 : map g (comap g (𝓝 d)) ≤ 𝓝 d := map_comap_le,
  replace lim1 : map h (map g (comap g (𝓝 d))) ≤ map h (𝓝 d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap i (map h (𝓝 d)) ≤  comap i  (𝓝 (i a)) := comap_mono H,
  rw ← di.nhds_eq_comap at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_within_ne_bot (di : dense_inducing i) (b : β) :
  ne_bot (𝓝[range i] b) :=
di.dense.nhds_within_ne_bot b

lemma comap_nhds_ne_bot (di : dense_inducing i) (b : β) : ne_bot (comap i (𝓝 b)) :=
comap_ne_bot $ λ s hs,
let ⟨_, ⟨ha, a, rfl⟩⟩ := mem_closure_iff_nhds.1 (di.dense b) s hs in ⟨a, ha⟩

variables [topological_space γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend (di : dense_inducing i) (f : α → γ) (b : β) : γ :=
@@lim _ ⟨f (di.dense.some b)⟩ (comap i (𝓝 b)) f

lemma extend_eq_of_tendsto [t2_space γ] {b : β} {c : γ} {f : α → γ}
  (hf : tendsto f (comap i (𝓝 b)) (𝓝 c)) :
  di.extend f b = c :=
by haveI := di.comap_nhds_ne_bot; exact hf.lim_eq

lemma extend_eq_at [t2_space γ] {f : α → γ} (a : α) (hf : continuous_at f a) :
  di.extend f (i a) = f a :=
extend_eq_of_tendsto _ $ di.nhds_eq_comap a ▸ hf

lemma extend_eq [t2_space γ] {f : α → γ} (hf : continuous f) (a : α) :
  di.extend f (i a) = f a :=
di.extend_eq_at a hf.continuous_at

lemma extend_unique_at [t2_space γ] {b : β} {f : α → γ} {g : β → γ} (di : dense_inducing i)
  (hf : ∀ᶠ x in comap i (𝓝 b), g (i x) = f x) (hg : continuous_at g b) :
  di.extend f b = g b :=
begin
  refine di.extend_eq_of_tendsto (λ s hs, mem_map.2 _),
  suffices : ∀ᶠ (x : α) in comap i (𝓝 b), g (i x) ∈ s,
    from hf.mp (this.mono $ λ x hgx hfx, hfx ▸ hgx),
  clear hf f,
  refine eventually_comap.2 ((hg.eventually hs).mono _),
  rintros _ hxs x rfl,
  exact hxs
end

lemma extend_unique [t2_space γ] {f : α → γ} {g : β → γ} (di : dense_inducing i)
  (hf : ∀ x, g (i x) = f x) (hg : continuous g) :
  di.extend f = g :=
funext $ λ b, extend_unique_at di (eventually_of_forall hf) hg.continuous_at

lemma continuous_at_extend [regular_space γ] {b : β} {f : α → γ} (di : dense_inducing i)
  (hf : ∀ᶠ x in 𝓝 b, ∃c, tendsto f (comap i $ 𝓝 x) (𝓝 c)) :
  continuous_at (di.extend f) b :=
begin
  set φ := di.extend f,
  haveI := di.comap_nhds_ne_bot,
  suffices : ∀ V' ∈ 𝓝 (φ b), is_closed V' → φ ⁻¹' V' ∈ 𝓝 b,
    by simpa [continuous_at, (closed_nhds_basis _).tendsto_right_iff],
  intros V' V'_in V'_closed,
  set V₁ := {x | tendsto f (comap i $ 𝓝 x) (𝓝 $ φ x)},
  have V₁_in : V₁ ∈ 𝓝 b,
  { filter_upwards [hf],
    rintros x ⟨c, hc⟩,
    dsimp [V₁, φ],
    rwa di.extend_eq_of_tendsto hc },
  obtain ⟨V₂, V₂_in, V₂_op, hV₂⟩ : ∃ V₂ ∈ 𝓝 b, is_open V₂ ∧ ∀ x ∈ i ⁻¹' V₂, f x ∈ V',
  { simpa [and_assoc] using ((nhds_basis_opens' b).comap i).tendsto_left_iff.mp
                            (mem_of_mem_nhds V₁_in : b ∈ V₁) V' V'_in },
  suffices : ∀ x ∈ V₁ ∩ V₂, φ x ∈ V',
  { filter_upwards [inter_mem V₁_in V₂_in], exact this },
  rintros x ⟨x_in₁, x_in₂⟩,
  have hV₂x : V₂ ∈ 𝓝 x := is_open.mem_nhds V₂_op x_in₂,
  apply V'_closed.mem_of_tendsto x_in₁,
  use V₂,
  tauto,
end

lemma continuous_extend [regular_space γ] {f : α → γ} (di : dense_inducing i)
  (hf : ∀b, ∃c, tendsto f (comap i (𝓝 b)) (𝓝 c)) : continuous (di.extend f) :=
continuous_iff_continuous_at.mpr $ assume b, di.continuous_at_extend $ univ_mem' hf

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
  (dense : dense_range e)
  (inj   : function.injective e)
  (H     : ∀ (a:α) s ∈ 𝓝 a,
    ∃t ∈ 𝓝 (e a), ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
{ inj := inj,
  ..dense_inducing.mk' e c dense H}

namespace dense_embedding
open topological_space
variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]
variables {e : α → β} (de : dense_embedding e)

lemma inj_iff {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma to_embedding : embedding e :=
{ induced := de.induced,
  inj := de.inj }

/-- If the domain of a `dense_embedding` is a separable space, then so is its codomain. -/
protected lemma separable_space [separable_space α] : separable_space β :=
de.to_dense_inducing.separable_space

/-- The product of two dense embeddings is a dense embedding. -/
protected lemma prod {e₁ : α → β} {e₂ : γ → δ} (de₁ : dense_embedding e₁)
  (de₂ : dense_embedding e₂) :
  dense_embedding (λ(p : α × γ), (e₁ p.1, e₂ p.2)) :=
{ inj := assume ⟨x₁, x₂⟩ ⟨y₁, y₂⟩,
    by simp; exact assume h₁ h₂, ⟨de₁.inj h₁, de₂.inj h₂⟩,
  ..dense_inducing.prod de₁.to_dense_inducing de₂.to_dense_inducing }

/-- The dense embedding of a subtype inside its closure. -/
def subtype_emb {α : Type*} (p : α → Prop) (e : α → β) (x : {x // p x}) :
  {x // x ∈ closure (e '' {x | p x})} :=
⟨e x, subset_closure $ mem_image_of_mem e x.prop⟩

protected lemma subtype (p : α → Prop) : dense_embedding (subtype_emb p e) :=
{ dense_embedding .
  dense   := assume ⟨x, hx⟩, closure_subtype.mpr $
    have (λ (x : {x // p x}), e x) = e ∘ coe, from rfl,
    begin
      rw ← image_univ,
      simp [(image_comp _ _ _).symm, (∘), subtype_emb, -image_univ],
      rw [this, image_comp, subtype.coe_image],
      simp,
      assumption
    end,
  inj     := assume ⟨x, hx⟩ ⟨y, hy⟩ h, subtype.eq $ de.inj $ @@congr_arg subtype.val h,
  induced := (induced_iff_nhds_eq _).2 (assume ⟨x, hx⟩,
    by simp [subtype_emb, nhds_subtype_eq_comap, de.to_inducing.nhds_eq_comap, comap_comap, (∘)]) }

end dense_embedding

lemma is_closed_property [topological_space β] {e : α → β} {p : β → Prop}
  (he : dense_range e) (hp : is_closed {x | p x}) (h : ∀a, p (e a)) :
  ∀b, p b :=
have univ ⊆ {b | p b},
  from calc univ = closure (range e) : he.closure_range.symm
    ... ⊆ closure {b | p b} : closure_mono $ range_subset_iff.mpr h
    ... = _ : hp.closure_eq,
assume b, this trivial

lemma is_closed_property2 [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_range e) (hp : is_closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂)) :
  ∀b₁ b₂, p b₁ b₂ :=
have ∀q:β×β, p q.1 q.2,
  from is_closed_property (he.prod_map he) hp $ λ _, h _ _,
assume b₁ b₂, this ⟨b₁, b₂⟩

lemma is_closed_property3 [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_range e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2})
  (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃)) :
  ∀b₁ b₂ b₃, p b₁ b₂ b₃ :=
have ∀q:β×β×β, p q.1 q.2.1 q.2.2,
  from is_closed_property (he.prod_map $ he.prod_map he) hp $ λ _, h _ _ _,
assume b₁ b₂ b₃, this ⟨b₁, b₂, b₃⟩

@[elab_as_eliminator]
lemma dense_range.induction_on [topological_space β] {e : α → β} (he : dense_range e) {p : β → Prop}
  (b₀ : β) (hp : is_closed {b | p b}) (ih : ∀a:α, p $ e a) : p b₀ :=
is_closed_property he hp ih b₀

@[elab_as_eliminator]
lemma dense_range.induction_on₂ [topological_space β] {e : α → β} {p : β → β → Prop}
  (he : dense_range e) (hp : is_closed {q:β×β | p q.1 q.2}) (h : ∀a₁ a₂, p (e a₁) (e a₂))
  (b₁ b₂ : β) : p b₁ b₂ := is_closed_property2 he hp h _ _

@[elab_as_eliminator]
lemma dense_range.induction_on₃ [topological_space β] {e : α → β} {p : β → β → β → Prop}
  (he : dense_range e) (hp : is_closed {q:β×β×β | p q.1 q.2.1 q.2.2})
  (h : ∀a₁ a₂ a₃, p (e a₁) (e a₂) (e a₃))
  (b₁ b₂ b₃ : β) : p b₁ b₂ b₃ := is_closed_property3 he hp h _ _ _

section
variables [topological_space β] [topological_space γ] [t2_space γ]
variables {f : α → β}

/-- Two continuous functions to a t2-space that agree on the dense range of a function are equal. -/
lemma dense_range.equalizer (hfd : dense_range f)
  {g h : β → γ} (hg : continuous g) (hh : continuous h) (H : g ∘ f = h ∘ f) :
  g = h :=
funext $ λ y, hfd.induction_on y (is_closed_eq hg hh) $ congr_fun H
end

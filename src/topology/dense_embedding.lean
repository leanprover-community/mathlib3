/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
import topology.maps topology.separation

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
open_locale classical

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
  ∀ a : α, nhds a = comap i (nhds $ i a) :=
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
  s ∈ nhds a → closure (i '' s) ∈ nhds (i a) :=
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
  have U_nhd : U ∈ nhds (i a) := mem_nhds_sets U_op e_a_in_U,
  exact (nhds (i a)).sets_of_superset U_nhd this
end

variables [topological_space δ] {f : γ → α} {g : γ → δ} {h : δ → β}
/--
 γ -f→ α
g↓     ↓e
 δ -h→ β
-/
lemma tendsto_comap_nhds_nhds  {d : δ} {a : α} (di : dense_inducing i) (H : tendsto h (nhds d) (nhds (i a)))
  (comm : h ∘ g = i ∘ f) : tendsto f (comap g (nhds d)) (nhds a) :=
begin
  have lim1 : map g (comap g (nhds d)) ≤ nhds d := map_comap_le,
  replace lim1 : map h (map g (comap g (nhds d))) ≤ map h (nhds d) := map_mono lim1,
  rw [filter.map_map, comm, ← filter.map_map, map_le_iff_le_comap] at lim1,
  have lim2 :  comap i (map h (nhds d)) ≤  comap i  (nhds (i a)) := comap_mono H,
  rw ← di.nhds_eq_comap at lim2,
  exact le_trans lim1 lim2,
end

protected lemma nhds_inf_neq_bot (di : dense_inducing i) {b : β} : nhds b ⊓ principal (range i) ≠ ⊥ :=
begin
  convert di.dense b,
  simp [closure_eq_nhds]
end

lemma comap_nhds_neq_bot (di : dense_inducing i) {b : β} : comap i (nhds b) ≠ ⊥ :=
forall_sets_neq_empty_iff_neq_bot.mp $
assume s ⟨t, ht, (hs : i ⁻¹' t ⊆ s)⟩,
have t ∩ range i ∈ nhds b ⊓ principal (range i),
  from inter_mem_inf_sets ht (subset.refl _),
let ⟨_, ⟨hx₁, y, rfl⟩⟩ := inhabited_of_mem_sets di.nhds_inf_neq_bot this in
subset_ne_empty hs $ ne_empty_of_mem hx₁

variables [topological_space γ]

/-- If `i : α → β` is a dense inducing, then any function `f : α → γ` "extends"
  to a function `g = extend di f : β → γ`. If `γ` is Hausdorff and `f` has a
  continuous extension, then `g` is the unique such extension. In general,
  `g` might not be continuous or even extend `f`. -/
def extend (di : dense_inducing i) (f : α → γ) (b : β) : γ :=
@lim _ _ ⟨f (dense_range.inhabited di.dense b).default⟩ (map f (comap i (nhds b)))

lemma extend_eq [t2_space γ] {b : β} {c : γ} {f : α → γ} (hf : map f (comap i (nhds b)) ≤ nhds c) :
  di.extend f b = c :=
@lim_eq _ _ (id _) _ _ _ (by simp; exact comap_nhds_neq_bot di) hf

lemma extend_e_eq [t2_space γ] {f : α → γ} (a : α) (hf : continuous_at f a) :
  di.extend f (i a) = f a :=
extend_eq _ $ di.nhds_eq_comap a ▸ hf

lemma extend_eq_of_cont [t2_space γ] {f : α → γ} (hf : continuous f) (a : α) :
  di.extend f (i a) = f a :=
di.extend_e_eq a (continuous_iff_continuous_at.1 hf a)

lemma tendsto_extend [regular_space γ] {b : β} {f : α → γ} (di : dense_inducing i)
  (hf : {b | ∃c, tendsto f (comap i $ nhds b) (nhds c)} ∈ nhds b) :
  tendsto (di.extend f) (nhds b) (nhds (di.extend f b)) :=
let φ := {b | tendsto f (comap i $ nhds b) (nhds $ di.extend f b)} in
have hφ : φ ∈ nhds b,
  from (nhds b).sets_of_superset hf $ assume b ⟨c, hc⟩,
    show tendsto f (comap i (nhds b)) (nhds (di.extend f b)), from (di.extend_eq hc).symm ▸ hc,
assume s hs,
let ⟨s'', hs''₁, hs''₂, hs''₃⟩ := nhds_is_closed hs in
let ⟨s', hs'₁, (hs'₂ : i ⁻¹' s' ⊆ f ⁻¹' s'')⟩ := mem_of_nhds hφ hs''₁ in
let ⟨t, (ht₁ : t ⊆ φ ∩ s'), ht₂, ht₃⟩ := mem_nhds_sets_iff.mp $ inter_mem_sets hφ hs'₁ in
have h₁ : closure (f '' (i ⁻¹' s')) ⊆ s'',
  by rw [closure_subset_iff_subset_of_is_closed hs''₃, image_subset_iff]; exact hs'₂,
have h₂ : t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)), from
  assume b' hb',
  have nhds b' ≤ principal t, by simp; exact mem_nhds_sets ht₂ hb',
  have map f (comap i (nhds b')) ≤ nhds (di.extend f b') ⊓ principal (f '' (i ⁻¹' t)),
    from calc _ ≤ map f (comap i (nhds b' ⊓ principal t)) : map_mono $ comap_mono $ le_inf (le_refl _) this
      ... ≤ map f (comap i (nhds b')) ⊓ map f (comap i (principal t)) :
        le_inf (map_mono $ comap_mono $ inf_le_left) (map_mono $ comap_mono $ inf_le_right)
      ... ≤ map f (comap i (nhds b')) ⊓ principal (f '' (i ⁻¹' t)) : by simp [le_refl]
      ... ≤ _ : inf_le_inf ((ht₁ hb').left) (le_refl _),
  show di.extend f b' ∈ closure (f '' (i ⁻¹' t)),
  begin
    rw [closure_eq_nhds],
    apply neq_bot_of_le_neq_bot _ this,
    simp,
    exact di.comap_nhds_neq_bot
  end,
(nhds b).sets_of_superset
  (show t ∈ nhds b, from mem_nhds_sets ht₂ ht₃)
  (calc t ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' t)) : h₂
    ... ⊆ di.extend f ⁻¹' closure (f '' (i ⁻¹' s')) :
      preimage_mono $ closure_mono $ image_subset f $ preimage_mono $ subset.trans ht₁ $ inter_subset_right _ _
    ... ⊆ di.extend f ⁻¹' s'' : preimage_mono h₁
    ... ⊆ di.extend f ⁻¹' s : preimage_mono hs''₂)

lemma continuous_extend [regular_space γ] {f : α → γ} (di : dense_inducing i)
  (hf : ∀b, ∃c, tendsto f (comap i (nhds b)) (nhds c)) : continuous (di.extend f) :=
continuous_iff_continuous_at.mpr $ assume b, di.tendsto_extend $ univ_mem_sets' hf

lemma mk'
  (i : α → β)
  (c     : continuous i)
  (dense : ∀x, x ∈ closure (range i))
  (H     : ∀ (a:α) s ∈ nhds a,
    ∃t ∈ nhds (i a), ∀ b, i b ∈ t → b ∈ s) :
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
  (H     : ∀ (a:α) s ∈ nhds a,
    ∃t ∈ nhds (e a), ∀ b, e b ∈ t → b ∈ s) :
  dense_embedding e :=
{ inj := inj,
  ..dense_inducing.mk' e c dense H}

namespace dense_embedding
variables [topological_space α] [topological_space β]
variables {e : α → β} (de : dense_embedding e)

lemma inj_iff {x y} : e x = e y ↔ x = y := de.inj.eq_iff

lemma to_embedding : embedding e :=
{ induced := de.induced,
  inj := de.inj }
end dense_embedding

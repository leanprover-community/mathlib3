/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import topology.uniform_space.basic

/-!
# Uniform convergence

A sequence of functions `Fₙ` (with values in a metric space) converges uniformly on a set `s` to a
function `f` if, for all `ε > 0`, for all large enough `n`, one has for all `y ∈ s` the inequality
`dist (f y, Fₙ y) < ε`. Under uniform convergence, many properties of the `Fₙ` pass to the limit,
most notably continuity. We prove this in the file, defining the notion of uniform convergence
in the more general setting of uniform spaces, and with respect to an arbitrary indexing set
endowed with a filter (instead of just `ℕ` with `at_top`).

## Main results

Let `α` be a topological space, `β` a uniform space, `Fₙ` and `f` be functions from `α`to `β`
(where the index `n` belongs to an indexing type `ι` endowed with a filter `p`).

* `tendsto_uniformly_on F f p s`: the fact that `Fₙ` converges uniformly to `f` on `s`. This means
  that, for any entourage `u` of the diagonal, for large enough `n` (with respect to `p`), one has
  `(f y, Fₙ y) ∈ u` for all `y ∈ s`.
* `tendsto_uniformly F f p`: same notion with `s = univ`.
* `tendsto_uniformly_on.continuous_on`: a uniform limit on a set of functions which are continuous
  on this set is itself continuous on this set.
* `tendsto_uniformly.continuous`: a uniform limit of continuous functions is continuous.
* `tendsto_uniformly_on.tendsto_comp`: If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends
  to `x` within `s`, then `Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s`.
* `tendsto_uniformly.tendsto_comp`: If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then
  `Fₙ gₙ` tends to `f x`.

We also define notions where the convergence is locally uniform, called
`tendsto_locally_uniformly_on F f p s` and `tendsto_locally_uniformly F f p`. The previous theorems
all have corresponding versions under locally uniform convergence.

Finally, we introduce the notion of a uniform Cauchy sequence, which is to uniform
convergence what a Cauchy sequence is to the usual notion of convergence.

## Implementation notes

We derive most of our initial results from an auxiliary definition `tendsto_uniformly_on_filter`.
This definition in and of itself can sometimes be useful, e.g., when studying the local behavior
of the `Fₙ` near a point, which would typically look like `tendsto_uniformly_on_filter F f p (𝓝 x)`.
Still, while this may be the "correct" definition (see
`tendsto_uniformly_on_iff_tendtso_uniformly_on_filter`), it is somewhat unwieldy to work with in
practice. Thus, we provide the more traditional definition in `tendsto_uniformly_on`.

Most results hold under weaker assumptions of locally uniform approximation. In a first section,
we prove the results under these weaker assumptions. Then, we derive the results on uniform
convergence from them.

## Tags

Uniform limit, uniform convergence, tends uniformly to
 -/

noncomputable theory
open_locale topological_space classical uniformity filter

open set filter

section generic

variables {α β γ ι : Type*} {p : filter ι} {p' : filter α}

lemma filter.eventually_swap_iff {f : (ι × α) → Prop} : (∀ᶠ (x : ι × α) in (p.prod p'), f x) ↔
  ∀ᶠ (y : α × ι) in (p'.prod p), f y.swap :=
begin
  rw [eventually_prod_iff, eventually_prod_iff],
  split,
  { intros h,
    obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := h,
    exact ⟨pb, hpb, pa, hpa, λ x hx y hy, hpapb hy hx⟩, },
  { intros h,
    obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := h,
    exact ⟨pb, hpb, pa, hpa, λ x hx y hy, hpapb hy hx⟩, },
end

lemma eventually_prod_principal_iff {f : ι × α → Prop} {s : set α} :
  (∀ᶠ (x : ι × α) in (p.prod (𝓟 s)), f x) ↔ ∀ᶠ (n : ι) in p, ∀ (y : α), y ∈ s → f (n, y) :=
begin
  rw [eventually_prod_iff, eventually_iff_exists_mem],
  split,
  { rintros ⟨pa, hpa, pb, hpb, hpapb⟩,
    exact ⟨_, hpa, (λ n hn y hy, hpapb hn ((eventually_principal.mp hpb) y hy))⟩, },
  { rintros ⟨t, ht, htmem⟩,
    exact ⟨_, ht, _, by simp, htmem⟩, },
end

lemma filter.prod_le_of_le_of_le {p₁ p₂ : filter ι} {q₁ q₂ : filter α} (hp : p₁ ≤ p₂)
  (hq : q₁ ≤ q₂) :  p₁ ×ᶠ q₁ ≤ p₂ ×ᶠ q₂ :=
begin
  intros s hs,
  rw mem_prod_iff at hs ⊢,
  obtain ⟨t₁, ht₁, t₂, ht₂, ht⟩ := hs,
  exact ⟨t₁, hp ht₁, t₂, hq ht₂, ht⟩,
end

lemma filter.prod_le_of_left_le (p' : filter α) {p'' : filter ι} (hp : p ≤ p'') :
  p ×ᶠ p' ≤ p'' ×ᶠ p' :=
filter.prod_le_of_le_of_le hp rfl.le

lemma filter.prod_le_of_right_le (p : filter ι) {p'' : filter α} (hp : p' ≤ p'') :
  p ×ᶠ p' ≤ p ×ᶠ p'' :=
filter.prod_le_of_le_of_le rfl.le hp

lemma filter.eventually.diag_of_prod_left {f : filter α} {g : filter γ}
  {p : (α × α) × γ → Prop} :
  (∀ᶠ x in (f ×ᶠ f ×ᶠ g), p x) →
  (∀ᶠ (x : α × γ) in (f ×ᶠ g), p ((x.1, x.1), x.2)) :=
begin
  intros h,
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h,
  refine (ht.diag_of_prod.prod_mk hs).mono (λ x hx, by simp only [hst hx.1 hx.2, prod.mk.eta]),
end

lemma filter.eventually.diag_of_prod_right {f : filter α} {g : filter γ}
  {p : α × γ × γ → Prop} :
  (∀ᶠ x in (f ×ᶠ (g ×ᶠ g)), p x) →
  (∀ᶠ (x : α × γ) in (f ×ᶠ g), p (x.1, x.2, x.2)) :=
begin
  intros h,
  obtain ⟨t, ht, s, hs, hst⟩ := eventually_prod_iff.1 h,
  refine (ht.prod_mk hs.diag_of_prod).mono (λ x hx, by simp only [hst hx.1 hx.2, prod.mk.eta]),
end

end generic

universes u v w
variables {α β γ ι : Type*} [uniform_space β]
variables {F : ι → α → β} {f : α → β} {s s' : set α} {x : α} {p : filter ι} {p' : filter α}
  {g : ι → α}

/-!
### Different notions of uniform convergence

We define uniform convergence and locally uniform convergence, on a set or in the whole space.
-/

/-- A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f`
with respect to the filter `p` if, for any entourage of the diagonal `u`, one has
`p ×ᶠ p'`-eventually `(f x, Fₙ x) ∈ u`. -/
def tendsto_uniformly_on_filter (F : ι → α → β) (f : α → β) (p : filter ι) (p' : filter α) :=
∀ u ∈ 𝓤 β, ∀ᶠ (n : ι × α) in (p ×ᶠ p'), (f n.snd, F n.fst n.snd) ∈ u

/--
A sequence of functions `Fₙ` converges uniformly on a filter `p'` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ p'` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `p'`.
-/
lemma tendsto_uniformly_on_filter_iff_tendsto :
  tendsto_uniformly_on_filter F f p p' ↔
  tendsto (λ q : ι × α, (f q.2, F q.1 q.2)) (p ×ᶠ p') (𝓤 β) :=
forall₂_congr $ λ u u_in, by simp [mem_map, filter.eventually, mem_prod_iff, preimage]

/-- A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` with
respect to the filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x ∈ s`. -/
def tendsto_uniformly_on (F : ι → α → β) (f : α → β) (p : filter ι) (s : set α) :=
∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ (x : α), x ∈ s → (f x, F n x) ∈ u

lemma tendsto_uniformly_on_iff_tendsto_uniformly_on_filter :
  tendsto_uniformly_on F f p s ↔ tendsto_uniformly_on_filter F f p (𝓟 s) :=
begin
  simp only [tendsto_uniformly_on, tendsto_uniformly_on_filter],
  apply forall₂_congr,
  simp_rw [eventually_prod_principal_iff],
  simp,
end

lemma tendsto_uniformly_on.tendsto_uniformly_on_filter
  (h : tendsto_uniformly_on F f p s) : tendsto_uniformly_on_filter F f p (𝓟 s) :=
by rwa ← tendsto_uniformly_on_iff_tendsto_uniformly_on_filter

/--
A sequence of functions `Fₙ` converges uniformly on a set `s` to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ 𝓟 s` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit besides it being in `s`.
-/
lemma tendsto_uniformly_on_iff_tendsto {F : ι → α → β} {f : α → β} {p : filter ι} {s : set α} :
  tendsto_uniformly_on F f p s ↔ tendsto (λ q : ι × α, (f q.2, F q.1 q.2)) (p ×ᶠ 𝓟 s) (𝓤 β) :=
by simp [tendsto_uniformly_on_iff_tendsto_uniformly_on_filter,
  tendsto_uniformly_on_filter_iff_tendsto]

/-- A sequence of functions `Fₙ` converges uniformly to a limiting function `f` with respect to a
filter `p` if, for any entourage of the diagonal `u`, one has `p`-eventually
`(f x, Fₙ x) ∈ u` for all `x`. -/
def tendsto_uniformly (F : ι → α → β) (f : α → β) (p : filter ι) :=
∀ u ∈ 𝓤 β, ∀ᶠ n in p, ∀ (x : α), (f x, F n x) ∈ u

lemma tendsto_uniformly_iff_tendsto_uniformly_on_filter :
  tendsto_uniformly F f p ↔ tendsto_uniformly_on_filter F f p ⊤ :=
begin
  simp only [tendsto_uniformly, tendsto_uniformly_on_filter],
  apply forall₂_congr,
  simp_rw [← principal_univ, eventually_prod_principal_iff],
  simp,
end

lemma tendsto_uniformly.tendsto_uniformly_on_filter
  (h : tendsto_uniformly F f p) : tendsto_uniformly_on_filter F f p ⊤ :=
by rwa ← tendsto_uniformly_iff_tendsto_uniformly_on_filter

lemma tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe :
  tendsto_uniformly_on F f p s ↔ tendsto_uniformly (λ i (x : s), F i x) (f ∘ coe) p :=
begin
  apply forall₂_congr,
  intros u hu,
  simp,
end

/--
A sequence of functions `Fₙ` converges uniformly to a limiting function `f` w.r.t.
filter `p` iff the function `(n, x) ↦ (f x, Fₙ x)` converges along `p ×ᶠ ⊤` to the uniformity.
In other words: one knows nothing about the behavior of `x` in this limit.
-/
lemma tendsto_uniformly_iff_tendsto {F : ι → α → β} {f : α → β} {p : filter ι} :
  tendsto_uniformly F f p ↔ tendsto (λ q : ι × α, (f q.2, F q.1 q.2)) (p ×ᶠ ⊤) (𝓤 β) :=
by simp [tendsto_uniformly_iff_tendsto_uniformly_on_filter, tendsto_uniformly_on_filter_iff_tendsto]

/-- Uniform converence implies pointwise convergence. -/
lemma tendsto_uniformly_on_filter.tendsto_at (h : tendsto_uniformly_on_filter F f p p')
  (hx : 𝓟 {x} ≤ p') : tendsto (λ n, F n x) p $ 𝓝 (f x) :=
begin
  refine uniform.tendsto_nhds_right.mpr (λ u hu, mem_map.mpr _),
  filter_upwards [(h u hu).curry],
  intros i h,
  simpa using (h.filter_mono hx),
end

/-- Uniform converence implies pointwise convergence. -/
lemma tendsto_uniformly_on.tendsto_at (h : tendsto_uniformly_on F f p s) {x : α} (hx : x ∈ s) :
  tendsto (λ n, F n x) p $ 𝓝 (f x) :=
h.tendsto_uniformly_on_filter.tendsto_at
  (le_principal_iff.mpr $ mem_principal.mpr $ singleton_subset_iff.mpr $ hx)

/-- Uniform converence implies pointwise convergence. -/
lemma tendsto_uniformly.tendsto_at (h : tendsto_uniformly F f p) (x : α) :
  tendsto (λ n, F n x) p $ 𝓝 (f x) :=
h.tendsto_uniformly_on_filter.tendsto_at le_top

lemma tendsto_uniformly_on_univ :
  tendsto_uniformly_on F f p univ ↔ tendsto_uniformly F f p :=
by simp [tendsto_uniformly_on, tendsto_uniformly]

lemma tendsto_uniformly_on_filter.mono_left {p'' : filter ι}
  (h : tendsto_uniformly_on_filter F f p p') (hp : p'' ≤ p) :
  tendsto_uniformly_on_filter F f p'' p' :=
λ u hu, (h u hu).filter_mono (p'.prod_le_of_left_le hp)

lemma tendsto_uniformly_on_filter.mono_right {p'' : filter α}
  (h : tendsto_uniformly_on_filter F f p p') (hp : p'' ≤ p') :
  tendsto_uniformly_on_filter F f p p'' :=
λ u hu, (h u hu).filter_mono (p.prod_le_of_right_le hp)

lemma tendsto_uniformly_on.mono {s' : set α}
  (h : tendsto_uniformly_on F f p s) (h' : s' ⊆ s) : tendsto_uniformly_on F f p s' :=
tendsto_uniformly_on_iff_tendsto_uniformly_on_filter.mpr
  (h.tendsto_uniformly_on_filter.mono_right (le_principal_iff.mpr $ mem_principal.mpr h'))

lemma tendsto_uniformly_on_filter.congr {F' : ι → α → β}
  (hf : tendsto_uniformly_on_filter F f p p')
  (hff' : ∀ᶠ (n : ι × α) in (p ×ᶠ p'), F n.fst n.snd = F' n.fst n.snd) :
  tendsto_uniformly_on_filter F' f p p' :=
begin
  refine (λ u hu, ((hf u hu).and hff').mono (λ n h, _)),
  rw ← h.right,
  exact h.left,
end

lemma tendsto_uniformly_on.congr {F' : ι → α → β}
  (hf : tendsto_uniformly_on F f p s) (hff' : ∀ᶠ n in p, set.eq_on (F n) (F' n) s) :
  tendsto_uniformly_on F' f p s :=
begin
  rw tendsto_uniformly_on_iff_tendsto_uniformly_on_filter at hf ⊢,
  refine hf.congr _,
  rw eventually_iff at hff' ⊢,
  simp only [set.eq_on] at hff',
  simp only [mem_prod_principal, hff', mem_set_of_eq],
end

protected lemma tendsto_uniformly.tendsto_uniformly_on
  (h : tendsto_uniformly F f p) : tendsto_uniformly_on F f p s :=
(tendsto_uniformly_on_univ.2 h).mono (subset_univ s)

/-- Composing on the right by a function preserves uniform convergence on a filter -/
lemma tendsto_uniformly_on_filter.comp (h : tendsto_uniformly_on_filter F f p p') (g : γ → α) :
  tendsto_uniformly_on_filter (λ n, F n ∘ g) (f ∘ g) p (p'.comap g) :=
begin
  intros u hu,
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (h u hu),
  rw eventually_prod_iff,
  simp_rw eventually_comap,
  exact ⟨pa, hpa, pb ∘ g, ⟨hpb.mono (λ x hx y hy, by simp only [hx, hy, function.comp_app]),
    λ x hx y hy, hpapb hx hy⟩⟩,
end

/-- Composing on the right by a function preserves uniform convergence on a set -/
lemma tendsto_uniformly_on.comp (h : tendsto_uniformly_on F f p s) (g : γ → α) :
  tendsto_uniformly_on (λ n, F n ∘ g) (f ∘ g) p (g ⁻¹' s) :=
begin
  rw tendsto_uniformly_on_iff_tendsto_uniformly_on_filter at h ⊢,
  simpa [tendsto_uniformly_on, comap_principal] using (tendsto_uniformly_on_filter.comp h g),
end

/-- Composing on the right by a function preserves uniform convergence -/
lemma tendsto_uniformly.comp (h : tendsto_uniformly F f p) (g : γ → α) :
  tendsto_uniformly (λ n, F n ∘ g) (f ∘ g) p :=
begin
  rw tendsto_uniformly_iff_tendsto_uniformly_on_filter at h ⊢,
  simpa [principal_univ, comap_principal] using (h.comp g),
end

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a filter -/
lemma uniform_continuous.comp_tendsto_uniformly_on_filter [uniform_space γ] {g : β → γ}
  (hg : uniform_continuous g) (h : tendsto_uniformly_on_filter F f p p') :
  tendsto_uniformly_on_filter (λ i, g ∘ (F i)) (g ∘ f) p p' :=
λ u hu, h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves
  uniform convergence on a set -/
lemma uniform_continuous.comp_tendsto_uniformly_on [uniform_space γ] {g : β → γ}
  (hg : uniform_continuous g) (h : tendsto_uniformly_on F f p s) :
  tendsto_uniformly_on (λ i, g ∘ (F i)) (g ∘ f) p s :=
λ u hu, h _ (hg hu)

/-- Composing on the left by a uniformly continuous function preserves uniform convergence -/
lemma uniform_continuous.comp_tendsto_uniformly [uniform_space γ] {g : β → γ}
  (hg : uniform_continuous g) (h : tendsto_uniformly F f p) :
  tendsto_uniformly (λ i, g ∘ (F i)) (g ∘ f) p :=
λ u hu, h _ (hg hu)

lemma tendsto_uniformly_on_filter.prod_map {ι' α' β' : Type*} [uniform_space β']
  {F' : ι' → α' → β'} {f' : α' → β'} {q : filter ι'} {q' : filter α'}
  (h : tendsto_uniformly_on_filter F f p p') (h' : tendsto_uniformly_on_filter F' f' q q') :
  tendsto_uniformly_on_filter (λ (i : ι × ι'), prod.map (F i.1) (F' i.2))
    (prod.map f f') (p.prod q) (p'.prod q') :=
begin
  intros u hu,
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu,
  obtain ⟨v, hv, w, hw, hvw⟩ := hu,
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono,
  simp only [prod_map, and_imp, prod.forall],
  intros n n' x hxv hxw,
  have hout : ((f x.fst, F n x.fst), (f' x.snd, F' n' x.snd)) ∈
    {x : (β × β) × β' × β' | ((x.fst.fst, x.snd.fst), x.fst.snd, x.snd.snd) ∈ u},
  { exact mem_of_mem_of_subset (set.mem_prod.mpr ⟨hxv, hxw⟩) hvw, },
  exact hout,
end

lemma tendsto_uniformly_on.prod_map {ι' α' β' : Type*} [uniform_space β']
  {F' : ι' → α' → β'} {f' : α' → β'} {p' : filter ι'} {s' : set α'}
  (h : tendsto_uniformly_on F f p s) (h' : tendsto_uniformly_on F' f' p' s') :
  tendsto_uniformly_on (λ (i : ι × ι'), prod.map (F i.1) (F' i.2))
    (prod.map f f') (p.prod p') (s ×ˢ s') :=
begin
  rw tendsto_uniformly_on_iff_tendsto_uniformly_on_filter at h h' ⊢,
  simpa only [prod_principal_principal] using (h.prod_map h'),
end

lemma tendsto_uniformly.prod_map {ι' α' β' : Type*} [uniform_space β'] {F' : ι' → α' → β'}
  {f' : α' → β'} {p' : filter ι'} (h : tendsto_uniformly F f p) (h' : tendsto_uniformly F' f' p') :
  tendsto_uniformly (λ (i : ι × ι'), prod.map (F i.1) (F' i.2)) (prod.map f f') (p.prod p') :=
begin
  rw [←tendsto_uniformly_on_univ, ←univ_prod_univ] at *,
  exact h.prod_map h',
end

lemma tendsto_uniformly_on_filter.prod {ι' β' : Type*} [uniform_space β']
  {F' : ι' → α → β'} {f' : α → β'} {q : filter ι'}
  (h : tendsto_uniformly_on_filter F f p p') (h' : tendsto_uniformly_on_filter F' f' q p') :
  tendsto_uniformly_on_filter (λ (i : ι × ι') a, (F i.1 a, F' i.2 a)) (λ a, (f a, f' a)) (p.prod q) p' :=
λ u hu, ((h.prod_map h') u hu).diag_of_prod_right

lemma tendsto_uniformly_on.prod {ι' β' : Type*} [uniform_space β'] {F' : ι' → α → β'} {f' : α → β'}
  {p' : filter ι'} (h : tendsto_uniformly_on F f p s) (h' : tendsto_uniformly_on F' f' p' s) :
  tendsto_uniformly_on (λ (i : ι × ι') a, (F i.1 a, F' i.2 a)) (λ a, (f a, f' a)) (p.prod p') s :=
(congr_arg _ s.inter_self).mp ((h.prod_map h').comp (λ a, (a, a)))

lemma tendsto_uniformly.prod {ι' β' : Type*} [uniform_space β'] {F' : ι' → α → β'} {f' : α → β'}
  {p' : filter ι'} (h : tendsto_uniformly F f p) (h' : tendsto_uniformly F' f' p') :
  tendsto_uniformly (λ (i : ι × ι') a, (F i.1 a, F' i.2 a)) (λ a, (f a, f' a)) (p.prod p') :=
(h.prod_map h').comp (λ a, (a, a))

/-- Uniform convergence on a filter `p'` to a constant function is equivalent to convergence in
`p ×ᶠ p'`. -/
lemma tendsto_prod_filter_iff {c : β} :
  tendsto ↿F (p ×ᶠ p') (𝓝 c) ↔ tendsto_uniformly_on_filter F (λ _, c) p p' :=
begin
  simp_rw [tendsto, nhds_eq_comap_uniformity, map_le_iff_le_comap.symm, map_map, le_def, mem_map],
  exact forall₂_congr (λ u hu, by simpa [eventually_iff]),
end

/-- Uniform convergence on a set `s` to a constant function is equivalent to convergence in
`p ×ᶠ 𝓟 s`. -/
lemma tendsto_prod_principal_iff {c : β} :
  tendsto ↿F (p ×ᶠ 𝓟 s) (𝓝 c) ↔ tendsto_uniformly_on F (λ _, c) p s :=
begin
  rw tendsto_uniformly_on_iff_tendsto_uniformly_on_filter,
  exact tendsto_prod_filter_iff,
end

/-- Uniform convergence to a constant function is equivalent to convergence in `p ×ᶠ ⊤`. -/
lemma tendsto_prod_top_iff {c : β} : tendsto ↿F (p ×ᶠ ⊤) (𝓝 c) ↔ tendsto_uniformly F (λ _, c) p :=
begin
  rw tendsto_uniformly_iff_tendsto_uniformly_on_filter,
  exact tendsto_prod_filter_iff,
end

/-- Uniform convergence on the empty set is vacuously true -/
lemma tendsto_uniformly_on_empty :
  tendsto_uniformly_on F f p ∅ :=
λ u hu, by simp

/-- Uniform convergence on a singleton is equivalent to regular convergence -/
lemma tendsto_uniformly_on_singleton_iff_tendsto :
  tendsto_uniformly_on F f p {x} ↔ tendsto (λ n : ι, F n x) p (𝓝 (f x)) :=
begin
  simp_rw [tendsto_uniformly_on_iff_tendsto, uniform.tendsto_nhds_right, tendsto_def],
  exact forall₂_congr (λ u hu, by simp [mem_prod_principal, preimage]),
end

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`λ n, λ a, g n` converges to the constant function `λ a, b` on any set `s` -/
lemma filter.tendsto.tendsto_uniformly_on_filter_const
  {g : ι → β} {b : β} (hg : tendsto g p (𝓝 b)) (p' : filter α) :
  tendsto_uniformly_on_filter (λ n : ι, λ a : α, g n) (λ a : α, b) p p' :=
begin
  rw tendsto_uniformly_on_filter_iff_tendsto,
  rw uniform.tendsto_nhds_right at hg,
  exact (hg.comp (tendsto_fst.comp ((@tendsto_id ι p).prod_map (@tendsto_id α p')))).congr
    (λ x, by simp),
end

/-- If a sequence `g` converges to some `b`, then the sequence of constant functions
`λ n, λ a, g n` converges to the constant function `λ a, b` on any set `s` -/
lemma filter.tendsto.tendsto_uniformly_on_const
  {g : ι → β} {b : β} (hg : tendsto g p (𝓝 b)) (s : set α) :
  tendsto_uniformly_on (λ n : ι, λ a : α, g n) (λ a : α, b) p s :=
tendsto_uniformly_on_iff_tendsto_uniformly_on_filter.mpr
  (hg.tendsto_uniformly_on_filter_const (𝓟 s))

lemma uniform_continuous_on.tendsto_uniformly [uniform_space α] [uniform_space γ]
  {x : α} {U : set α} (hU : U ∈ 𝓝 x)
  {F : α → β → γ} (hF : uniform_continuous_on ↿F (U ×ˢ (univ : set β))) :
  tendsto_uniformly F (F x) (𝓝 x) :=
begin
  let φ := (λ q : α × β, ((x, q.2), q)),
  rw [tendsto_uniformly_iff_tendsto,
      show (λ q : α × β, (F x q.2, F q.1 q.2)) = prod.map ↿F ↿F ∘ φ, by { ext ; simpa }],
  apply hF.comp (tendsto_inf.mpr ⟨_, _⟩),
  { rw [uniformity_prod, tendsto_inf, tendsto_comap_iff, tendsto_comap_iff,
      show (λp : (α × β) × α × β, (p.1.1, p.2.1)) ∘ φ = (λa, (x, a)) ∘ prod.fst, by { ext, simp },
      show (λp : (α × β) × α × β, (p.1.2, p.2.2)) ∘ φ = (λb, (b, b)) ∘ prod.snd, by { ext, simp }],
    exact ⟨tendsto_left_nhds_uniformity.comp tendsto_fst,
           (tendsto_diag_uniformity id ⊤).comp tendsto_top⟩ },
  { rw tendsto_principal,
    apply mem_of_superset (prod_mem_prod hU (mem_top.mpr rfl)) (λ q h, _),
    simp [h.1, mem_of_mem_nhds hU] }
end

lemma uniform_continuous₂.tendsto_uniformly [uniform_space α] [uniform_space γ]
  {f : α → β → γ} (h : uniform_continuous₂ f) {x : α} : tendsto_uniformly f (f x) (𝓝 x) :=
uniform_continuous_on.tendsto_uniformly univ_mem $
  by rwa [univ_prod_univ, uniform_continuous_on_univ]

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
def uniform_cauchy_seq_on_filter
  (F : ι → α → β) (p : filter ι) (p' : filter α) : Prop :=
  ∀ u : set (β × β), u ∈ 𝓤 β → ∀ᶠ (m : (ι × ι) × α) in ((p ×ᶠ p) ×ᶠ p'),
    (F m.fst.fst m.snd, F m.fst.snd m.snd) ∈ u

/-- A sequence is uniformly Cauchy if eventually all of its pairwise differences are
uniformly bounded -/
def uniform_cauchy_seq_on
  (F : ι → α → β) (p : filter ι) (s : set α) : Prop :=
  ∀ u : set (β × β), u ∈ 𝓤 β → ∀ᶠ (m : ι × ι) in (p ×ᶠ p), ∀ (x : α), x ∈ s →
    (F m.fst x, F m.snd x) ∈ u

lemma uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter :
  uniform_cauchy_seq_on F p s ↔ uniform_cauchy_seq_on_filter F p (𝓟 s) :=
begin
  simp only [uniform_cauchy_seq_on, uniform_cauchy_seq_on_filter],
  refine forall₂_congr (λ u hu, _),
  rw eventually_prod_principal_iff,
end

lemma uniform_cauchy_seq_on.uniform_cauchy_seq_on_filter (hF : uniform_cauchy_seq_on F p s) :
  uniform_cauchy_seq_on_filter F p (𝓟 s) :=
by rwa ←uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter

/-- A sequence that converges uniformly is also uniformly Cauchy -/
lemma tendsto_uniformly_on_filter.uniform_cauchy_seq_on_filter
  (hF : tendsto_uniformly_on_filter F f p p') :
  uniform_cauchy_seq_on_filter F p p' :=
begin
  intros u hu,
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩,
  have := tendsto_swap4_prod.eventually ((hF t ht).prod_mk (hF t ht)),
  apply this.diag_of_prod_right.mono,
  simp only [and_imp, prod.forall],
  intros n1 n2 x hl hr,
  exact set.mem_of_mem_of_subset (prod_mk_mem_comp_rel (htsymm hl) hr) htmem,
end

/-- A sequence that converges uniformly is also uniformly Cauchy -/
lemma tendsto_uniformly_on.uniform_cauchy_seq_on (hF : tendsto_uniformly_on F f p s) :
  uniform_cauchy_seq_on F p s :=
uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter.mpr
  hF.tendsto_uniformly_on_filter.uniform_cauchy_seq_on_filter

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
lemma uniform_cauchy_seq_on_filter.tendsto_uniformly_on_filter_of_tendsto [ne_bot p]
  (hF : uniform_cauchy_seq_on_filter F p p')
  (hF' : ∀ᶠ (x : α) in p', tendsto (λ n, F n x) p (𝓝 (f x))) :
  tendsto_uniformly_on_filter F f p p' :=
begin
  -- Proof idea: |f_n(x) - f(x)| ≤ |f_n(x) - f_m(x)| + |f_m(x) - f(x)|. We choose `n`
  -- so that |f_n(x) - f_m(x)| is uniformly small across `s` whenever `m ≥ n`. Then for
  -- a fixed `x`, we choose `m` sufficiently large such that |f_m(x) - f(x)| is small.
  intros u hu,
  rcases comp_symm_of_uniformity hu with ⟨t, ht, htsymm, htmem⟩,

  -- We will choose n, x, and m simultaneously. n and x come from hF. m comes from hF'
  -- But we need to promote hF' to the full product filter to use it
  have hmc : ∀ᶠ (x : (ι × ι) × α) in p ×ᶠ p ×ᶠ p', tendsto (λ (n : ι), F n x.snd) p (𝓝 (f x.snd)),
  { rw eventually_prod_iff,
    refine ⟨(λ x, true), by simp, _, hF', by simp⟩, },

  -- To apply filter operations we'll need to do some order manipulation
  rw filter.eventually_swap_iff,
  have := tendsto_prod_assoc.eventually (tendsto_prod_swap.eventually ((hF t ht).and hmc)),
  apply this.curry.mono,
  simp only [equiv.prod_assoc_apply, eventually_and, eventually_const, prod.snd_swap,
    prod.fst_swap, and_imp, prod.forall],

  -- Complete the proof
  intros x n hx hm',
  refine set.mem_of_mem_of_subset (mem_comp_rel.mpr _) htmem,
  rw uniform.tendsto_nhds_right at hm',
  have := hx.and (hm' ht),
  obtain ⟨m, hm⟩ := this.exists,
  exact ⟨F m x, ⟨hm.2, htsymm hm.1⟩⟩,
end

/-- A uniformly Cauchy sequence converges uniformly to its limit -/
lemma uniform_cauchy_seq_on.tendsto_uniformly_on_of_tendsto [ne_bot p]
  (hF : uniform_cauchy_seq_on F p s) (hF' : ∀ x : α, x ∈ s → tendsto (λ n, F n x) p (𝓝 (f x))) :
  tendsto_uniformly_on F f p s :=
tendsto_uniformly_on_iff_tendsto_uniformly_on_filter.mpr
  (hF.uniform_cauchy_seq_on_filter.tendsto_uniformly_on_filter_of_tendsto hF')

lemma uniform_cauchy_seq_on_filter.mono_left {p'' : filter ι}
  (hf : uniform_cauchy_seq_on_filter F p p') (hp : p'' ≤ p) :
  uniform_cauchy_seq_on_filter F p'' p' :=
begin
  intros u hu,
  have := (hf u hu).filter_mono (p'.prod_le_of_left_le (filter.prod_le_of_le_of_le hp hp)),
  exact this.mono (by simp),
end

lemma uniform_cauchy_seq_on_filter.mono_right {p'' : filter α}
  (hf : uniform_cauchy_seq_on_filter F p p') (hp : p'' ≤ p') :
  uniform_cauchy_seq_on_filter F p p'' :=
begin
  intros u hu,
  have := (hf u hu).filter_mono ((p ×ᶠ p).prod_le_of_right_le hp),
  exact this.mono (by simp),
end

lemma uniform_cauchy_seq_on.mono {s' : set α} (hf : uniform_cauchy_seq_on F p s) (hss' : s' ⊆ s) :
  uniform_cauchy_seq_on F p s' :=
begin
  rw uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter at hf ⊢,
  exact hf.mono_right (le_principal_iff.mpr $mem_principal.mpr hss'),
end

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
lemma uniform_cauchy_seq_on_filter.comp {γ : Type*} (hf : uniform_cauchy_seq_on_filter F p p')
  (g : γ → α) :
  uniform_cauchy_seq_on_filter (λ n, F n ∘ g) p (p'.comap g) :=
begin
  intros u hu,
  obtain ⟨pa, hpa, pb, hpb, hpapb⟩ := eventually_prod_iff.mp (hf u hu),
  rw eventually_prod_iff,
  refine ⟨pa, hpa, pb ∘ g, _, λ x hx y hy, hpapb hx hy⟩,
  exact eventually_comap.mpr (hpb.mono (λ x hx y hy, by simp only [hx, hy, function.comp_app])),
end

/-- Composing on the right by a function preserves uniform Cauchy sequences -/
lemma uniform_cauchy_seq_on.comp {γ : Type*} (hf : uniform_cauchy_seq_on F p s) (g : γ → α) :
  uniform_cauchy_seq_on (λ n, F n ∘ g) p (g ⁻¹' s) :=
begin
  rw uniform_cauchy_seq_on_iff_uniform_cauchy_seq_on_filter at hf ⊢,
  simpa only [uniform_cauchy_seq_on, comap_principal] using (hf.comp g),
end

/-- Composing on the left by a uniformly continuous function preserves
uniform Cauchy sequences -/
lemma uniform_continuous.comp_uniform_cauchy_seq_on [uniform_space γ] {g : β → γ}
  (hg : uniform_continuous g) (hf : uniform_cauchy_seq_on F p s) :
  uniform_cauchy_seq_on (λ n, g ∘ (F n)) p s :=
λ u hu, hf _ (hg hu)

lemma uniform_cauchy_seq_on.prod_map {ι' α' β' : Type*} [uniform_space β']
  {F' : ι' → α' → β'} {p' : filter ι'} {s' : set α'}
  (h : uniform_cauchy_seq_on F p s) (h' : uniform_cauchy_seq_on F' p' s') :
  uniform_cauchy_seq_on (λ (i : ι × ι'), prod.map (F i.1) (F' i.2))
    (p.prod p') (s ×ˢ s') :=
begin
  intros u hu,
  rw [uniformity_prod_eq_prod, mem_map, mem_prod_iff] at hu,
  obtain ⟨v, hv, w, hw, hvw⟩ := hu,
  simp_rw [mem_prod, prod_map, and_imp, prod.forall],
  rw [← set.image_subset_iff] at hvw,
  apply (tendsto_swap4_prod.eventually ((h v hv).prod_mk (h' w hw))).mono,
  intros x hx a b ha hb,
  refine hvw ⟨_, mk_mem_prod (hx.1 a ha) (hx.2 b hb), rfl⟩,
end

lemma uniform_cauchy_seq_on.prod {ι' β' : Type*} [uniform_space β'] {F' : ι' → α → β'}
  {p' : filter ι'}
  (h : uniform_cauchy_seq_on F p s) (h' : uniform_cauchy_seq_on F' p' s) :
  uniform_cauchy_seq_on (λ (i : ι × ι') a, (F i.fst a, F' i.snd a)) (p ×ᶠ p') s :=
(congr_arg _ s.inter_self).mp ((h.prod_map h').comp (λ a, (a, a)))

lemma uniform_cauchy_seq_on.prod' {β' : Type*} [uniform_space β'] {F' : ι → α → β'}
  (h : uniform_cauchy_seq_on F p s) (h' : uniform_cauchy_seq_on F' p s) :
  uniform_cauchy_seq_on (λ (i : ι) a, (F i a, F' i a)) p s :=
begin
  intros u hu,
  have hh : tendsto (λ x : ι, (x, x)) p (p ×ᶠ p), { exact tendsto_diag, },
  exact (hh.prod_map hh).eventually ((h.prod h') u hu),
end

section seq_tendsto

lemma tendsto_uniformly_on_of_seq_tendsto_uniformly_on {l : filter ι} [l.is_countably_generated]
  (h : ∀ u : ℕ → ι, tendsto u at_top l → tendsto_uniformly_on (λ n, F (u n)) f at_top s) :
  tendsto_uniformly_on F f l s :=
begin
  rw [tendsto_uniformly_on_iff_tendsto, tendsto_iff_seq_tendsto],
  intros u hu,
  rw tendsto_prod_iff' at hu,
  specialize h (λ n, (u n).fst) hu.1,
  rw tendsto_uniformly_on_iff_tendsto at h,
  have : ((λ (q : ι × α), (f q.snd, F q.fst q.snd)) ∘ u)
    = (λ (q : ℕ × α), (f q.snd, F ((λ (n : ℕ), (u n).fst) q.fst) q.snd)) ∘ (λ n, (n, (u n).snd)),
  { ext1 n, simp, },
  rw this,
  refine tendsto.comp h _,
  rw tendsto_prod_iff',
  exact ⟨tendsto_id, hu.2⟩,
end

lemma tendsto_uniformly_on.seq_tendsto_uniformly_on {l : filter ι}
  (h : tendsto_uniformly_on F f l s) (u : ℕ → ι) (hu : tendsto u at_top l) :
  tendsto_uniformly_on (λ n, F (u n)) f at_top s :=
begin
  rw tendsto_uniformly_on_iff_tendsto at h ⊢,
  have : (λ (q : ℕ × α), (f q.snd, F (u q.fst) q.snd))
    = (λ (q : ι × α), (f q.snd, F q.fst q.snd)) ∘ (λ p : ℕ × α, (u p.fst, p.snd)),
  { ext1 x, simp, },
  rw this,
  refine h.comp _,
  rw tendsto_prod_iff',
  exact ⟨hu.comp tendsto_fst, tendsto_snd⟩,
end

lemma tendsto_uniformly_on_iff_seq_tendsto_uniformly_on {l : filter ι} [l.is_countably_generated] :
  tendsto_uniformly_on F f l s
    ↔ ∀ u : ℕ → ι, tendsto u at_top l → tendsto_uniformly_on (λ n, F (u n)) f at_top s :=
⟨tendsto_uniformly_on.seq_tendsto_uniformly_on, tendsto_uniformly_on_of_seq_tendsto_uniformly_on⟩

lemma tendsto_uniformly_iff_seq_tendsto_uniformly {l : filter ι} [l.is_countably_generated] :
  tendsto_uniformly F f l
    ↔ ∀ u : ℕ → ι, tendsto u at_top l → tendsto_uniformly (λ n, F (u n)) f at_top :=
begin
  simp_rw ← tendsto_uniformly_on_univ,
  exact tendsto_uniformly_on_iff_seq_tendsto_uniformly_on,
end

end seq_tendsto

variable [topological_space α]

/-- A sequence of functions `Fₙ` converges locally uniformly on a set `s` to a limiting function
`f` with respect to a filter `p` if, for any entourage of the diagonal `u`, for any `x ∈ s`, one
has `p`-eventually `(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x` in `s`. -/
def tendsto_locally_uniformly_on (F : ι → α → β) (f : α → β) (p : filter ι) (s : set α) :=
  ∀ u ∈ 𝓤 β, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u

/-- A sequence of functions `Fₙ` converges locally uniformly to a limiting function `f` with respect
to a filter `p` if, for any entourage of the diagonal `u`, for any `x`, one has `p`-eventually
`(f y, Fₙ y) ∈ u` for all `y` in a neighborhood of `x`. -/
def tendsto_locally_uniformly (F : ι → α → β) (f : α → β) (p : filter ι) :=
  ∀ u ∈ 𝓤 β, ∀ (x : α), ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u

lemma tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe :
  tendsto_locally_uniformly_on F f p s ↔
  tendsto_locally_uniformly (λ i (x : s), F i x) (f ∘ coe) p :=
begin
  refine forall₂_congr (λ V hV, _),
  simp only [exists_prop, function.comp_app, set_coe.forall, subtype.coe_mk],
  refine forall₂_congr (λ x hx, ⟨_, _⟩),
  { rintro ⟨t, ht₁, ht₂⟩,
    obtain ⟨u, hu₁, hu₂⟩ := mem_nhds_within_iff_exists_mem_nhds_inter.mp ht₁,
    exact ⟨coe⁻¹' u,
           (mem_nhds_subtype _ _ _).mpr ⟨u, hu₁, rfl.subset⟩,
           ht₂.mono (λ i hi y hy₁ hy₂, hi y (hu₂ ⟨hy₂, hy₁⟩))⟩, },
  { rintro ⟨t, ht₁, ht₂⟩,
    obtain ⟨u, hu₁, hu₂⟩ := (mem_nhds_subtype _ _ _).mp ht₁,
    exact ⟨u ∩ s,
           mem_nhds_within_iff_exists_mem_nhds_inter.mpr ⟨u, hu₁, rfl.subset⟩,
           ht₂.mono (λ i hi y hy, hi y hy.2 (hu₂ (by simp [hy.1])))⟩, },
end

lemma tendsto_locally_uniformly_iff_forall_tendsto :
  tendsto_locally_uniformly F f p ↔
  ∀ x, tendsto (λ (y : ι × α), (f y.2, F y.1 y.2)) (p ×ᶠ (𝓝 x)) (𝓤 β) :=
begin
  simp only [tendsto_locally_uniformly, filter.forall_in_swap, tendsto_def, mem_prod_iff,
    set.prod_subset_iff],
  refine forall₃_congr (λ x u hu, ⟨_, _⟩),
  { rintros ⟨n, hn, hp⟩,
    exact ⟨_, hp, n, hn, λ i hi a ha, hi a ha⟩, },
  { rintros ⟨I, hI, n, hn, hu⟩,
    exact ⟨n, hn, by filter_upwards [hI] using hu⟩, },
end

protected lemma tendsto_uniformly_on.tendsto_locally_uniformly_on
  (h : tendsto_uniformly_on F f p s) : tendsto_locally_uniformly_on F f p s :=
λ u hu x hx,⟨s, self_mem_nhds_within, by simpa using (h u hu)⟩

protected lemma tendsto_uniformly.tendsto_locally_uniformly
  (h : tendsto_uniformly F f p) : tendsto_locally_uniformly F f p :=
λ u hu x, ⟨univ, univ_mem, by simpa using (h u hu)⟩

lemma tendsto_locally_uniformly_on.mono (h : tendsto_locally_uniformly_on F f p s) (h' : s' ⊆ s) :
  tendsto_locally_uniformly_on F f p s' :=
begin
  assume u hu x hx,
  rcases h u hu x (h' hx) with ⟨t, ht, H⟩,
  exact ⟨t, nhds_within_mono x h' ht, H.mono (λ n, id)⟩
end

lemma tendsto_locally_uniformly_on_univ :
  tendsto_locally_uniformly_on F f p univ ↔ tendsto_locally_uniformly F f p :=
by simp [tendsto_locally_uniformly_on, tendsto_locally_uniformly, nhds_within_univ]

protected lemma tendsto_locally_uniformly.tendsto_locally_uniformly_on
  (h : tendsto_locally_uniformly F f p) : tendsto_locally_uniformly_on F f p s :=
(tendsto_locally_uniformly_on_univ.mpr h).mono (subset_univ _)

/-- On a compact space, locally uniform convergence is just uniform convergence. -/
lemma tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space [compact_space α] :
  tendsto_locally_uniformly F f p ↔ tendsto_uniformly F f p :=
begin
  refine ⟨λ h V hV, _, tendsto_uniformly.tendsto_locally_uniformly⟩,
  choose U hU using h V hV,
  obtain ⟨t, ht⟩ := compact_univ.elim_nhds_subcover' (λ k hk, U k) (λ k hk, (hU k).1),
  replace hU := λ (x : t), (hU x).2,
  rw ← eventually_all at hU,
  -- rw [← principal_univ, eventually_prod_principal_iff],
  refine hU.mono (λ i hi x, _),
  specialize ht (mem_univ x),
  simp only [exists_prop, mem_Union, set_coe.exists, exists_and_distrib_right,subtype.coe_mk] at ht,
  obtain ⟨y, ⟨hy₁, hy₂⟩, hy₃⟩ := ht,
  exact hi ⟨⟨y, hy₁⟩, hy₂⟩ x hy₃,
end

/-- For a compact set `s`, locally uniform convergence on `s` is just uniform convergence on `s`. -/
lemma tendsto_locally_uniformly_on_iff_tendsto_uniformly_on_of_compact (hs : is_compact s) :
  tendsto_locally_uniformly_on F f p s ↔ tendsto_uniformly_on F f p s :=
begin
  haveI : compact_space s := is_compact_iff_compact_space.mp hs,
  refine ⟨λ h, _, tendsto_uniformly_on.tendsto_locally_uniformly_on⟩,
  rwa [tendsto_locally_uniformly_on_iff_tendsto_locally_uniformly_comp_coe,
    tendsto_locally_uniformly_iff_tendsto_uniformly_of_compact_space,
    ← tendsto_uniformly_on_iff_tendsto_uniformly_comp_coe] at h,
end

lemma tendsto_locally_uniformly_on.comp [topological_space γ] {t : set γ}
  (h : tendsto_locally_uniformly_on F f p s)
  (g : γ → α) (hg : maps_to g t s) (cg : continuous_on g t) :
  tendsto_locally_uniformly_on (λ n, (F n) ∘ g) (f ∘ g) p t :=
begin
  assume u hu x hx,
  rcases h u hu (g x) (hg hx) with ⟨a, ha, H⟩,
  have : g⁻¹' a ∈ 𝓝[t] x :=
    ((cg x hx).preimage_mem_nhds_within' (nhds_within_mono (g x) hg.image_subset ha)),
  exact ⟨g ⁻¹' a, this, H.mono (λ n hn y hy, hn _ hy)⟩
end

lemma tendsto_locally_uniformly.comp [topological_space γ]
  (h : tendsto_locally_uniformly F f p) (g : γ → α) (cg : continuous g) :
  tendsto_locally_uniformly (λ n, (F n) ∘ g) (f ∘ g) p :=
begin
  rw ← tendsto_locally_uniformly_on_univ at h ⊢,
  rw continuous_iff_continuous_on_univ at cg,
  exact h.comp _ (maps_to_univ _ _) cg
end

/-!
### Uniform approximation

In this section, we give lemmas ensuring that a function is continuous if it can be approximated
uniformly by continuous functions. We give various versions, within a set or the whole space, at
a single point or at all points, with locally uniform approximation or uniform approximation. All
the statements are derived from a statement about locally uniform approximation within a set at
a point, called `continuous_within_at_of_locally_uniform_approx_of_continuous_within_at`. -/

/-- A function which can be locally uniformly approximated by functions which are continuous
within a set at a point is continuous within this set at this point. -/
lemma continuous_within_at_of_locally_uniform_approx_of_continuous_within_at
  (hx : x ∈ s) (L : ∀ u ∈ 𝓤 β, ∃ (t ∈ 𝓝[s] x) (F : α → β), continuous_within_at F s x ∧
    ∀ y ∈ t, (f y, F y) ∈ u) : continuous_within_at f s x :=
begin
  apply uniform.continuous_within_at_iff'_left.2 (λ u₀ hu₀, _),
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β), comp_rel u u ⊆ u₀ :=
    comp_mem_uniformity_sets hu₀,
  obtain ⟨u₂, h₂, hsymm, u₂₁⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β),
    (∀{a b}, (a, b) ∈ u → (b, a) ∈ u) ∧ comp_rel u u ⊆ u₁ := comp_symm_of_uniformity h₁,
  rcases L u₂ h₂ with ⟨t, tx, F, hFc, hF⟩,
  have A : ∀ᶠ y in 𝓝[s] x, (f y, F y) ∈ u₂ := eventually.mono tx hF,
  have B : ∀ᶠ y in 𝓝[s] x, (F y, F x) ∈ u₂ :=
    uniform.continuous_within_at_iff'_left.1 hFc h₂,
  have C : ∀ᶠ y in 𝓝[s] x, (f y, F x) ∈ u₁ :=
    (A.and B).mono (λ y hy, u₂₁ (prod_mk_mem_comp_rel hy.1 hy.2)),
  have : (F x, f x) ∈ u₁ :=
    u₂₁ (prod_mk_mem_comp_rel (refl_mem_uniformity h₂) (hsymm (A.self_of_nhds_within hx))),
  exact C.mono (λ y hy, u₁₀ (prod_mk_mem_comp_rel hy this))
end

/-- A function which can be locally uniformly approximated by functions which are continuous at
a point is continuous at this point. -/
lemma continuous_at_of_locally_uniform_approx_of_continuous_at
  (L : ∀ u ∈ 𝓤 β, ∃ (t ∈ 𝓝 x) F, continuous_at F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
  continuous_at f x :=
begin
  rw ← continuous_within_at_univ,
  apply continuous_within_at_of_locally_uniform_approx_of_continuous_within_at (mem_univ _) _,
  simpa only [exists_prop, nhds_within_univ, continuous_within_at_univ] using L
end

/-- A function which can be locally uniformly approximated by functions which are continuous
on a set is continuous on this set. -/
lemma continuous_on_of_locally_uniform_approx_of_continuous_within_at
  (L : ∀ (x ∈ s) (u ∈ 𝓤 β), ∃ (t ∈ 𝓝[s] x) F,
    continuous_within_at F s x ∧ ∀ y ∈ t, (f y, F y) ∈ u) : continuous_on f s :=
λ x hx, continuous_within_at_of_locally_uniform_approx_of_continuous_within_at hx (L x hx)

/-- A function which can be uniformly approximated by functions which are continuous on a set
is continuous on this set. -/
lemma continuous_on_of_uniform_approx_of_continuous_on
  (L : ∀ u ∈ 𝓤 β, ∃ F, continuous_on F s ∧ ∀ y ∈ s, (f y, F y) ∈ u) : continuous_on f s :=
continuous_on_of_locally_uniform_approx_of_continuous_within_at $
  λ x hx u hu, ⟨s, self_mem_nhds_within, (L u hu).imp $
    λ F hF, ⟨hF.1.continuous_within_at hx, hF.2⟩⟩

/-- A function which can be locally uniformly approximated by continuous functions is continuous. -/
lemma continuous_of_locally_uniform_approx_of_continuous_at
  (L : ∀ (x : α), ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∃ F, continuous_at F x ∧ ∀ y ∈ t, (f y, F y) ∈ u) :
  continuous f :=
continuous_iff_continuous_at.2 $ λ x, continuous_at_of_locally_uniform_approx_of_continuous_at (L x)

/-- A function which can be uniformly approximated by continuous functions is continuous. -/
lemma continuous_of_uniform_approx_of_continuous
  (L : ∀ u ∈ 𝓤 β, ∃ F, continuous F ∧ ∀ y, (f y, F y) ∈ u) : continuous f :=
continuous_iff_continuous_on_univ.mpr $ continuous_on_of_uniform_approx_of_continuous_on $
  by simpa [continuous_iff_continuous_on_univ] using L

/-!
### Uniform limits

From the previous statements on uniform approximation, we deduce continuity results for uniform
limits.
-/

/-- A locally uniform limit on a set of functions which are continuous on this set is itself
continuous on this set. -/
protected lemma tendsto_locally_uniformly_on.continuous_on
  (h : tendsto_locally_uniformly_on F f p s) (hc : ∀ᶠ n in p, continuous_on (F n) s) [ne_bot p] :
  continuous_on f s :=
begin
  apply continuous_on_of_locally_uniform_approx_of_continuous_within_at (λ x hx u hu, _),
  rcases h u hu x hx with ⟨t, ht, H⟩,
  rcases (hc.and H).exists with ⟨n, hFc, hF⟩,
  exact ⟨t, ht, ⟨F n, hFc.continuous_within_at hx, hF⟩⟩
end

/-- A uniform limit on a set of functions which are continuous on this set is itself continuous
on this set. -/
protected lemma tendsto_uniformly_on.continuous_on (h : tendsto_uniformly_on F f p s)
  (hc : ∀ᶠ n in p, continuous_on (F n) s) [ne_bot p] : continuous_on f s :=
h.tendsto_locally_uniformly_on.continuous_on hc

/-- A locally uniform limit of continuous functions is continuous. -/
protected lemma tendsto_locally_uniformly.continuous (h : tendsto_locally_uniformly F f p)
  (hc : ∀ᶠ n in p, continuous (F n)) [ne_bot p] : continuous f :=
continuous_iff_continuous_on_univ.mpr $ h.tendsto_locally_uniformly_on.continuous_on $
  hc.mono $ λ n hn, hn.continuous_on

/-- A uniform limit of continuous functions is continuous. -/
protected lemma tendsto_uniformly.continuous (h : tendsto_uniformly F f p)
  (hc : ∀ᶠ n in p, continuous (F n)) [ne_bot p] : continuous f :=
h.tendsto_locally_uniformly.continuous hc

/-!
### Composing limits under uniform convergence

In general, if `Fₙ` converges pointwise to a function `f`, and `gₙ` tends to `x`, it is not true
that `Fₙ gₙ` tends to `f x`. It is true however if the convergence of `Fₙ` to `f` is uniform. In
this paragraph, we prove variations around this statement.
-/

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` within a set `s` to a function `f`
which is continuous at `x` within `s `, and `gₙ` tends to `x` within `s`, then `Fₙ (gₙ)` tends
to `f x`. -/
lemma tendsto_comp_of_locally_uniform_limit_within
  (h : continuous_within_at f s x) (hg : tendsto g p (𝓝[s] x))
  (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
begin
  apply uniform.tendsto_nhds_right.2 (λ u₀ hu₀, _),
  obtain ⟨u₁, h₁, u₁₀⟩ : ∃ (u : set (β × β)) (H : u ∈ 𝓤 β), comp_rel u u ⊆ u₀ :=
    comp_mem_uniformity_sets hu₀,
  rcases hunif u₁ h₁ with ⟨s, sx, hs⟩,
  have A : ∀ᶠ n in p, g n ∈ s := hg sx,
  have B : ∀ᶠ n in p, (f x, f (g n)) ∈ u₁ := hg (uniform.continuous_within_at_iff'_right.1 h h₁),
  refine ((hs.and A).and B).mono (λ y hy, _),
  rcases hy with ⟨⟨H1, H2⟩, H3⟩,
  exact u₁₀ (prod_mk_mem_comp_rel H3 (H1 _ H2))
end

/-- If `Fₙ` converges locally uniformly on a neighborhood of `x` to a function `f` which is
continuous at `x`, and `gₙ` tends to `x`, then `Fₙ (gₙ)` tends to `f x`. -/
lemma tendsto_comp_of_locally_uniform_limit (h : continuous_at f x) (hg : tendsto g p (𝓝 x))
  (hunif : ∀ u ∈ 𝓤 β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, (f y, F n y) ∈ u) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
begin
  rw ← continuous_within_at_univ at h,
  rw ← nhds_within_univ at hunif hg,
  exact tendsto_comp_of_locally_uniform_limit_within h hg hunif
end

/-- If `Fₙ` tends locally uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then
`Fₙ gₙ` tends to `f x` if `f` is continuous at `x` within `s` and `x ∈ s`. -/
lemma tendsto_locally_uniformly_on.tendsto_comp (h : tendsto_locally_uniformly_on F f p s)
  (hf : continuous_within_at f s x) (hx : x ∈ s) (hg : tendsto g p (𝓝[s] x)) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit_within hf hg (λ u hu, h u hu x hx)

/-- If `Fₙ` tends uniformly to `f` on a set `s`, and `gₙ` tends to `x` within `s`, then `Fₙ gₙ`
tends to `f x` if `f` is continuous at `x` within `s`. -/
lemma tendsto_uniformly_on.tendsto_comp (h : tendsto_uniformly_on F f p s)
  (hf : continuous_within_at f s x) (hg : tendsto g p (𝓝[s] x)) :
  tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit_within hf hg (λ u hu,
  ⟨s, self_mem_nhds_within, h u hu⟩)

/-- If `Fₙ` tends locally uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
lemma tendsto_locally_uniformly.tendsto_comp (h : tendsto_locally_uniformly F f p)
  (hf : continuous_at f x) (hg : tendsto g p (𝓝 x)) : tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
tendsto_comp_of_locally_uniform_limit hf hg (λ u hu, h u hu x)

/-- If `Fₙ` tends uniformly to `f`, and `gₙ` tends to `x`, then `Fₙ gₙ` tends to `f x`. -/
lemma tendsto_uniformly.tendsto_comp (h : tendsto_uniformly F f p)
  (hf : continuous_at f x) (hg : tendsto g p (𝓝 x)) : tendsto (λ n, F n (g n)) p (𝓝 (f x)) :=
h.tendsto_locally_uniformly.tendsto_comp hf hg

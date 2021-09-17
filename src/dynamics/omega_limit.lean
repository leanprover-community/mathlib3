/-
Copyright (c) 2020 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo
-/
import dynamics.flow

/-!
# ω-limits

For a function `ϕ : τ → α → β` where `β` is a topological space, we
define the ω-limit under `ϕ` of a set `s` in `α` with respect to
filter `f` on `τ`: an element `y : β` is in the ω-limit of `s` if the
forward images of `s` intersect arbitrarily small neighbourhoods of
`y` frequently "in the direction of `f`".

In practice `ϕ` is often a continuous monoid-act, but the definition
requires only that `ϕ` has a coercion to the appropriate function
type. In the case where `τ` is `ℕ` or `ℝ` and `f` is `at_top`, we
recover the usual definition of the ω-limit set as the set of all `y`
such that there exist sequences `(tₙ)`, `(xₙ)` such that `ϕ tₙ xₙ ⟶ y`
as `n ⟶ ∞`.

## Notations

The `omega_limit` locale provides the localised notation `ω` for
`omega_limit`, as well as `ω⁺` and `ω⁻` for `omega_limit at_top` and
`omega_limit at_bot` respectively for when the acting monoid is
endowed with an order.
-/

open set function filter
open_locale topological_space

/-!
### Definition and notation
-/

section omega_limit

variables {τ : Type*} {α : Type*} {β : Type*} {ι : Type*}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def omega_limit [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : set β :=
⋂ u ∈ f, closure (image2 ϕ u s)

localized "notation `ω` := omega_limit" in omega_limit

localized "notation `ω⁺` := omega_limit at_top" in omega_limit
localized "notation `ω⁻` := omega_limit at_bot" in omega_limit

variables [topological_space β]
variables (f : filter τ) (ϕ : τ → α → β) (s s₁ s₂: set α)

/-!
### Elementary properties
-/

lemma omega_limit_def : ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ u s) := rfl

lemma omega_limit_subset_of_tendsto {m : τ → τ} {f₁ f₂ : filter τ} (hf : tendsto m f₁ f₂) :
  ω f₁ (λ t x, ϕ (m t) x) s ⊆ ω f₂ ϕ s :=
begin
  apply Inter_subset_Inter2, intro u,  use m ⁻¹' u,
  apply Inter_subset_Inter2, intro hu, use tendsto_def.mp hf _ hu,
  rw ←image2_image_left,
  exact closure_mono (image2_subset (image_preimage_subset _ _) subset.rfl),
end

lemma omega_limit_mono_left {f₁ f₂ : filter τ} (hf : f₁ ≤ f₂) : ω f₁ ϕ s ⊆ ω f₂ ϕ s :=
omega_limit_subset_of_tendsto ϕ s (tendsto_id' hf)

lemma omega_limit_mono_right {s₁ s₂ : set α} (hs : s₁ ⊆ s₂) : ω f ϕ s₁ ⊆ ω f ϕ s₂ :=
bInter_subset_bInter_right $ λ u hu, closure_mono (image2_subset subset.rfl hs)

lemma is_closed_omega_limit : is_closed (ω f ϕ s) :=
is_closed_Inter $ λ u, is_closed_Inter $ λ hu, is_closed_closure

lemma maps_to_omega_limit' {α' β' : Type*} [topological_space β'] {f : filter τ} {ϕ : τ → α → β}
  {ϕ' : τ → α' → β'} {ga : α → α'} {s' : set α'} (hs : maps_to ga s s')
  {gb : β → β'} (hg : ∀ᶠ t in f, eq_on (gb ∘ (ϕ t)) (ϕ' t ∘ ga) s)
  (hgc : continuous gb) :
  maps_to gb (ω f ϕ s) (ω f ϕ' s') :=
begin
  simp only [omega_limit_def, mem_Inter, maps_to],
  intros y hy u hu,
  refine map_mem_closure hgc (hy _ (inter_mem hu hg)) (forall_image2_iff.2 $ λ t ht x hx, _),
  calc gb (ϕ t x) = ϕ' t (ga x) : ht.2 hx
  ... ∈ image2 ϕ' u s' : mem_image2_of_mem ht.1 (hs hx)
end

lemma maps_to_omega_limit {α' β' : Type*} [topological_space β'] {f : filter τ} {ϕ : τ → α → β}
  {ϕ' : τ → α' → β'} {ga : α → α'} {s' : set α'} (hs : maps_to ga s s')
  {gb : β → β'} (hg : ∀ t x, gb (ϕ t x) = ϕ' t (ga x))
  (hgc : continuous gb) :
  maps_to gb (ω f ϕ s) (ω f ϕ' s') :=
maps_to_omega_limit' _ hs (eventually_of_forall $ λ t x hx, hg t x) hgc

lemma omega_limit_image_eq {α' : Type*} (ϕ : τ → α' → β) (f : filter τ) (g : α → α') :
  ω f ϕ (g '' s) = ω f (λ t x, ϕ t (g x)) s :=
by simp only [omega_limit, image2_image_right]

lemma omega_limit_preimage_subset {α' : Type*} (ϕ : τ → α' → β) (s : set α') (f : filter τ)
  (g : α → α') :
  ω f (λ t x, ϕ t (g x)) (g ⁻¹' s) ⊆ ω f ϕ s :=
maps_to_omega_limit _ (maps_to_preimage _ _) (λ t x, rfl) continuous_id

/-!
### Equivalent definitions of the omega limit

The next few lemmas are various versions of the property
characterising ω-limits:
-/

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
lemma mem_omega_limit_iff_frequently (y : β) : y ∈ ω f ϕ s ↔
  ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).nonempty :=
begin
  simp_rw [frequently_iff, omega_limit_def, mem_Inter, mem_closure_iff_nhds],
  split,
  { intros h _ hn _ hu,
    rcases h _ hu _ hn with ⟨_, _, _, _, ht, hx, hϕtx⟩,
    exact ⟨_, ht, _, hx, by rwa [mem_preimage, hϕtx]⟩,
  },
  { intros h _ hu _ hn,
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩,
    exact  ⟨_, hϕtx, _, _, ht, hx, rfl⟩ }
end

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
lemma mem_omega_limit_iff_frequently₂ (y : β) : y ∈ ω f ϕ s ↔
  ∀ n ∈ 𝓝 y, ∃ᶠ t in f, (ϕ t '' s ∩ n).nonempty :=
by simp_rw [mem_omega_limit_iff_frequently, image_inter_nonempty_iff]

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
lemma mem_omega_limit_singleton_iff_map_cluster_point (x : α) (y : β) :
  y ∈ ω f ϕ {x} ↔ map_cluster_pt y f (λ t, ϕ t x) :=
by simp_rw [mem_omega_limit_iff_frequently, map_cluster_pt_iff, singleton_inter_nonempty,
  mem_preimage]

/-!
### Set operations and omega limits
-/

lemma omega_limit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
subset_inter (omega_limit_mono_right _ _ (inter_subset_left _ _))
  (omega_limit_mono_right _ _(inter_subset_right _ _))

lemma omega_limit_Inter (p : ι → set α) : ω f ϕ (⋂ i, p i) ⊆ ⋂ i, ω f ϕ (p i) :=
subset_Inter $ λ i, omega_limit_mono_right _ _ (Inter_subset _ _)

lemma omega_limit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ :=
begin
  ext y, split,
  { simp only [mem_union, mem_omega_limit_iff_frequently, union_inter_distrib_right,
      union_nonempty, frequently_or_distrib],
    contrapose!,
    simp only [not_frequently, not_nonempty_iff_eq_empty, ← subset_empty_iff],
    rintro ⟨⟨n₁, hn₁, h₁⟩, ⟨n₂, hn₂, h₂⟩⟩,
    refine ⟨n₁ ∩ n₂, inter_mem hn₁ hn₂, h₁.mono $ λ t, _, h₂.mono $ λ t, _⟩,
    exacts [subset.trans $ inter_subset_inter_right _ $ preimage_mono $ inter_subset_left _ _,
      subset.trans $ inter_subset_inter_right _ $ preimage_mono $ inter_subset_right _ _] },
  { rintros (hy|hy),
    exacts [omega_limit_mono_right _ _ (subset_union_left  _ _) hy,
      omega_limit_mono_right _ _ (subset_union_right _ _) hy] },
end

lemma omega_limit_Union (p : ι → set α) : (⋃ i, ω f ϕ (p i)) ⊆ ω f ϕ ⋃ i, p i :=
by { rw Union_subset_iff,
     exact λ i, omega_limit_mono_right _ _ (subset_Union _ _)}

/-!
Different expressions for omega limits, useful for rewrites. In
particular, one may restrict the intersection to sets in `f` which are
subsets of some set `v` also in `f`.
-/

lemma omega_limit_eq_Inter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
bInter_eq_Inter _ _

lemma omega_limit_eq_bInter_inter {v : set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ (u ∩ v) s) :=
subset.antisymm
  (Inter_subset_Inter2 (λ u, ⟨u ∩ v,
   Inter_subset_Inter2 (λ hu, ⟨inter_mem hu hv, subset.rfl⟩)⟩))
  (Inter_subset_Inter (λ u,
   Inter_subset_Inter (λ hu, closure_mono
     (image2_subset (inter_subset_left _ _) subset.rfl))))

lemma omega_limit_eq_Inter_inter {v : set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂ (u : ↥f.sets), closure (image2 ϕ (u ∩ v) s) :=
by { rw omega_limit_eq_bInter_inter _ _ _ hv, apply bInter_eq_Inter }

lemma omega_limit_subset_closure_fw_image {u : set τ} (hu : u ∈ f) :
  ω f ϕ s ⊆ closure (image2 ϕ u s) :=
begin
  rw omega_limit_eq_Inter,
  intros _ hx,
  rw mem_Inter at hx,
  exact hx ⟨u, hu⟩,
end

/-!
### `ω-limits and compactness
-/

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
lemma eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
  {c : set β} (hc₁ : is_compact c) (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c)
  {n : set β} (hn₁ : is_open n) (hn₂ : ω f ϕ s ⊆ n) :
  ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
begin
  rcases hc₂ with ⟨v, hv₁, hv₂⟩,
  let k := closure (image2 ϕ v s),
  have hk : is_compact (k \ n) :=
    is_compact.diff (compact_of_is_closed_subset hc₁ is_closed_closure hv₂) hn₁,
  let j := λ u, (closure (image2 ϕ (u ∩ v) s))ᶜ,
  have hj₁ : ∀ u ∈ f, is_open (j u), from
    λ _ _, (is_open_compl_iff.mpr is_closed_closure),
  have hj₂ : k \ n ⊆ ⋃ u ∈ f, j u, begin
    have : (⋃ u ∈ f, j u) = ⋃ (u : ↥f.sets), j u, from bUnion_eq_Union _ _,
    rw [this, diff_subset_comm, diff_Union],
    rw omega_limit_eq_Inter_inter _ _ _ hv₁ at hn₂,
    simp_rw diff_compl,
    rw ←inter_Inter,
    exact subset.trans (inter_subset_right _ _) hn₂,
  end,
  rcases hk.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁ : ∀ u ∈ g, u ∈ f, hg₂, hg₃⟩,
  let w := (⋂ u ∈ g, u) ∩ v,
  have hw₂ : w ∈ f, by simpa *,
  have hw₃ : k \ n ⊆ (closure (image2 ϕ w s))ᶜ, from
    calc k \ n ⊆ ⋃ u ∈ g, j u : hg₃
    ... ⊆ (closure (image2 ϕ w s))ᶜ :
    begin
      simp only [Union_subset_iff, compl_subset_compl],
      intros u hu,
      mono* using [w],
      exact Inter_subset_of_subset u (Inter_subset_of_subset hu subset.rfl),
    end,
  have hw₄ : kᶜ ⊆ (closure (image2 ϕ w s))ᶜ, begin
    rw compl_subset_compl,
    calc closure (image2 ϕ w s)
        ⊆ _ : closure_mono (image2_subset (inter_subset_right _ _) subset.rfl)
  end,
  have hnc : nᶜ ⊆ (k \ n) ∪ kᶜ, by rw [union_comm, ←inter_subset, diff_eq, inter_comm],
  have hw : closure (image2 ϕ w s) ⊆ n, from
    compl_subset_compl.mp (subset.trans hnc (union_subset hw₃ hw₄)),
  exact ⟨_, hw₂, hw⟩
end

/-- A set is eventually carried into any open neighbourhood of its ω-limit:
if `c` is a compact set such that `closure {ϕ t x | t ∈ v, x ∈ s} ⊆ c` for some `v ∈ f`
and `n` is an open neighbourhood of `ω f ϕ s`, then for some `u ∈ f` we have
`closure {ϕ t x | t ∈ u, x ∈ s} ⊆ n`. -/
lemma eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
  [t2_space β] {c : set β} (hc₁ : is_compact c) (hc₂ : ∀ᶠ t in f, maps_to (ϕ t) s c)
  {n : set β} (hn₁ : is_open n) (hn₂ : ω f ϕ s ⊆ n) :
  ∃ u ∈ f, closure (image2 ϕ u s) ⊆ n :=
eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
  f ϕ _ hc₁ ⟨_, hc₂, closure_minimal (image2_subset_iff.2 (λ t, id)) hc₁.is_closed⟩ hn₁ hn₂

lemma eventually_maps_to_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
  [t2_space β] {c : set β} (hc₁ : is_compact c) (hc₂ : ∀ᶠ t in f, maps_to (ϕ t) s c)
  {n : set β} (hn₁ : is_open n) (hn₂ : ω f ϕ s ⊆ n) :
  ∀ᶠ t in f, maps_to (ϕ t) s n :=
begin
  rcases eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset
    f ϕ s hc₁ hc₂ hn₁ hn₂ with ⟨u, hu_mem, hu⟩,
  refine mem_of_superset hu_mem (λ t ht x hx, _),
  exact hu (subset_closure $ mem_image2_of_mem ht hx)
end

lemma eventually_closure_subset_of_is_open_of_omega_limit_subset [compact_space β]
  {v : set β} (hv₁ : is_open v) (hv₂ : ω f ϕ s ⊆ v) :
  ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v :=
eventually_closure_subset_of_is_compact_absorbing_of_is_open_of_omega_limit_subset'
  _ _ _ compact_univ ⟨univ, univ_mem, subset_univ _⟩ hv₁ hv₂

lemma eventually_maps_to_of_is_open_of_omega_limit_subset [compact_space β]
  {v : set β} (hv₁ : is_open v) (hv₂ : ω f ϕ s ⊆ v) :
  ∀ᶠ t in f, maps_to (ϕ t) s v :=
begin
  rcases eventually_closure_subset_of_is_open_of_omega_limit_subset f ϕ s hv₁ hv₂
    with ⟨u, hu_mem, hu⟩,
  refine mem_of_superset hu_mem (λ t ht x hx, _),
  exact hu (subset_closure $ mem_image2_of_mem ht hx)
end

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
lemma nonempty_omega_limit_of_is_compact_absorbing [ne_bot f] {c : set β} (hc₁ : is_compact c)
  (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c) (hs : s.nonempty) :
  (ω f ϕ s).nonempty :=
begin
  rcases hc₂ with ⟨v, hv₁, hv₂⟩,
  rw omega_limit_eq_Inter_inter _ _ _ hv₁,
  apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed,
  { rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩,
    use ⟨u₁ ∩ u₂, inter_mem hu₁ hu₂⟩, split,
   all_goals { exact closure_mono (image2_subset
        (inter_subset_inter_left _ (by simp)) subset.rfl) }},
  { intro u,
    have hn : (image2 ϕ (u ∩ v) s).nonempty, from
      nonempty.image2 (nonempty_of_mem (inter_mem u.prop hv₁)) hs,
    exact hn.mono subset_closure },
  { intro _,
    apply compact_of_is_closed_subset hc₁ is_closed_closure,
    calc _ ⊆ closure (image2 ϕ v s) : closure_mono (image2_subset
                                        (inter_subset_right _ _) subset.rfl)
    ...    ⊆ c : hv₂ },
  { exact λ _, is_closed_closure },
end

lemma nonempty_omega_limit [compact_space β] [ne_bot f] (hs : s.nonempty) :
  (ω f ϕ s).nonempty :=
nonempty_omega_limit_of_is_compact_absorbing _ _ _
  compact_univ ⟨univ, univ_mem, subset_univ _⟩ hs

end omega_limit

/-!
### ω-limits of Flows by a Monoid
-/

namespace flow

variables
{τ : Type*} [topological_space τ] [add_monoid τ] [has_continuous_add τ]
{α : Type*} [topological_space α]
(f : filter τ) (ϕ : flow τ α) (s : set α)

open_locale omega_limit

lemma is_invariant_omega_limit (hf : ∀ t, tendsto ((+) t) f f) :
  is_invariant ϕ (ω f ϕ s) :=
λ t, maps_to.mono (subset.refl _) (omega_limit_subset_of_tendsto ϕ s (hf t)) $
  maps_to_omega_limit _ (maps_to_id _) (λ t' x, (ϕ.map_add _ _ _).symm)
    (continuous_const.flow ϕ continuous_id)

lemma omega_limit_image_subset (t : τ) (ht : tendsto (+ t) f f) :
  ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s :=
begin
  simp only [omega_limit_image_eq, ← map_add],
  exact omega_limit_subset_of_tendsto ϕ s ht
end

end flow

/-!
### ω-limits of Flows by a Group
-/

namespace flow

variables
{τ : Type*} [topological_space τ] [add_comm_group τ] [topological_add_group τ]
{α : Type*} [topological_space α]
(f : filter τ) (ϕ : flow τ α) (s : set α)

open_locale omega_limit

/-- the ω-limit of a forward image of `s` is the same as the ω-limit of `s`. -/
@[simp] lemma omega_limit_image_eq (hf : ∀ t, tendsto (+ t) f f) (t : τ) :
  ω f ϕ (ϕ t '' s) = ω f ϕ s :=
subset.antisymm (omega_limit_image_subset _ _ _ _ (hf t)) $
calc ω f ϕ s = ω f ϕ (ϕ (-t) '' (ϕ t '' s)) : by simp [image_image, ← map_add]
... ⊆ ω f ϕ (ϕ t '' s) : omega_limit_image_subset _ _ _ _ (hf _)

lemma omega_limit_omega_limit (hf : ∀ t, tendsto ((+) t) f f) :
  ω f ϕ (ω f ϕ s) ⊆ ω f ϕ s :=
begin
  simp only [subset_def, mem_omega_limit_iff_frequently₂, frequently_iff],
  intros _ h,
  rintro n hn u hu,
  rcases mem_nhds_iff.mp hn with ⟨o, ho₁, ho₂, ho₃⟩,
  rcases h o (is_open.mem_nhds ho₂ ho₃) hu with ⟨t, ht₁, ht₂⟩,
  have l₁ : (ω f ϕ s ∩ o).nonempty, from
    ht₂.mono (inter_subset_inter_left _
      ((is_invariant_iff_image _ _).mp (is_invariant_omega_limit _ _ _ hf) _)),
  have l₂ : ((closure (image2 ϕ u s)) ∩ o).nonempty :=
    l₁.mono (λ b hb, ⟨omega_limit_subset_closure_fw_image _ _ _ hu hb.1, hb.2⟩),
  have l₃ : (o ∩ image2 ϕ u s).nonempty,
  begin
    rcases l₂ with ⟨b, hb₁, hb₂⟩,
    exact mem_closure_iff_nhds.mp hb₁ o (is_open.mem_nhds ho₂ hb₂)
  end,
  rcases l₃ with ⟨ϕra, ho, ⟨_, _, hr, ha, hϕra⟩⟩,
  exact ⟨_, hr, ϕra, ⟨_, ha, hϕra⟩, ho₁ ho⟩,
end

end flow

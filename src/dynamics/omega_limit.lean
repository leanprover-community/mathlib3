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

/-!
### ω-limit sets
-/

section omega_limit

variables {τ : Type*} {α : Type*} {β : Type*}

/-- The ω-limit of a set `s` under `ϕ` with respect to a filter `f` is
    ⋂ u ∈ f, cl (ϕ u s). -/
def omega_limit [topological_space β] (f : filter τ) (ϕ : τ → α → β) (s : set α) : set β :=
⋂ u ∈ f, closure (image2 ϕ u s)

localized "notation `ω` := omega_limit" in omega_limit

localized "notation `ω⁺` := omega_limit at_top" in omega_limit
localized "notation `ω⁺` := omega_limit at_bot" in omega_limit

variables [topological_space β]
variables (f : filter τ) (ϕ : τ → α → β) (s s₁ s₂: set α)

-- some elementary properties:

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
begin
  apply Inter_subset_Inter, intro _,
  apply Inter_subset_Inter, intro _,
  exact closure_mono (image2_subset subset.rfl hs),
end

lemma is_closed_omega_limit : is_closed (ω f ϕ s) :=
begin
  apply is_closed_Inter, intro _,
  apply is_closed_Inter, intro _,
  exact is_closed_closure,
end

-- the next few lemmas are various versions of the property
-- characterising ω-limits:

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    preimages of an arbitrary neighbourhood of `y` frequently
    (w.r.t. `f`) intersects of `s`. -/
lemma mem_omega_limit_iff_frequently (y : β) : y ∈ ω f ϕ s ↔
  ∀ n ∈ nhds y, ∃ᶠ t in f, (s ∩ ϕ t ⁻¹' n).nonempty :=
begin
  simp_rw frequently_iff,
  split,
  { intros h _ hn _ hu,
    simp_rw [omega_limit_def, mem_Inter] at h,
    rcases mem_closure_iff_nhds.mp (h _ hu) _ hn with
      ⟨_, _, _, _, ht, hx, hϕtx⟩,
    exact ⟨_, ht, _, hx, show _ ∈ n, by rwa hϕtx⟩,
  },
  { rintro h _ ⟨_, hc⟩,
    rw [←hc, mem_Inter, mem_closure_iff_nhds],
    intros hu _ hn,
    rcases h _ hn hu with ⟨_, ht, _, hx, hϕtx⟩,
    exact  ⟨_, hϕtx, _, _, ht, hx, rfl⟩ }
end

/-- An element `y` is in the ω-limit set of `s` w.r.t. `f` if the
    forward images of `s` frequently (w.r.t. `f`) intersect arbitrary
    neighbourhoods of `y`. -/
lemma mem_omega_limit_iff_frequently₂ (y : β) : y ∈ ω f ϕ s ↔
  ∀ n ∈ nhds y, ∃ᶠ t in f, (ϕ t '' s ∩ n).nonempty :=
begin
  rw mem_omega_limit_iff_frequently,
  have : ∀ t n, (ϕ t '' s ∩ n).nonempty ↔ (s ∩ ϕ t ⁻¹' n).nonempty, begin
    intros t n,
    split,
    { rintro ⟨_, ⟨x, hx₁, hx₂⟩, hy₂⟩,
      exact ⟨x, hx₁, show ϕ t x ∈ n, from hx₂.symm ▸ hy₂⟩ },
    { rintro ⟨_, hx₁, hx₂⟩, exact ⟨_, ⟨_, hx₁, rfl⟩, hx₂⟩ },
  end,
  simp_rw this,
end

/-- An element `y` is in the ω-limit of `x` w.r.t. `f` if the forward
    images of `x` frequently (w.r.t. `f`) falls within an arbitrary
    neighbourhood of `y`. -/
lemma mem_omega_limit_singleton_iff_map_cluster_point (x : α) (y : β) :
  y ∈ ω f ϕ {x} ↔ map_cluster_pt y f (λ t, ϕ t x) :=
begin
  rw map_cluster_pt_iff,
  have l : ∀ t x v, ϕ t x ∈ v ↔ ({x} ∩ ϕ t ⁻¹' v).nonempty, begin
    intros _ _ _,
    simp_rw [←image_inter_nonempty_iff, image_singleton, singleton_inter_nonempty]
  end,
  simp_rw [mem_omega_limit_iff_frequently, l],
end

lemma omega_limit_inter : ω f ϕ (s₁ ∩ s₂) ⊆ ω f ϕ s₁ ∩ ω f ϕ s₂ :=
begin
  unfold omega_limit,
  simp_rw ←Inter_inter_distrib,
  apply Inter_subset_Inter, intro u,
  apply Inter_subset_Inter, intro hu,
  calc closure (image2 ϕ u (s₁ ∩ s₂))
      ⊆ closure (_ ∩ _)       : closure_mono image2_inter_subset_right
  ... ⊆ closure _ ∩ closure _ : closure_inter_subset_inter_closure _ _,
end

lemma omega_limit_union : ω f ϕ (s₁ ∪ s₂) = ω f ϕ s₁ ∪ ω f ϕ s₂ :=
begin
  apply subset.antisymm,
  { intros y hy,
    simp_rw [mem_omega_limit_iff_frequently, frequently_iff] at hy,
    apply classical.by_contradiction,
    rw [mem_union, not_or_distrib],
    simp_rw [mem_omega_limit_iff_frequently, frequently_iff, not_forall, not_exists],
    rintro ⟨⟨n₁, hn₁, u₁, hu₁, h₁⟩, n₂, hn₂, u₂, hu₂, h₂⟩,
    rcases hy _ (inter_mem_sets hn₁ hn₂) (inter_mem_sets hu₁ hu₂) with ⟨t, ht, h⟩,
    rw [union_inter_distrib_right, union_nonempty] at h,
    exact or.elim h
      (λ he, h₁ t ht.1 (nonempty.mono
        (inter_subset_inter_right _ (preimage_mono (inter_subset_left  _ _))) he))
      (λ he, h₂ t ht.2 (nonempty.mono
        (inter_subset_inter_right _ (preimage_mono (inter_subset_right _ _))) he)) },
  { intros y hy,
    exact or.elim hy
    (λ hy₂, omega_limit_mono_right _ _ (subset_union_left  _ _) hy₂)
    (λ hy₂, omega_limit_mono_right _ _ (subset_union_right _ _) hy₂) },
end

lemma omega_limit_eq_Inter : ω f ϕ s = ⋂ u : ↥f.sets, closure (image2 ϕ u s) :=
bInter_eq_Inter _ _

lemma omega_limit_eq_bInter_inter {v : set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂ u ∈ f, closure (image2 ϕ (u ∩ v) s) :=
subset.antisymm
  (Inter_subset_Inter2 (λ u, ⟨u ∩ v,
   Inter_subset_Inter2 (λ hu, ⟨inter_mem_sets hu hv, subset.rfl⟩)⟩))
  (Inter_subset_Inter (λ u,
   Inter_subset_Inter (λ hu, closure_mono
     (image2_subset (inter_subset_left _ _) subset.rfl))))

lemma omega_limit_eq_Inter_inter {v : set τ} (hv : v ∈ f) :
  ω f ϕ s = ⋂ (u : ↥f.sets), closure (image2 ϕ (u ∩ v) s) :=
by { rw omega_limit_eq_bInter_inter _ _ _ hv, apply bInter_eq_Inter }

-- ω-limits in compact spaces:

/-- A set is eventually carried into any neighbourhood of its ω-limit:
    for any neighbourhood v of ω f ϕ s, there exists u ∈ f such that
    cl (ϕ u s) ⊆ v -/
lemma eventually_subset_nhd_omega_limit [compact_space β]
  {v : set β} (ho : is_open v) (hv : ω f ϕ s ⊆ v) :
  ∃ u ∈ f, closure (image2 ϕ u s) ⊆ v :=
begin
  let j := λ u, (closure (image2 ϕ u s))ᶜ,
  have hj₁ : ∀ u ∈ f, is_open (j u),
   from λ _ _, is_open_compl_iff.mpr is_closed_closure,
  have hj₂ : vᶜ ⊆ ⋃ u ∈ f, j u,
   by { rw [compl_subset_comm], simp_rw [compl_Union, compl_compl'], assumption },
  have hc : is_compact vᶜ, from (is_closed_compl_iff.mpr ho).compact,
  rcases hc.elim_finite_subcover_image hj₁ hj₂ with ⟨g, hg₁, hg₂, hg₃⟩,
  let w := ⋂₀ g,
  have hw₁ : w ∈ f, from sInter_mem_sets_of_finite hg₂ hg₁,
  have hw₂ : closure (image2 ϕ w s) ⊆ v, begin
    rw compl_subset_comm at hg₃,
    simp_rw [compl_Union, compl_compl'] at hg₃,
    calc closure (image2 ϕ w s)
        ⊆ ⋂ u ∈ g, closure (image2 ϕ u s) :
          subset_Inter (λ _, subset_Inter (λ hu, closure_mono
            (image2_subset (sInter_subset_of_mem hu) subset.rfl)))
    ... ⊆ v : hg₃,
  end,
  exact ⟨_, hw₁, hw₂⟩,
end

/-- The ω-limit of a nonempty set w.r.t. a nontrivial filter is nonempty. -/
lemma nonempty_omega_limit
  {c : set β} (hc₁ : is_compact c) (hc₂ : ∃ v ∈ f, closure (image2 ϕ v s) ⊆ c)
  (hs : s.nonempty) (hf : ne_bot f) : (ω f ϕ s).nonempty :=
begin
  rcases hc₂ with ⟨v, hv₁, hv₂⟩,
  rw omega_limit_eq_Inter_inter _ _ _ hv₁,
  apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed,
  { rintro ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩,
    use ⟨u₁ ∩ u₂, inter_mem_sets hu₁ hu₂⟩, split,
   all_goals { exact closure_mono (image2_subset
        (inter_subset_inter_left _ (by simp)) subset.rfl) }},
  { intro u,
    have hn : (image2 ϕ (u ∩ v) s).nonempty, from
      nonempty.image2 (hf.nonempty_of_mem (inter_mem_sets u.prop hv₁)) hs,
    exact hn.mono subset_closure },
  { intro _,
    apply compact_of_is_closed_subset hc₁ is_closed_closure,
    calc _ ⊆ closure (image2 ϕ v s) : closure_mono (image2_subset
                                        (inter_subset_right _ _) subset.rfl)
    ...    ⊆ c : hv₂ },
  { exact λ _, is_closed_closure },
end

lemma nonempty_omega_limit_of_compact [compact_space β]
  (hs : s.nonempty) (hf : ne_bot f) : (ω f ϕ s).nonempty :=
nonempty_omega_limit _ _ _ compact_univ ⟨univ, univ_mem_sets, subset_univ _⟩ hs hf

end omega_limit

namespace flow

variables
{τ : Type*} [topological_space τ] [add_monoid τ] [has_continuous_add τ]
{α : Type*} [topological_space α]
(f : filter τ) (ϕ : flow τ α) (s : set α)

open_locale omega_limit

lemma is_invariant_omega_limit (hf : ∀ t, tendsto (+ t) f f) :
  is_invariant ϕ (ω f ϕ s) :=
begin
  rw is_invariant_iff_image,
  intro t,
  calc ϕ t '' ω f ϕ s
      ⊆ _          : image_Inter_subset _ (ϕ t)
  ... ⊆ _          : Inter_subset_Inter (λ _, image_Inter_subset _ _)
  ... ⊆ ⋂ u ∈ f, _ : Inter_subset_Inter (λ _, Inter_subset_Inter (λ _,
                       (image_closure_subset_closure_image
                         (continuous_uncurry_left _ ϕ.continuous))))
  ... ⊆ ω f ϕ s : by { simp_rw [image_image2, map_add],
                       exact omega_limit_subset_of_tendsto _ _ (hf t) },
end

lemma omega_limit_fw_image_subset (hf : ∀ t, tendsto (λ t₁, t + t₁) f f) (t : τ) :
  ω f ϕ (ϕ t '' s) ⊆ ω f ϕ s :=
begin
    apply Inter_subset_Inter2, intro u,  use (λ t₁, t + t₁) ⁻¹' u,
    apply Inter_subset_Inter2, intro hu, use tendsto_def.mp (hf t) _ hu,
    apply closure_mono,
    simp_rw [image2_image_right, map_add],
    rw ←image2_image_left,
    exact image2_subset (image_preimage_subset _ _) subset.rfl,
end

end flow

-- ω-limits of flows by a group:
namespace flow

variables
{τ : Type*} [topological_space τ] [add_comm_group τ] [topological_add_group τ]
{α : Type*} [topological_space α]
(f : filter τ) (ϕ : flow τ α) (s : set α)

open_locale omega_limit

lemma omega_limit_fw_image_eq (hf : ∀ t, tendsto (+ t) f f) (t : τ) :
  ω f ϕ (ϕ t '' s) = ω f ϕ s :=
begin
  apply subset.antisymm,
  { have : ∀ t, tendsto (λ t₁, t + t₁) f f,
      by { simp_rw add_comm at hf, assumption },
    apply omega_limit_fw_image_subset,
    assumption },
  { calc ω f ϕ s
         ⊆ ω f (λ t₁ x, ϕ (t₁ - t) x) (ϕ t '' s) : 
           Inter_subset_Inter (λ _, Inter_subset_Inter (λ _, closure_mono
           (by { simp_rw [image2_image_right, map_add, add_sub_cancel'_right] })))
    ... ⊆ ω f ϕ (ϕ t '' s) :
          omega_limit_subset_of_tendsto _ _
          (by { simp_rw sub_eq_add_neg, exact hf (-t) })},
end

end flow

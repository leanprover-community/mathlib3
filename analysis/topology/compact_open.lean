/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/

import analysis.topology.continuity tactic.tidy

open set

universes u v w

section locally_compact

-- There are various definitions of "locally compact space" in the
-- literature, which agree for Hausdorff spaces but not in general.
-- This one is the precise condition on X needed for the evaluation
-- map C(X, Y) × X → Y to be continuous for all Y when C(X, Y) is
-- given the compact-open topology.
class locally_compact_space (α : Type u) [topological_space α] :=
(local_compact_nhds : ∀ (x : α) (n ∈ (nhds x).sets), ∃ s ∈ (nhds x).sets, s ⊆ n ∧ compact s)

variables {α : Type u} [topological_space α]

lemma locally_compact_of_compact_nhds [t2_space α]
  (h : ∀ x : α, ∃ s, s ∈ (nhds x).sets ∧ compact s) :
  locally_compact_space α :=
⟨assume x n hn,
  let ⟨u, un, uo, xu⟩ := mem_nhds_sets_iff.mp hn in
  let ⟨k, kx, kc⟩ := h x in
  -- K is compact but not necessarily contained in N.
  -- K \ U is again compact and doesn't contain x, so
  -- we may find open sets V, W separating x from K \ U.
  -- Then K \ W is a compact neighborhood of x contained in U.
  let ⟨v, w, vo, wo, xv, kuw, vw⟩ :=
    compact_compact_separated compact_singleton (compact_diff kc uo)
      (by rw [singleton_inter_eq_empty]; exact λ h, h.2 xu) in
  have wn : -w ∈ (nhds x).sets, from
   mem_nhds_sets_iff.mpr
     ⟨v, subset_compl_iff_disjoint.mpr vw, vo, singleton_subset_iff.mp xv⟩,
  ⟨k - w,
   filter.inter_mem_sets kx wn,
   subset.trans (diff_subset_comm.mp kuw) un,
   compact_diff kc wo⟩⟩

lemma locally_compact_of_compact [t2_space α] (h : compact (univ : set α)) :
  locally_compact_space α :=
locally_compact_of_compact_nhds (assume x, ⟨univ, mem_nhds_sets is_open_univ trivial, h⟩)

end locally_compact

section compact_open
variables {α : Type u} {β : Type v} {γ : Type w}
variables [topological_space α] [topological_space β] [topological_space γ]

local notation `C(` α `, ` β `)` := subtype (continuous : set (α → β))

def compact_open_gen {s : set α} (hs : compact s) {u : set β} (hu : is_open u) : set C(α,β) :=
{f | f.val '' s ⊆ u}

-- The compact-open topology on the space of continuous maps α → β.
def compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : compact s) (u : set β) (hu : is_open u), m = compact_open_gen hs hu}

local attribute [instance] compact_open

private lemma is_open_gen {s : set α} (hs : compact s) {u : set β} (hu : is_open u) :
  is_open (compact_open_gen hs hu) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

section functorial

variables {g : β → γ} (hg : continuous g)

def continuous_map.induced : C(α, β) → C(α, γ) :=
λ f, ⟨g ∘ f, f.property.comp hg⟩

private lemma preimage_gen {s : set α} (hs : compact s) {u : set γ} (hu : is_open u) :
  continuous_map.induced hg ⁻¹' (compact_open_gen hs hu) = compact_open_gen hs (hg _ hu) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [image_comp, image_subset_iff]
end

-- C(α, -) is a functor.
lemma continuous_induced : continuous (continuous_map.induced hg : C(α, β) → C(α, γ)) :=
continuous_generated_from $ assume m ⟨s, hs, u, hu, hm⟩,
  by rw [hm, preimage_gen]; apply is_open_gen

end functorial

section ev

variables (α β)
def ev : C(α, β) × α → β := λ p, p.1.val p.2

variables {α β}
-- The evaluation map C(α, β) × α → β is continuous if α is locally compact.
lemma continuous_ev [locally_compact_space α] : continuous (ev α β) :=
continuous_iff_tendsto.mpr $ assume ⟨f, x⟩ n hn,
  let ⟨v, vn, vo, fxv⟩ := mem_nhds_sets_iff.mp hn in
  have v ∈ (nhds (f.val x)).sets, from mem_nhds_sets vo fxv,
  let ⟨s, hs, sv, sc⟩ :=
    locally_compact_space.local_compact_nhds x (f.val ⁻¹' v)
      (f.property.tendsto x this) in
  let ⟨u, us, uo, xu⟩ := mem_nhds_sets_iff.mp hs in
  show (ev α β) ⁻¹' n ∈ (nhds (f, x)).sets, from
  let w := set.prod (compact_open_gen sc vo) u in
  have w ⊆ ev α β ⁻¹' n, from assume ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f'.val x' ∈ f'.val '' s  : mem_image_of_mem f'.val (us hx')
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn,
  have is_open w, from is_open_prod (is_open_gen _ _) uo,
  have (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  mem_nhds_sets_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

end ev

section coev

variables (α β)
def coev : β → C(α, β × α) :=
λ b, ⟨λ a, (b, a), continuous.prod_mk continuous_const continuous_id⟩

variables {α β}
lemma image_coev {y : β} (s : set α) : (coev α β y).val '' s = set.prod {y} s := by tidy

-- The coevaluation map β → C(α, β × α) is continuous (always).
lemma continuous_coev : continuous (coev α β) :=
continuous_generated_from $ begin
  rintros _ ⟨s, sc, u, uo, rfl⟩,
  rw is_open_iff_forall_mem_open,
  intros y hy,
  change (coev α β y).val '' s ⊆ u at hy,
  rw image_coev s at hy,
  rcases generalized_tube_lemma compact_singleton sc uo hy
    with ⟨v, w, vo, wo, yv, sw, vwu⟩,
  refine ⟨v, _, vo, singleton_subset_iff.mp yv⟩,
  intros y' hy',
  change (coev α β y').val '' s ⊆ u,
  rw image_coev s,
  exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu
end

end coev

end compact_open

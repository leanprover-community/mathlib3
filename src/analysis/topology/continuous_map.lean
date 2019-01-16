/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Type of continuous maps and the compact-open topology on them.
-/

import analysis.topology.continuity tactic.tidy

open set

universes u v w

def continuous_map (α : Type u) (β : Type v) [topological_space α] [topological_space β] :
  Type (max u v) :=
subtype (continuous : (α → β) → Prop)

local notation `C(` α `, ` β `)` := continuous_map α β

namespace continuous_map

section compact_open
variables {α : Type u} {β : Type v} {γ : Type w}
variables [topological_space α] [topological_space β] [topological_space γ]

instance : has_coe_to_fun C(α, β) :=
⟨λ_, α → β, λf, f.1⟩

def compact_open.gen (s : set α) (u : set β) : set C(α,β) := {f | f '' s ⊆ u}

-- The compact-open topology on the space of continuous maps α → β.
instance compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : compact s) (u : set β) (hu : is_open u), m = compact_open.gen s u}

private lemma is_open_gen {s : set α} (hs : compact s) {u : set β} (hu : is_open u) :
  is_open (compact_open.gen s u) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

section functorial

variables {g : β → γ} (hg : continuous g)

def induced (f : C(α, β)) : C(α, γ) := ⟨g ∘ f, f.property.comp hg⟩

private lemma preimage_gen {s : set α} (hs : compact s) {u : set γ} (hu : is_open u) :
  continuous_map.induced hg ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [image_comp, image_subset_iff]
end

/-- C(α, -) is a functor. -/
lemma continuous_induced : continuous (continuous_map.induced hg : C(α, β) → C(α, γ)) :=
continuous_generated_from $ assume m ⟨s, hs, u, hu, hm⟩,
  by rw [hm, preimage_gen hg hs hu]; exact is_open_gen hs (hg _ hu)

end functorial

section ev

variables (α β)
def ev (p : C(α, β) × α) : β := p.1 p.2

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
  let w := set.prod (compact_open.gen s v) u in
  have w ⊆ ev α β ⁻¹' n, from assume ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f'.val x' ∈ f'.val '' s  : mem_image_of_mem f'.val (us hx')
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn,
  have is_open w, from is_open_prod (is_open_gen sc vo) uo,
  have (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  mem_nhds_sets_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

end ev

section coev

variables (α β)
def coev (b : β) : C(α, β × α) := ⟨λ a, (b, a), continuous.prod_mk continuous_const continuous_id⟩

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

end continuous_map

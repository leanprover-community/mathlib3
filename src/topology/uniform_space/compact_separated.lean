/-
Copyright (c) 2020 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import topology.uniform_space.separation
import topology.uniform_space.uniform_convergence
/-!
# Compact separated uniform spaces

## Main statements

* `compact_space_uniformity`: On a separated compact uniform space, the topology determines the
  uniform structure, entourages are exactly the neighborhoods of the diagonal.
* `uniform_space_of_compact_t2`: every compact T2 topological structure is induced by a uniform
  structure. This uniform structure is described in the previous item.
* Heine-Cantor theorem: continuous functions on compact separated uniform spaces with values in
  uniform spaces are automatically uniformly continuous. There are several variations, the main one
  is `compact_space.uniform_continuous_of_continuous`.

## Implementation notes

The construction `uniform_space_of_compact_t2` is not declared as an instance, as it would badly
loop.

## tags

uniform space, uniform continuity, compact space
-/

open_locale classical uniformity topological_space filter
open filter uniform_space set

variables {α β γ : Type*} [uniform_space α] [uniform_space β]


/-!
### Uniformity on compact separated spaces
-/

/-- On a separated compact uniform space, the topology determines the uniform structure, entourages
are exactly the neighborhoods of the diagonal. -/
lemma compact_space_uniformity [compact_space α] [separated_space α] : 𝓤 α = ⨆ x : α, 𝓝 (x, x) :=
begin
  symmetry, refine le_antisymm supr_nhds_le_uniformity _,
  by_contra H,
  obtain ⟨V, hV, h⟩ : ∃ V : set (α × α), (∀ x : α, V ∈ 𝓝 (x, x)) ∧ 𝓤 α ⊓ 𝓟 Vᶜ ≠ ⊥,
  { simpa [le_iff_forall_inf_principal_compl] using H },
  let F := 𝓤 α ⊓ 𝓟 Vᶜ,
  haveI : ne_bot F := ⟨h⟩,
  obtain ⟨⟨x, y⟩, hx⟩ : ∃ (p : α × α), cluster_pt p F :=
    cluster_point_of_compact F,
  have : cluster_pt (x, y) (𝓤 α) :=
    hx.of_inf_left,
  obtain rfl : x = y := eq_of_uniformity_inf_nhds this,
  have : cluster_pt (x, x) (𝓟 Vᶜ) :=
   hx.of_inf_right,
  have : (x, x) ∉ interior V,
  { have : (x, x) ∈ closure Vᶜ, by rwa mem_closure_iff_cluster_pt,
    rwa closure_compl at this },
  have : (x, x) ∈ interior V,
  { rw mem_interior_iff_mem_nhds,
    exact hV x },
  contradiction
end

lemma unique_uniformity_of_compact_t2 [t : topological_space γ] [compact_space γ]
[t2_space γ] {u u' : uniform_space γ}
(h : u.to_topological_space = t) (h' : u'.to_topological_space = t) : u = u' :=
begin
  apply uniform_space_eq,
  change uniformity _ = uniformity _,
  haveI : @compact_space γ u.to_topological_space, { rw h ; assumption },
  haveI : @compact_space γ u'.to_topological_space, { rw h' ; assumption },
  haveI : @separated_space γ u, { rwa [separated_iff_t2, h] },
  haveI : @separated_space γ u', { rwa [separated_iff_t2, h'] },
  rw [compact_space_uniformity, compact_space_uniformity, h, h']
end

/-- The unique uniform structure inducing a given compact Hausdorff topological structure. -/
def uniform_space_of_compact_t2 [topological_space γ] [compact_space γ] [t2_space γ] :
  uniform_space γ :=
{ uniformity := ⨆ x, 𝓝 (x, x),
  refl := begin
    simp_rw [filter.principal_le_iff, mem_supr],
    rintros V V_in ⟨x, _⟩ ⟨⟩,
    exact mem_of_mem_nhds (V_in x),
  end,
  symm := begin
    refine le_of_eq _,
    rw map_supr,
    congr' with x : 1,
    erw [nhds_prod_eq, ← prod_comm],
  end,
  comp := begin
    /-
    This is the difficult part of the proof. We need to prove that, for each neighborhood W
    of the diagonal Δ, W ○ W is still a neighborhood of the diagonal.
    -/
    set 𝓝Δ := ⨆ x : γ, 𝓝 (x, x), -- The filter of neighborhoods of Δ
    set F := 𝓝Δ.lift' (λ (s : set (γ × γ)), s ○ s), -- Compositions of neighborhoods of Δ
    -- If this weren't true, then there would be V ∈ 𝓝Δ such that F ⊓ 𝓟 Vᶜ ≠ ⊥
    rw le_iff_forall_inf_principal_compl,
    intros V V_in,
    by_contra H,
    haveI : ne_bot (F ⊓ 𝓟 Vᶜ) := ⟨H⟩,
    -- Hence compactness would give us a cluster point (x, y) for F ⊓ 𝓟 Vᶜ
    obtain ⟨⟨x, y⟩, hxy⟩ : ∃ (p : γ × γ), cluster_pt p (F ⊓ 𝓟 Vᶜ) := cluster_point_of_compact _,
    -- In particular (x, y) is a cluster point of 𝓟 Vᶜ, hence is not in the interior of V,
    -- and a fortiori not in Δ, so x ≠ y
    have clV : cluster_pt (x, y) (𝓟 $ Vᶜ) := hxy.of_inf_right,
    have : (x, y) ∉ interior V,
    { have : (x, y) ∈ closure (Vᶜ), by rwa mem_closure_iff_cluster_pt,
      rwa closure_compl at this },
    have diag_subset : diagonal γ ⊆ interior V,
    { rw subset_interior_iff_nhds,
      rintros ⟨x, x⟩ ⟨⟩,
      exact (mem_supr.mp V_in : _) x },
    have x_ne_y : x ≠ y,
    { intro h,
      apply this,
      apply diag_subset,
      simp [h] },
    -- Since γ is compact and Hausdorff, it is normal, hence regular.
    haveI : normal_space γ := normal_of_compact_t2,
    -- So there are closed neighboords V₁ and V₂ of x and y contained in disjoint open neighborhoods
    -- U₁ and U₂.
    obtain
      ⟨U₁, U₁_in, V₁, V₁_in, U₂, U₂_in₂, V₂, V₂_in, V₁_cl, V₂_cl, U₁_op, U₂_op, VU₁, VU₂, hU₁₂⟩ :=
       disjoint_nested_nhds x_ne_y,
    -- We set U₃ := (V₁ ∪ V₂)ᶜ so that W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃ is an open
    -- neighborhood of Δ.
    let U₃ := (V₁ ∪ V₂)ᶜ,
    have U₃_op : is_open U₃ :=
      is_open_compl_iff.mpr (is_closed.union V₁_cl V₂_cl),
    let W := U₁ ×ˢ U₁ ∪ U₂ ×ˢ U₂ ∪ U₃ ×ˢ U₃,
    have W_in : W ∈ 𝓝Δ,
    { rw mem_supr,
      intros x,
      apply is_open.mem_nhds (is_open.union (is_open.union _ _) _),
      { by_cases hx : x ∈ V₁ ∪ V₂,
        { left,
          cases hx with hx hx ; [left, right] ; split ; tauto },
        { right,
          rw mem_prod,
          tauto }, },
      all_goals { simp only [is_open.prod, *] } },
    -- So W ○ W ∈ F by definition of F
    have : W ○ W ∈ F, by simpa only using mem_lift' W_in,
    -- And V₁ ×ˢ V₂ ∈ 𝓝 (x, y)
    have hV₁₂ : V₁ ×ˢ V₂ ∈ 𝓝 (x, y) := prod_mem_nhds V₁_in V₂_in,
    -- But (x, y) is also a cluster point of F so (V₁ ×ˢ V₂) ∩ (W ○ W) ≠ ∅
    -- However the construction of W implies (V₁ ×ˢ V₂) ∩ (W ○ W) = ∅.
    -- Indeed assume for contradiction there is some (u, v) in the intersection.
    obtain ⟨⟨u, v⟩, ⟨u_in, v_in⟩, w, huw, hwv⟩ := cluster_pt_iff.mp (hxy.of_inf_left) hV₁₂ this,
    -- So u ∈ V₁, v ∈ V₂, and there exists some w such that (u, w) ∈ W and (w ,v) ∈ W.
    -- Because u is in V₁ which is disjoint from U₂ and U₃, (u, w) ∈ W forces (u, w) ∈ U₁ ×ˢ U₁.
    have uw_in : (u, w) ∈ U₁ ×ˢ U₁ := (huw.resolve_right $ λ h, (h.1 $ or.inl u_in)).resolve_right
      (λ h, hU₁₂ ⟨VU₁ u_in, h.1⟩),
    -- Similarly, because v ∈ V₂, (w ,v) ∈ W forces (w, v) ∈ U₂ ×ˢ U₂.
    have wv_in : (w, v) ∈ U₂ ×ˢ U₂ := (hwv.resolve_right $ λ h, (h.2 $ or.inr v_in)).resolve_left
      (λ h, hU₁₂ ⟨h.2, VU₂ v_in⟩),
    -- Hence w ∈ U₁ ∩ U₂ which is empty.
    -- So we have a contradiction
    exact hU₁₂ ⟨uw_in.2, wv_in.1⟩,
  end,
  is_open_uniformity := begin
    -- Here we need to prove the topology induced by the constructed uniformity is the
    -- topology we started with.
    suffices : ∀ x : γ, filter.comap (prod.mk x) (⨆ y, 𝓝 (y ,y)) = 𝓝 x,
    { intros s,
      change is_open s ↔ _,
      simp_rw [is_open_iff_mem_nhds, nhds_eq_comap_uniformity_aux, this] },
    intros x,
    simp_rw [comap_supr, nhds_prod_eq, comap_prod,
             show prod.fst ∘ prod.mk x = λ y : γ, x, by ext ; simp,
             show prod.snd ∘ (prod.mk x) = (id : γ → γ), by ext ; refl, comap_id],
    rw [supr_split_single _ x, comap_const_of_mem (λ V, mem_of_mem_nhds)],
    suffices : ∀ y ≠ x, comap (λ (y : γ), x) (𝓝 y) ⊓ 𝓝 y ≤ 𝓝 x,
      by simpa,
    intros y hxy,
    simp [comap_const_of_not_mem (compl_singleton_mem_nhds hxy) (by simp)],
  end }

/-!
### Heine-Cantor theorem
-/

/-- Heine-Cantor: a continuous function on a compact separated uniform space is uniformly
continuous. -/
lemma compact_space.uniform_continuous_of_continuous [compact_space α] [separated_space α]
  {f : α → β} (h : continuous f) : uniform_continuous f :=
calc
map (prod.map f f) (𝓤 α) = map (prod.map f f) (⨆ x, 𝓝 (x, x))  : by rw compact_space_uniformity
                     ... =  ⨆ x, map (prod.map f f) (𝓝 (x, x)) : by rw map_supr
                     ... ≤ ⨆ x, 𝓝 (f x, f x)     : supr_mono (λ x, (h.prod_map h).continuous_at)
                     ... ≤ ⨆ y, 𝓝 (y, y)         : supr_comp_le (λ y, 𝓝 (y, y)) f
                     ... ≤ 𝓤 β                   : supr_nhds_le_uniformity

/-- Heine-Cantor: a continuous function on a compact separated set of a uniform space is
uniformly continuous. -/
lemma is_compact.uniform_continuous_on_of_continuous' {s : set α} {f : α → β}
  (hs : is_compact s) (hs' : is_separated s) (hf : continuous_on f s) : uniform_continuous_on f s :=
begin
  rw uniform_continuous_on_iff_restrict,
  rw is_separated_iff_induced at hs',
  rw is_compact_iff_compact_space at hs,
  rw continuous_on_iff_continuous_restrict at hf,
  resetI,
  exact compact_space.uniform_continuous_of_continuous hf,
end

/-- Heine-Cantor: a continuous function on a compact set of a separated uniform space
is uniformly continuous. -/
lemma is_compact.uniform_continuous_on_of_continuous [separated_space α] {s : set α} {f : α → β}
  (hs : is_compact s) (hf : continuous_on f s) : uniform_continuous_on f s :=
hs.uniform_continuous_on_of_continuous' (is_separated_of_separated_space s) hf

/-- A family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is locally compact,
`β` is compact and separated and `f` is continuous on `U × (univ : set β)` for some separated
neighborhood `U` of `x`. -/
lemma continuous_on.tendsto_uniformly [locally_compact_space α] [compact_space β]
  [separated_space β] [uniform_space γ] {f : α → β → γ} {x : α} {U : set α}
  (hxU : U ∈ 𝓝 x) (hU : is_separated U) (h : continuous_on ↿f (U ×ˢ (univ : set β))) :
  tendsto_uniformly f (f x) (𝓝 x) :=
begin
  rcases locally_compact_space.local_compact_nhds _ _ hxU with ⟨K, hxK, hKU, hK⟩,
  have : uniform_continuous_on ↿f (K ×ˢ (univ : set β)),
  { refine is_compact.uniform_continuous_on_of_continuous' (hK.prod compact_univ) _
      (h.mono $ prod_mono hKU subset.rfl),
    exact (hU.mono hKU).prod (is_separated_of_separated_space _) },
  exact this.tendsto_uniformly hxK
end

/-- A continuous family of functions `α → β → γ` tends uniformly to its value at `x` if `α` is
locally compact and `β` is compact and separated. -/
lemma continuous.tendsto_uniformly [separated_space α] [locally_compact_space α]
  [compact_space β] [separated_space β] [uniform_space γ]
  (f : α → β → γ) (h : continuous ↿f) (x : α) : tendsto_uniformly f (f x) (𝓝 x) :=
h.continuous_on.tendsto_uniformly univ_mem $ is_separated_of_separated_space _

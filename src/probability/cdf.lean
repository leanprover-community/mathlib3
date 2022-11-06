/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.constructions.borel_space

/-!
# Cdf

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

## Notation



## Implementation details



## References

* [F. Bar, *Quuxes*][bibkey]

-/


open measure_theory topological_space set measure_theory.measure filter

open_locale topological_space ennreal

section cdf

variables {α β : Type*} {X : α → β} {m₀ : measurable_space α} {μ : measure α}

/-- Cumulative distribution function -/
def cdf [preorder β] {m₀ : measurable_space α} (X : α → β) (μ : measure α) : β → ℝ≥0∞ :=
λ b, μ (X ⁻¹' Iic b)

lemma monotone_cdf [preorder β] {m₀ : measurable_space α} (X : α → β) (μ : measure α) :
  monotone (cdf X μ) :=
λ x y hxy, measure_mono (λ a ha, le_trans ha hxy)

lemma cdf_eq_map_Iic [preorder β] [measurable_space β] [topological_space β]
  [order_closed_topology β] [opens_measurable_space β] (hX : ae_measurable X μ) (x : β) :
cdf X μ x = μ.map X (Iic x) :=
by { rw [cdf, map_apply_of_ae_measurable hX], exact measurable_set_Iic, }

lemma tendsto_cdf_nhds_within_Iio [topological_space β] [conditionally_complete_linear_order β]
  [order_topology β] (x : β) :
  tendsto (cdf X μ) (𝓝[<] x) (𝓝 $ Sup (cdf X μ '' Iio x)) :=
monotone.tendsto_nhds_within_Iio (monotone_cdf X μ) x

lemma tendsto_nhds_within_iff {α ι} [topological_space α] {l : filter ι}
  (x : ι → α) (s : set α) (a : α) :
  tendsto x l (𝓝[s] a) ↔ tendsto x l (𝓝 a) ∧ ∀ᶠ n in l, x n ∈ s :=
⟨λ h, ⟨tendsto_nhds_of_tendsto_nhds_within h, eventually_mem_of_tendsto_nhds_within h⟩,
  λ h, tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ h.1 h.2⟩

lemma tendsto_nhds_within_iff_seq_tendsto [topological_space α]
  {f : α → β} {x : α} {l : filter β} {s : set α} [(𝓝[s] x).is_countably_generated] (hx : x ∈ s) :
  tendsto f (𝓝[s] x) l
    ↔ (∀ xs : ℕ → α, (∀ n, xs n ∈ s) → tendsto xs at_top (𝓝 x) → tendsto (f ∘ xs) at_top l) :=
begin
  rw tendsto_iff_seq_tendsto,
  simp_rw tendsto_nhds_within_iff,
  refine ⟨λ h xs hxs_ge h_tendsto, h xs ⟨h_tendsto, eventually_of_forall hxs_ge⟩,
    λ h xs h_tendsto, _⟩,
  classical,
  let ys : ℕ → α := λ n, if xs n ∈ s then xs n else x,
  have hys_eq_xs : ys =ᶠ[at_top] xs,
  { filter_upwards [h_tendsto.2] with n hxsn_mem,
    simp_rw [ys, if_pos hxsn_mem], },
  refine (tendsto_congr' _).mp (h ys _ _),
  { filter_upwards [hys_eq_xs] with n hn,
    rw [function.comp_apply, hn], },
  { intros n,
    simp_rw ys,
    split_ifs with h' h',
    exacts [h', hx], },
  { rw tendsto_congr' hys_eq_xs,
    exact h_tendsto.1, },
end

lemma tendsto_nhds_iff_monotone_tendsto [topological_space α] [linear_order α] [order_topology α]
  {f : α → β} {x : α} {l : filter β} [(𝓝 x).is_countably_generated] :
  tendsto f (𝓝 x) l
    ↔ ((∀ xs : ℕ → α, antitone xs → tendsto xs at_top (𝓝 x) → tendsto (f ∘ xs) at_top l)
      ∧ (∀ xs : ℕ → α, monotone xs → tendsto xs at_top (𝓝 x) → tendsto (f ∘ xs) at_top l)) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw tendsto_iff_seq_tendsto at h,
    exact ⟨λ xs _ h_tendsto, h xs h_tendsto, λ xs _ h_tendsto, h xs h_tendsto⟩, },
  refine tendsto_of_subseq_tendsto (λ xs hxs_tendsto, _),
  sorry,
end

lemma tendsto_nhds_Ici_iff_seq_tendsto [topological_space α] [linear_order α] [order_topology α]
  {f : α → β} {x : α} {l : filter β}
  [(𝓝[≥] x).is_countably_generated] :
  tendsto f (𝓝[≥] x) l
    ↔ (∀ xs : ℕ → α, (∀ n, x ≤ xs n) → antitone xs → tendsto xs at_top (𝓝 x)
      → tendsto (f ∘ xs) at_top l) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw tendsto_nhds_within_iff_seq_tendsto at h,
    swap, { exact le_rfl, },
    exact λ xs h_mem h_anti h_tendsto, h xs h_mem h_tendsto, },
  refine tendsto_of_subseq_tendsto (λ xs hxs_tendsto, _),
  rw tendsto_nhds_within_iff at hxs_tendsto,
  cases hxs_tendsto with hxs_tendsto hxs_mem,
  obtain ⟨ns, hxns_anti, hxns_tendsto⟩ :
    ∃ ns : ℕ → ℕ, antitone (xs ∘ ns) ∧ tendsto (xs ∘ ns) at_top (𝓝 x),
  { sorry, },
  exact ⟨ns, h (xs ∘ ns) sorry hxns_anti hxns_tendsto⟩,
end

lemma cdf_continuous_within_at_Ici [topological_space β] [conditionally_complete_linear_order β]
  [order_topology β] {mβ : measurable_space β} [opens_measurable_space β] [is_finite_measure μ]
  (x : β) [(𝓝[≥] x).is_countably_generated] (hX : measurable X) :
  continuous_within_at (cdf X μ) (Ici x) x :=
begin
  refine tendsto_nhds_Ici_iff_seq_tendsto.mpr (λ xs h_ge h_anti h_tendsto, _),
  simp_rw cdf,
  have h_eq_infi : X ⁻¹' Iic x = ⋂ n, X ⁻¹' Iic (xs n),
  { ext1 y,
    simp only [mem_preimage, mem_Iic, mem_Inter],
    refine ⟨λ h_le i, h_le.trans (h_ge i), λ h, _⟩,
    rw ← le_cinfi_iff at h,
    { refine h.trans_eq _,
      refine cinfi_eq_of_forall_ge_of_forall_gt_exists_lt h_ge (λ y hx_lt_y, _),
      exact eventually.exists (eventually_lt_of_tendsto_lt hx_lt_y h_tendsto), },
    { refine ⟨x, λ y hy, _⟩,
      obtain ⟨n, rfl⟩ := hy,
      exact h_ge n, }, },
  rw h_eq_infi,
  have h_anti_set : antitone (λ n, X ⁻¹' Iic (xs n)),
  { intros i j hij a ha,
    simp only [mem_preimage, mem_Iic] at ha ⊢,
    refine ha.trans (h_anti hij), },
  exact tendsto_measure_Inter (λ n, hX measurable_set_Iic) h_anti_set ⟨0, measure_ne_top _ _⟩,
end

lemma strict_anti_subseq_of_tendsto_at_bot {β : Type*} [linear_order β] [no_min_order β]
  {u : ℕ → β} (hu : tendsto u at_top at_bot) :
  ∃ φ : ℕ → ℕ, strict_mono φ ∧ strict_anti (u ∘ φ) :=
let ⟨φ, h, h'⟩ := extraction_of_frequently_at_top (frequently_low_scores hu) in
⟨φ, h, λ n m hnm, h' m _ (h hnm)⟩

lemma tendsto_at_bot_iff_seq_tendsto [linear_order α] [no_min_order α]
  [(at_bot : filter α).is_countably_generated] {f : α → β} {l : filter β} :
  tendsto f at_bot l
    ↔ ∀ x : ℕ → α, strict_anti x → tendsto x at_top at_bot → tendsto (f ∘ x) at_top l :=
begin
  refine ⟨λ h x h_anti hx, h.comp hx, λ H, _⟩,
  refine tendsto_of_subseq_tendsto (λ x hx_tendsto, _),
  obtain ⟨ns, hxns_anti, hxns_tendsto⟩ :
    ∃ ns : ℕ → ℕ, strict_anti (x ∘ ns) ∧ tendsto (x ∘ ns) at_top at_bot,
  { obtain ⟨ns, hns_strict_mono, hns_comp_anti⟩ := strict_anti_subseq_of_tendsto_at_bot hx_tendsto,
    exact ⟨ns, hns_comp_anti, hx_tendsto.comp (strict_mono.tendsto_at_top hns_strict_mono)⟩, },
  exact ⟨ns, H (x ∘ ns) hxns_anti hxns_tendsto⟩,
end

lemma tendsto_cdf_at_bot [topological_space β] [conditionally_complete_linear_order β]
  [order_topology β] {mβ : measurable_space β} [opens_measurable_space β] [is_finite_measure μ]
  (hX : measurable X) [(at_bot : filter β).is_countably_generated] [no_min_order β] :
  tendsto (cdf X μ) at_bot (𝓝 0) :=
begin
  rw tendsto_at_bot_iff_seq_tendsto,
  intros x hx_anti hx_tendsto,
  have h_anti : antitone (λ n, X ⁻¹' Iic (x n)),
  { change antitone ((λ y, X ⁻¹' Iic y) ∘ x),
    refine monotone.comp_antitone _ hx_anti.antitone,
    intros i j hij b,
    simp only [mem_preimage, mem_Iic],
    exact λ h, h.trans hij, },
  have h_tendsto : tendsto (cdf X μ ∘ x) at_top (𝓝 (μ (⋂ n, X ⁻¹' Iic (x n)))),
    from tendsto_measure_Inter (λ n, hX measurable_set_Iic) h_anti ⟨0, measure_ne_top _ _⟩,
  convert h_tendsto,
  rw ← @measure_empty _ _ μ,
  congr,
  ext1 a,
  simp only [mem_empty_iff_false, mem_Inter, mem_preimage, mem_Iic, false_iff, not_forall, not_le],
  obtain ⟨n, -, hn⟩ := exists_lt_of_tendsto_at_bot hx_tendsto 0 (X a),
  exact ⟨n, hn⟩,
end


end cdf

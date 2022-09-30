/-
Copyright (c) 2022 Yaël Dillies, Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kexing Ying
-/
import data.set.intervals.ord_connected
import measure_theory.covering.differentiation
import measure_theory.measure.lebesgue
import measure_theory.covering.besicovitch_vector_space
import order.upper_lower

/-!
# Order-connected sets are null-measurable

This file proves that order-connected sets in `ℝⁿ` under the pointwise order are measurable.

## Main declarations

* `is_upper_set.null_frontier`/`is_lower_set.null_frontier`
-/

namespace tactic
open positivity

private lemma ennreal_of_real_pos {r : ℝ} : 0 < r → 0 < ennreal.of_real r := ennreal.of_real_pos.2

/-- Extension for the `positivity` tactic: `ennreal.of_real` is positive if its input is. -/
@[positivity]
meta def positivity_ennreal_of_real : expr → tactic strictness
| `(ennreal.of_real %%r) := do
    positive p ← core r,
    positive <$> mk_app ``ennreal_of_real_pos [p]
| e := pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `ennreal.of_real r`"

end tactic

namespace ennreal
open_locale ennreal

variables {a b c : ℝ≥0∞}

protected lemma div_le_div_left (h : a ≤ b) (c : ℝ≥0∞) : c / b ≤ c / a :=
ennreal.div_le_div le_rfl h

protected lemma div_le_div_right (h : a ≤ b) (c : ℝ≥0∞) : a / c ≤ b / c :=
ennreal.div_le_div h le_rfl

end ennreal

section
variables {α : Type*} {r r' : α → α → Prop}

lemma directed_on.mono' {s : set α} (hs : directed_on r s)
  (h : ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → r a b → r' a b) :
  directed_on r' s :=
λ x hx y hy, let ⟨z, hz, hxz, hyz⟩ := hs _ hx _ hy in ⟨z, hz, h hx hz hxz, h hy hz hyz⟩

end

section
variables {α β : Type*} [preorder α] {f : α → β}

open set

/-- An antitone function on an inf-semilattice is directed. -/
lemma directed_on_of_inf {r : β → β → Prop} {s : set α} (hs : directed_on (≤) s)
  (hf : ∀ ⦃a₁⦄, a₁ ∈ s → ∀ ⦃a₂⦄, a₂ ∈ s → a₁ ≤ a₂ → r (f a₁) (f a₂)) : directed_on r (f '' s) :=
directed_on_image.2 $ hs.mono' hf

end

section
variables {α β : Type*} [semilattice_sup α] [preorder β] {f : α → β} {s : set α}

-- lemma monotone_on.directed_ge (hf : monotone_on f s) : directed_on (≥) f := directed_of_inf hf

end

section
variables {α β : Type*} [semilattice_inf α] [preorder β] {f : α → β} {s : set α}

lemma monotone.directed_ge (hf : monotone f) : directed (≥) f := directed_of_inf hf

-- lemma monotone_on.directed_on_ge (hf : monotone_on f s) : directed_on (≥) s f :=
-- directed_of_inf hf

end

namespace emetric
variables {α β : Type*} [pseudo_emetric_space α] [pseudo_emetric_space β] {f : α → β} {s t : set α}
  {x : α}

open filter set
open_locale topological_space ennreal

lemma nhds_within_basis_ball : (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_eball s

lemma nhds_within_basis_closed_ball :
  (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, closed_ball x ε ∩ s) :=
nhds_within_has_basis nhds_basis_closed_eball s

lemma mem_nhds_within_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
nhds_within_basis_ball.mem_iff

lemma tendsto_nhds_within_nhds_within {t : set β} {a b} :
  tendsto f (𝓝[s] a) (𝓝[t] b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
(nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans $
  forall₂_congr $ λ ε hε, exists₂_congr $ λ δ hδ,
  forall_congr $ λ x, by simp; itauto

lemma tendsto_nhds_within_nhds {a b} :
  tendsto f (𝓝[s] a) (𝓝 b) ↔
    ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
by { rw [← nhds_within_univ b, tendsto_nhds_within_nhds_within], simp only [mem_univ, true_and] }

lemma tendsto_nhds_nhds {a b} :
  tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
nhds_basis_eball.tendsto_iff nhds_basis_eball

end emetric

namespace ennreal
open_locale ennreal
variables {s : set ℝ≥0∞} {x : ℝ≥0∞}

open filter set
open_locale topological_space ennreal

-- lemma nhds_basis_Icc (hx : x ≠ ⊤) :
--   (𝓝 x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, Icc (x - ε) (x + ε)) :=
-- begin
--   rw nhds_of_ne_top hx,
--   refine has_basis_binfi_principal _ ⟨∞, with_top.coe_lt_top _⟩,
--   sorry
-- end

-- lemma nhds_within_basis_ball : (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, Icc x ε ∩ s) :=
-- nhds_within_has_basis (nhds_basis_Icc _) s

-- lemma nhds_within_basis_closed_ball :
--   (𝓝[s] x).has_basis (λ ε : ℝ≥0∞, 0 < ε) (λ ε, closed_ball x ε ∩ s) :=
-- nhds_within_has_basis nhds_basis_closed_eball s

-- lemma mem_nhds_within_iff : s ∈ 𝓝[t] x ↔ ∃ ε > 0, ball x ε ∩ t ⊆ s :=
-- nhds_within_basis_ball.mem_iff

-- lemma tendsto_nhds_within_nhds_within {t : set β} {a b} :
--   tendsto f (𝓝[s] a) (𝓝[t] b) ↔
--     ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, x ∈ s → edist x a < δ → f x ∈ t ∧ edist (f x) b < ε :=
-- (nhds_within_basis_ball.tendsto_iff nhds_within_basis_ball).trans $
--   forall₂_congr $ λ ε hε, exists₂_congr $ λ δ hδ,
--   forall_congr $ λ x, by simp; itauto

-- lemma tendsto_nhds_within_nhds {a b} :
--   tendsto f (𝓝[s] a) (𝓝 b) ↔
--     ∀ ε > 0, ∃ δ > 0, ∀{x:α}, x ∈ s → edist x a < δ → edist (f x) b < ε :=
-- by { rw [← nhds_within_univ b, tendsto_nhds_within_nhds_within], simp only [mem_univ, true_and] }

-- lemma tendsto_nhds_nhds {a b} :
--   tendsto f (𝓝 a) (𝓝 b) ↔ ∀ ε > 0, ∃ δ > 0, ∀ ⦃x⦄, edist x a < δ → edist (f x) b < ε :=
-- nhds_basis_eball.tendsto_iff nhds_basis_eball

end ennreal

section
variables {ι α : Type*} [fintype ι] [pseudo_emetric_space α]

lemma edist_pi_const_le (a b : α) : edist (λ _ : ι, a) (λ _, b) ≤ edist a b :=
edist_pi_le_iff.2 $ λ _, le_rfl

end

section
variables {ι α : Type*} [fintype ι] [pseudo_metric_space α]

lemma dist_pi_const_le (a b : α) : dist (λ _ : ι, a) (λ _, b) ≤ dist a b :=
(dist_pi_le_iff dist_nonneg).2 $ λ _, le_rfl

lemma nndist_pi_const_le (a b : α) : nndist (λ _ : ι, a) (λ _, b) ≤ nndist a b :=
nndist_pi_le_iff.2 $ λ _, le_rfl

end

section
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β] [Π b, pseudo_metric_space (π b)]
  {f g : Π b, π b} {r : ℝ}

lemma dist_pi_le_iff' : dist f g ≤ r ↔ ∀ b, dist (f b) (g b) ≤ r :=
begin
  by_cases hr : 0 ≤ r,
  { exact dist_pi_le_iff hr },
  { exact iff_of_false (λ h, hr $ dist_nonneg.trans h)
      (λ h, hr $ dist_nonneg.trans $ h $ classical.arbitrary _) }
end

end

section
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β] [Π b, seminormed_add_comm_group (π b)]
  {f : Π b, π b} {r : ℝ}

lemma pi_norm_le_iff' : ∥f∥ ≤ r ↔ ∀ b, ∥f b∥ ≤ r :=
begin
  by_cases hr : 0 ≤ r,
  { exact pi_norm_le_iff hr },
  { exact iff_of_false (λ h, hr $ (norm_nonneg _).trans h)
      (λ h, hr $ (norm_nonneg _).trans $ h $ classical.arbitrary _) }
end

end

section
variables {ι E : Type*} [fintype ι] [seminormed_add_comm_group E]

lemma pi_norm_const_le (a : E) : ∥(λ _ : ι, a)∥ ≤ ∥a∥ :=
(pi_norm_le_iff $ norm_nonneg _).2 $ λ _, le_rfl

end

open function measure_theory measure_theory.measure metric set

variables {ι : Type*} [fintype ι] {s : set (ι → ℝ)} {x : ι → ℝ} {δ : ℝ}

lemma is_upper_set.Ioi_subset_of_mem_closure (h : is_upper_set s) (hx : x ∈ closure s) :
  Ioi x ⊆ s :=
begin
  rintro y (hy : _ < _),
  set d := finset.univ.inf' sorry (λ i, dist (x i) $ y i),
  have hd : 0 < d := (finset.lt_inf'_iff _).2 (λ i _, sorry), -- false :(
  obtain ⟨z, hz, hxz⟩ :=  metric.mem_closure_iff.1 hx _ hd,
  refine h (λ i, _) hz,
  have := (dist_le_pi_dist _ _ i).trans_lt (hxz.trans_le $ finset.inf'_le _ $ finset.mem_univ i),
  rw [dist_eq_norm', dist_eq_norm', real.norm_eq_abs,
    real.norm_of_nonneg (sub_nonneg_of_le $ hy.le _)] at this,
  exact (sub_le_sub_iff_right _).1 (this.le.trans' $ le_abs_self _),
end

lemma is_lower_set.Iio_subset_of_mem_closure (h : is_lower_set s) (hx : x ∈ closure s) :
  Iio x ⊆ s :=
sorry

protected lemma is_upper_set.closure (h : is_upper_set s) : is_upper_set (closure s) :=
is_upper_set_iff_Ioi_subset.2 $ λ x hx, (h.Ioi_subset_of_mem_closure hx).trans subset_closure

protected lemma is_lower_set.closure (h : is_lower_set s) : is_lower_set (closure s) :=
is_lower_set_iff_Iio_subset.2 $ λ x hx, (h.Iio_subset_of_mem_closure hx).trans subset_closure

protected lemma is_upper_set.interior (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure }

protected lemma is_lower_set.interior (h : is_lower_set s) : is_lower_set (interior s) :=
by { rw [←is_upper_set_compl, ←closure_compl], exact h.compl.closure }

lemma is_upper_set.exists_subset_ball (hs : is_upper_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ s :=
begin
  refine ⟨x + const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_add_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hxy.2).trans ((_root_.sub_le.1 hz.1).trans_eq' _),
  ring,
end

lemma is_lower_set.exists_subset_ball (hs : is_lower_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ s :=
begin
  refine ⟨x - const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_sub_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (half_pos hδ),
  refine λ z hz, hs (λ i, _) hy,
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  refine (sub_le_iff_le_add.1 hz.2).trans ((_root_.sub_le.1 hxy.1).trans_eq' _),
  ring,
end

open filter topological_space
open_locale ennreal nnreal topological_space

variables {α : Type*} [topological_space α] [linear_order α]

lemma exists_seq_strict_anti_tendsto_nhds_within [densely_ordered α] [no_max_order α]
  [first_countable_topology α] (x : α) :
  ∃ u : ℕ → α, strict_anti u ∧ (∀ n, x < u n) ∧ tendsto u at_top (𝓝[>] x) :=
sorry

private lemma aux₀
  (h : ∀ δ, 0 < δ → ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ s) :
  ¬ tendsto (λ r, volume (closure s ∩ closed_ball x r) / volume (closed_ball x r)) (𝓝[>] 0)
    (𝓝 0) :=
begin
  choose f hf₀ hf₁ using h,
  intros H,
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strict_anti_tendsto_nhds_within (0 : ℝ),
  refine not_eventually.2 (frequently_of_forall $ λ _, lt_irrefl $
    ennreal.of_real $ 4⁻¹ ^ fintype.card ι)
   ((tendsto.eventually_lt (H.comp hε₀) tendsto_const_nhds _).mono $ λ n, lt_of_le_of_lt _),
  swap,
  refine (ennreal.div_le_div_right (volume.mono $ subset_inter
    ((hf₁ _ $ hε' n).trans subset_closure) $ hf₀ _ $ hε' n) _).trans_eq' _,
  dsimp,
  have := hε' n,
  rw [real.volume_pi_closed_ball, real.volume_pi_closed_ball, ←ennreal.of_real_div_of_pos, ←div_pow,
    mul_div_mul_left _ _ (@two_ne_zero ℝ _ _), div_right_comm, div_self, one_div],
  exact this.ne',
  all_goals { positivity },
end

private lemma aux₁
  (h : ∀ δ, 0 < δ → ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ sᶜ) :
  ¬ tendsto (λ r, volume (closure s ∩ closed_ball x r) / volume (closed_ball x r)) (𝓝[>] 0)
    (𝓝 1) :=
begin
  choose f hf₀ hf₁ using h,
  intros H,
  obtain ⟨ε, hε, hε', hε₀⟩ := exists_seq_strict_anti_tendsto_nhds_within (0 : ℝ),
  refine not_eventually.2 (frequently_of_forall $ λ _, lt_irrefl $
    ennreal.of_real $ 1 - 4⁻¹ ^ fintype.card ι)
   ((tendsto.eventually_lt tendsto_const_nhds (H.comp hε₀) _).mono $ λ n, lt_of_le_of_lt' _),
  swap,
  refine (ennreal.div_le_div_right (volume.mono $ _) _).trans_eq _,
  exact closed_ball x (ε n) \ closed_ball (f (ε n) $ hε' n) (ε n / 4),
  rotate,
  dsimp,
  have := hε' n,
  sorry,
  sorry,
  sorry,
  -- rw [volume_diff, real.volume_pi_closed_ball, real.volume_pi_closed_ball,
  --   ←ennreal.of_real_div_of_pos, ←div_pow, mul_div_mul_left _ _ (@two_ne_zero ℝ _ _),
  --   div_right_comm, div_self, one_div],
  -- exact this.ne',
  -- all_goals { positivity },
end

lemma is_upper_set.null_frontier (hs : is_upper_set s) : volume (frontier s) = 0 :=
begin
  refine eq_bot_mono (volume.mono $ λ x hx, _)
    (besicovitch.ae_tendsto_measure_inter_div_of_measurable_set _ is_closed_closure.measurable_set),
  { exact s },
  by_cases x ∈ closure s; simp [h],
  { exact aux₁ (λ _, hs.compl.exists_subset_ball $ frontier_subset_closure $
      by rwa frontier_compl) },
  { exact aux₀ (λ _, hs.exists_subset_ball $ frontier_subset_closure hx) }
end

lemma is_lower_set.null_frontier (hs : is_lower_set s) : volume (frontier s) = 0 :=
begin
  refine eq_bot_mono (volume.mono $ λ x hx, _)
    (besicovitch.ae_tendsto_measure_inter_div_of_measurable_set _ is_closed_closure.measurable_set),
  { exact s },
  by_cases x ∈ closure s; simp [h],
  { exact aux₁ (λ _, hs.compl.exists_subset_ball $ frontier_subset_closure $
      by rwa frontier_compl) },
  { exact aux₀ (λ _, hs.exists_subset_ball $ frontier_subset_closure hx) }
end

lemma set.ord_connected.null_frontier (hs : s.ord_connected) : volume (frontier s) = 0 :=
begin
  rw ← hs.upper_closure_inter_lower_closure,
  refine le_bot_iff.1 ((volume.mono $ (frontier_inter_subset _ _).trans $ union_subset_union
    (inter_subset_left _ _) $ inter_subset_right _ _).trans $ (measure_union_le _ _).trans_eq _),
  rw [(upper_set.upper _).null_frontier, (lower_set.lower _).null_frontier, zero_add, bot_eq_zero],
end

lemma set.ord_connected.null_measurable_set (hs : s.ord_connected) : null_measurable_set s :=
null_measurable_set_of_null_frontier hs.null_frontier

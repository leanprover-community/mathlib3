/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.upper_lower
import analysis.normed.field.basic

/-!
# Topological facts about upper/lower/order-connected sets

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/
-- move `real.norm_of_nonneg`

section
variables {α : Type*} [topological_space α] [linear_order α]

open filter set topological_space
open_locale topological_space

lemma exists_seq_strict_anti_tendsto_nhds_within [order_topology α] [densely_ordered α]
  [no_max_order α] [first_countable_topology α] (x : α) :
  ∃ u : ℕ → α, strict_anti u ∧ (∀ n, x < u n) ∧ tendsto u at_top (𝓝[>] x) :=
let ⟨u, hu, hx, h⟩ := exists_seq_strict_anti_tendsto x in ⟨u, hu, hx,
  tendsto_nhds_within_mono_right (range_subset_iff.2 hx) $ tendsto_nhds_within_range.2 h⟩

end

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

protected lemma sub_div (h : 0 < b → b < a → c ≠ 0) : (a - b) / c = a / c - b / c :=
by { simp_rw div_eq_mul_inv, exact ennreal.sub_mul (by simpa using h) }

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
variables {β : Type*} {π : β → Type*} [nonempty β] [fintype β]
  [Π b, seminormed_add_comm_group (π b)] {f : Π b, π b} {r : ℝ}

lemma pi_norm_le_iff'' : ∥f∥ ≤ r ↔ ∀ b, ∥f b∥ ≤ r :=
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

section
variables {α β : Type*}

@[to_additive] instance order_dual.has_smul' [h : has_smul α β] : has_smul αᵒᵈ β := h
@[to_additive order_dual.has_smul']
instance order_dual.has_pow' [h : has_pow α β] : has_pow α βᵒᵈ := h

instance [topological_space β] [has_vadd α β] [has_continuous_const_vadd α β] :
  has_continuous_const_vadd α βᵒᵈ :=
‹has_continuous_const_vadd α β›

@[to_additive] instance [topological_space β] [has_smul α β] [has_continuous_const_smul α β] :
  has_continuous_const_smul α βᵒᵈ :=
‹has_continuous_const_smul α β›

@[to_additive] instance order_dual.has_continuous_const_smul' [topological_space β] [has_smul α β]
  [has_continuous_const_smul α β] :
  has_continuous_const_smul αᵒᵈ β :=
‹has_continuous_const_smul α β›

end

open function  metric set
open_locale pointwise

variables {α ι : Type*}

section
variables [topological_space α] [ordered_comm_group α] [has_continuous_const_smul α α]
  {s : set α}

@[to_additive is_upper_set.closure]
protected lemma is_upper_set.closure' (h : is_upper_set s) : is_upper_set (closure s) :=
λ x y hxy hx, closure_mono (h.smul_subset $ one_le_div'.2 hxy) $
  by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ }

@[to_additive is_lower_set.closure]
protected lemma is_lower_set.closure' (h : is_lower_set s) : is_lower_set (closure s) :=
h.of_dual.closure'

/-
Note: ` s.ord_connected` does not imply `(closure s).ord_connected`, as we can see by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/

@[to_additive is_upper_set.interior]
protected lemma is_upper_set.interior' (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure' }

@[to_additive is_lower_set.interior]
protected lemma is_lower_set.interior' (h : is_lower_set s) : is_lower_set (interior s) :=
h.of_dual.interior'

@[to_additive set.ord_connected.interior]
protected lemma set.ord_connected.interior' (h : s.ord_connected) : (interior s).ord_connected :=
begin
  rw [←h.upper_closure_inter_lower_closure, interior_inter],
  exact (upper_closure s).upper.interior'.ord_connected.inter
    (lower_closure s).lower.interior'.ord_connected,
end

end

/-! ### `ℝⁿ` -/

section finite
variables [finite ι] {s : set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

lemma is_upper_set.mem_interior_of_forall_lt (hs : is_upper_set s) (hx : x ∈ closure s)
  (h : ∀ i, x i < y i) :
  y ∈ interior s :=
begin
  casesI nonempty_fintype ι,
  obtain ⟨ε, hε, hxy⟩ := pi.exists_forall_pos_add_lt h,
  obtain ⟨z, hz, hxz⟩ := metric.mem_closure_iff.1 hx _ hε,
  rw dist_pi_lt_iff hε at hxz,
  have hyz : ∀ i, z i < y i,
  { refine λ i, (hxy _).trans_le' (sub_le_iff_le_add'.1 $ (le_abs_self _).trans _),
    rw [←real.norm_eq_abs, ←dist_eq_norm'],
    exact (hxz _).le },
  obtain ⟨δ, hδ, hyz⟩ := pi.exists_forall_pos_add_lt hyz,
  refine mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩,
  rintro w hw,
  refine hs (λ i, _) hz,
  simp_rw [ball_pi _ hδ, real.ball_eq_Ioo] at hw,
  exact ((lt_sub_iff_add_lt.2 $ hyz _).trans (hw _ $ mem_univ _).1).le,
end

lemma is_lower_set.mem_interior_of_forall_lt (hs : is_lower_set s) (hx : x ∈ closure s)
  (h : ∀ i, y i < x i) :
  y ∈ interior s :=
begin
  casesI nonempty_fintype ι,
  obtain ⟨ε, hε, hxy⟩ := pi.exists_forall_pos_add_lt h,
  obtain ⟨z, hz, hxz⟩ := metric.mem_closure_iff.1 hx _ hε,
  rw dist_pi_lt_iff hε at hxz,
  have hyz : ∀ i, y i < z i,
  { refine λ i, (lt_sub_iff_add_lt.2 $ hxy _).trans_le (_root_.sub_le.1 $ (le_abs_self _).trans _),
    rw [←real.norm_eq_abs, ←dist_eq_norm],
    exact (hxz _).le },
  obtain ⟨δ, hδ, hyz⟩ := pi.exists_forall_pos_add_lt hyz,
  refine mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩,
  rintro w hw,
  refine hs (λ i, _) hz,
  simp_rw [ball_pi _ hδ, real.ball_eq_Ioo] at hw,
  exact ((hw _ $ mem_univ _).2.trans $ hyz _).le,
end

end finite

section fintype
variables [fintype ι] {s : set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

lemma is_upper_set.exists_subset_ball (hs : is_upper_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior s :=
begin
  refine ⟨x + const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_add_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four),
  refine λ z hz, hs.mem_interior_of_forall_lt (subset_closure hy) (λ i, _),
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  linarith,
end

lemma is_lower_set.exists_subset_ball (hs : is_lower_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior s :=
begin
  refine ⟨x - const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_sub_left,
    refine (add_le_add_left (pi_norm_const_le _) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four),
  refine λ z hz, hs.mem_interior_of_forall_lt (subset_closure hy) (λ i, _),
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  linarith,
end

end fintype

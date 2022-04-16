/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import topology.continuous_function.bounded

/-!
# Thickenings and thickened indicators

## Main definitions

## Main results

-/
noncomputable theory
open_locale classical nnreal ennreal topological_space bounded_continuous_function

section thickened_indicator

variables {α : Type*} [pseudo_emetric_space α]

def thickened_indicator' (δ : ℝ) (E : set α) : α → ℝ≥0∞ :=
λ (x : α), (1 : ℝ≥0∞) - (inf_edist x E) / (ennreal.of_real δ)

lemma thickened_indicator'_empty {δ : ℝ} (δ_pos : 0 < δ) :
  thickened_indicator' δ (∅ : set α) = 0 :=
begin
  rw thickened_indicator',
  simp_rw [inf_edist_empty, top_div],
  have := top_div,
  sorry,
end

example : has_continuous_div ℝ≥0∞ :=
sorry --by library_search!

example : has_continuous_mul ℝ≥0∞ :=
sorry --by library_search!

#check ennreal.continuous_at_const_mul

lemma continuous_thickened_indicator' {δ : ℝ} (δ_pos : 0 < δ) (E : set α) :
  continuous (thickened_indicator' δ E) :=
begin
  unfold thickened_indicator',
  let f := λ (x : α), (⟨1, (inf_edist x E) / (ennreal.of_real δ)⟩ : ℝ≥0 × ℝ≥0∞),
  let sub := λ (p : ℝ≥0 × ℝ≥0∞), ((p.1 : ℝ≥0∞) - p.2),
  rw (show (λ (x : α), ((1 : ℝ≥0∞)) - (inf_edist x E) / (ennreal.of_real δ)) = sub ∘ f, by refl),
  apply continuous.comp (@ennreal.continuous_nnreal_sub 1),
  apply (ennreal.continuous_at_div_const (ennreal.of_real δ) _).comp continuous_inf_edist,
  norm_num [δ_pos],
end

lemma thickened_indicator'_le_one (δ : ℝ) (E : set α) (x : α) :
  thickened_indicator' δ E x ≤ 1 :=
by apply @tsub_le_self _ _ _ _ (1 : ℝ≥0∞)

lemma thickened_indicator'_lt_top {δ : ℝ} {E : set α} {x : α} :
  thickened_indicator' δ E x < ∞ :=
lt_of_le_of_lt (thickened_indicator'_le_one _ _ _) one_lt_top

lemma thickened_indicator'_one (δ : ℝ) (E : set α) {x : α} (x_in_E : x ∈ E) :
  thickened_indicator' δ E x = 1 :=
by simp [thickened_indicator', inf_edist_zero_of_mem x_in_E, tsub_zero]

lemma thickened_indicator'_zero {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_out : x ∉ thickening δ E) :
  thickened_indicator' δ E x = 0 :=
begin
  rw [thickening, mem_set_of_eq, not_lt] at x_out,
  unfold thickened_indicator',
  apply le_antisymm _ bot_le,
  have key := tsub_le_tsub (@rfl _ (1 : ℝ≥0∞)).le (ennreal.div_le_div x_out rfl.le),
  rw [ennreal.div_self (ne_of_gt (ennreal.of_real_pos.mpr δ_pos)) of_real_ne_top] at key,
  simpa using key,
end

lemma thickened_indicator'_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : set α) :
  thickened_indicator' δ₁ E ≤ thickened_indicator' δ₂ E :=
begin
  intro x,
  apply tsub_le_tsub (@rfl ℝ≥0∞ 1).le,
  exact ennreal.div_le_div rfl.le (of_real_le_of_real hle),
end

lemma thickened_indicator'_subset (δ : ℝ) {E₁ E₂ : set α} (subset : E₁ ⊆ E₂) :
  thickened_indicator' δ E₁ ≤ thickened_indicator' δ E₂ :=
begin
  intro x,
  apply tsub_le_tsub (@rfl ℝ≥0∞ 1).le,
  exact ennreal.div_le_div (inf_edist_le_inf_edist_of_subset subset) rfl.le,
end

@[simps] def thickened_indicator {δ : ℝ} (δ_pos : 0 < δ) (E : set α) : α →ᵇ ℝ≥0 :=
{ to_fun := λ (x : α), (thickened_indicator' δ E x).to_nnreal,
  continuous_to_fun := begin
    apply continuous_on.comp_continuous
            continuous_on_to_nnreal (continuous_thickened_indicator' δ_pos E),
    intro x,
    rw mem_set_of_eq,
    apply ne_of_lt,
    exact lt_of_le_of_lt (@thickened_indicator'_le_one _ _ δ E x) one_lt_top,
  end,
  map_bounded' := begin
    use 2,
    intros x y,
    rw [nnreal.dist_eq],
    apply (abs_sub _ _).trans,
    rw [nnreal.abs_eq, nnreal.abs_eq, ←one_add_one_eq_two],
    have key := @thickened_indicator'_le_one _ _ δ E,
    apply add_le_add;
    { norm_cast,
      refine (to_nnreal_le_to_nnreal ((lt_of_le_of_lt (key _) one_lt_top).ne) one_ne_top).mpr
             (key _), },
  end, }

lemma thickened_indicator.coe_fn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : set α) :
  ⇑(thickened_indicator δ_pos E) = ennreal.to_nnreal ∘ thickened_indicator' δ E := rfl

lemma thickened_indicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : set α) (x : α) :
  thickened_indicator δ_pos E x ≤ 1 :=
begin
  rw [thickened_indicator.coe_fn_eq_comp],
  simpa using (to_nnreal_le_to_nnreal thickened_indicator'_lt_top.ne one_ne_top).mpr
    (thickened_indicator'_le_one δ E x),
end

lemma thickened_indicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_in_E : x ∈ E) :
  thickened_indicator δ_pos E x = 1 :=
by rw [thickened_indicator_apply, thickened_indicator'_one δ E x_in_E, one_to_nnreal]

lemma thickened_indicator_zero {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_out : x ∉ thickening δ E) :
  thickened_indicator δ_pos E x = 0 :=
by rw [thickened_indicator_apply, thickened_indicator'_zero δ_pos E x_out, zero_to_nnreal]

lemma thickened_indicator_mono {δ₁ δ₂ : ℝ}
  (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂) (E : set α) :
  ⇑(thickened_indicator δ₁_pos E) ≤ thickened_indicator δ₂_pos E :=
begin
  intro x,
  apply (to_nnreal_le_to_nnreal thickened_indicator'_lt_top.ne thickened_indicator'_lt_top.ne).mpr,
  apply thickened_indicator'_mono hle,
end

lemma thickened_indicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : set α} (subset : E₁ ⊆ E₂) :
  ⇑(thickened_indicator δ_pos E₁) ≤ thickened_indicator δ_pos E₂ :=
begin
  intro x,
  exact (to_nnreal_le_to_nnreal thickened_indicator'_lt_top.ne thickened_indicator'_lt_top.ne).mpr
        (thickened_indicator'_subset δ subset x),
end

end thickened_indicator -- section

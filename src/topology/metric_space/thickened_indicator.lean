/-
Copyright (c) 2022 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import data.real.ennreal
import topology.continuous_function.bounded
import topology.metric_space.hausdorff_distance

/-!
# Thickened indicators

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file is about thickened indicators of sets in (pseudo e)metric spaces. For a decreasing
sequence of thickening radii tending to 0, the thickened indicators of a closed set form a
decreasing pointwise converging approximation of the indicator function of the set, where the
members of the approximating sequence are nonnegative bounded continuous functions.

## Main definitions

 * `thickened_indicator_aux δ E`: The `δ`-thickened indicator of a set `E` as an
   unbundled `ℝ≥0∞`-valued function.
 * `thickened_indicator δ E`: The `δ`-thickened indicator of a set `E` as a bundled
   bounded continuous `ℝ≥0`-valued function.

## Main results

 * For a sequence of thickening radii tending to 0, the `δ`-thickened indicators of a set `E` tend
   pointwise to the indicator of `closure E`.
   - `thickened_indicator_aux_tendsto_indicator_closure`: The version is for the
     unbundled `ℝ≥0∞`-valued functions.
   - `thickened_indicator_tendsto_indicator_closure`: The version is for the bundled `ℝ≥0`-valued
     bounded continuous functions.

-/
noncomputable theory
open_locale classical nnreal ennreal topology bounded_continuous_function

open nnreal ennreal set metric emetric filter

section thickened_indicator

variables {α : Type*} [pseudo_emetric_space α]

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator_aux` is the unbundled `ℝ≥0∞`-valued function. See `thickened_indicator`
for the (bundled) bounded continuous function with `ℝ≥0`-values. -/
def thickened_indicator_aux (δ : ℝ) (E : set α) : α → ℝ≥0∞ :=
λ (x : α), (1 : ℝ≥0∞) - (inf_edist x E) / (ennreal.of_real δ)

lemma continuous_thickened_indicator_aux {δ : ℝ} (δ_pos : 0 < δ) (E : set α) :
  continuous (thickened_indicator_aux δ E) :=
begin
  unfold thickened_indicator_aux,
  let f := λ (x : α), (⟨1, (inf_edist x E) / (ennreal.of_real δ)⟩ : ℝ≥0 × ℝ≥0∞),
  let sub := λ (p : ℝ≥0 × ℝ≥0∞), ((p.1 : ℝ≥0∞) - p.2),
  rw (show (λ (x : α), ((1 : ℝ≥0∞)) - (inf_edist x E) / (ennreal.of_real δ)) = sub ∘ f, by refl),
  apply (@ennreal.continuous_nnreal_sub 1).comp,
  apply (ennreal.continuous_div_const (ennreal.of_real δ) _).comp continuous_inf_edist,
  norm_num [δ_pos],
end

lemma thickened_indicator_aux_le_one (δ : ℝ) (E : set α) (x : α) :
  thickened_indicator_aux δ E x ≤ 1 :=
by apply @tsub_le_self _ _ _ _ (1 : ℝ≥0∞)

lemma thickened_indicator_aux_lt_top {δ : ℝ} {E : set α} {x : α} :
  thickened_indicator_aux δ E x < ∞ :=
lt_of_le_of_lt (thickened_indicator_aux_le_one _ _ _) one_lt_top

lemma thickened_indicator_aux_closure_eq (δ : ℝ) (E : set α) :
  thickened_indicator_aux δ (closure E) = thickened_indicator_aux δ E :=
by simp_rw [thickened_indicator_aux, inf_edist_closure]

lemma thickened_indicator_aux_one (δ : ℝ) (E : set α) {x : α} (x_in_E : x ∈ E) :
  thickened_indicator_aux δ E x = 1 :=
by simp [thickened_indicator_aux, inf_edist_zero_of_mem x_in_E, tsub_zero]

lemma thickened_indicator_aux_one_of_mem_closure
  (δ : ℝ) (E : set α) {x : α} (x_mem : x ∈ closure E) :
  thickened_indicator_aux δ E x = 1 :=
by rw [←thickened_indicator_aux_closure_eq, thickened_indicator_aux_one δ (closure E) x_mem]

lemma thickened_indicator_aux_zero
  {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_out : x ∉ thickening δ E) :
  thickened_indicator_aux δ E x = 0 :=
begin
  rw [thickening, mem_set_of_eq, not_lt] at x_out,
  unfold thickened_indicator_aux,
  apply le_antisymm _ bot_le,
  have key := tsub_le_tsub (@rfl _ (1 : ℝ≥0∞)).le (ennreal.div_le_div x_out rfl.le),
  rw [ennreal.div_self (ne_of_gt (ennreal.of_real_pos.mpr δ_pos)) of_real_ne_top] at key,
  simpa using key,
end

lemma thickened_indicator_aux_mono {δ₁ δ₂ : ℝ} (hle : δ₁ ≤ δ₂) (E : set α) :
  thickened_indicator_aux δ₁ E ≤ thickened_indicator_aux δ₂ E :=
λ _, tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ennreal.div_le_div rfl.le (of_real_le_of_real hle))

lemma indicator_le_thickened_indicator_aux (δ : ℝ) (E : set α) :
  E.indicator (λ _, (1 : ℝ≥0∞)) ≤ thickened_indicator_aux δ E :=
begin
  intro a,
  by_cases a ∈ E,
  { simp only [h, indicator_of_mem, thickened_indicator_aux_one δ E h, le_refl], },
  { simp only [h, indicator_of_not_mem, not_false_iff, zero_le], },
end

lemma thickened_indicator_aux_subset (δ : ℝ) {E₁ E₂ : set α} (subset : E₁ ⊆ E₂) :
  thickened_indicator_aux δ E₁ ≤ thickened_indicator_aux δ E₂ :=
λ _, tsub_le_tsub (@rfl ℝ≥0∞ 1).le (ennreal.div_le_div (inf_edist_anti subset) rfl.le)

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise (i.e., w.r.t. the product topology on `α → ℝ≥0∞`) to the indicator function of the
closure of E.

This statement is for the unbundled `ℝ≥0∞`-valued functions `thickened_indicator_aux δ E`, see
`thickened_indicator_tendsto_indicator_closure` for the version for bundled `ℝ≥0`-valued
bounded continuous functions. -/
lemma thickened_indicator_aux_tendsto_indicator_closure
  {δseq : ℕ → ℝ} (δseq_lim : tendsto δseq at_top (𝓝 0)) (E : set α) :
  tendsto (λ n, (thickened_indicator_aux (δseq n) E)) at_top
    (𝓝 (indicator (closure E) (λ x, (1 : ℝ≥0∞)))) :=
begin
  rw tendsto_pi_nhds,
  intro x,
  by_cases x_mem_closure : x ∈ closure E,
  { simp_rw [thickened_indicator_aux_one_of_mem_closure _ E x_mem_closure],
    rw (show (indicator (closure E) (λ _, (1 : ℝ≥0∞))) x = 1,
        by simp only [x_mem_closure, indicator_of_mem]),
    exact tendsto_const_nhds, },
  { rw (show (closure E).indicator (λ _, (1 : ℝ≥0∞)) x = 0,
        by simp only [x_mem_closure, indicator_of_not_mem, not_false_iff]),
    rcases exists_real_pos_lt_inf_edist_of_not_mem_closure x_mem_closure with ⟨ε, ⟨ε_pos, ε_lt⟩⟩,
    rw metric.tendsto_nhds at δseq_lim,
    specialize δseq_lim ε ε_pos,
    simp only [dist_zero_right, real.norm_eq_abs, eventually_at_top, ge_iff_le] at δseq_lim,
    rcases δseq_lim with ⟨N, hN⟩,
    apply @tendsto_at_top_of_eventually_const _ _ _ _ _ _ _ N,
    intros n n_large,
    have key : x ∉ thickening ε E, by simpa only [thickening, mem_set_of_eq, not_lt] using ε_lt.le,
    refine le_antisymm _ bot_le,
    apply (thickened_indicator_aux_mono (lt_of_abs_lt (hN n n_large)).le E x).trans,
    exact (thickened_indicator_aux_zero ε_pos E key).le, },
end

/-- The `δ`-thickened indicator of a set `E` is the function that equals `1` on `E`
and `0` outside a `δ`-thickening of `E` and interpolates (continuously) between
these values using `inf_edist _ E`.

`thickened_indicator` is the (bundled) bounded continuous function with `ℝ≥0`-values.
See `thickened_indicator_aux` for the unbundled `ℝ≥0∞`-valued function. -/
@[simps] def thickened_indicator {δ : ℝ} (δ_pos : 0 < δ) (E : set α) : α →ᵇ ℝ≥0 :=
{ to_fun := λ (x : α), (thickened_indicator_aux δ E x).to_nnreal,
  continuous_to_fun := begin
    apply continuous_on.comp_continuous
            continuous_on_to_nnreal (continuous_thickened_indicator_aux δ_pos E),
    intro x,
    exact (lt_of_le_of_lt (@thickened_indicator_aux_le_one _ _ δ E x) one_lt_top).ne,
  end,
  map_bounded' := begin
    use 2,
    intros x y,
    rw [nnreal.dist_eq],
    apply (abs_sub _ _).trans,
    rw [nnreal.abs_eq, nnreal.abs_eq, ←one_add_one_eq_two],
    have key := @thickened_indicator_aux_le_one _ _ δ E,
    apply add_le_add;
    { norm_cast,
      refine (to_nnreal_le_to_nnreal ((lt_of_le_of_lt (key _) one_lt_top).ne) one_ne_top).mpr
             (key _), },
  end, }

lemma thickened_indicator.coe_fn_eq_comp {δ : ℝ} (δ_pos : 0 < δ) (E : set α) :
  ⇑(thickened_indicator δ_pos E) = ennreal.to_nnreal ∘ thickened_indicator_aux δ E := rfl

lemma thickened_indicator_le_one {δ : ℝ} (δ_pos : 0 < δ) (E : set α) (x : α) :
  thickened_indicator δ_pos E x ≤ 1 :=
begin
  rw [thickened_indicator.coe_fn_eq_comp],
  simpa using (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne one_ne_top).mpr
    (thickened_indicator_aux_le_one δ E x),
end

lemma thickened_indicator_one_of_mem_closure
  {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_mem : x ∈ closure E) :
  thickened_indicator δ_pos E x = 1 :=
by rw [thickened_indicator_apply,
       thickened_indicator_aux_one_of_mem_closure δ E x_mem, one_to_nnreal]

lemma thickened_indicator_one {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_in_E : x ∈ E) :
  thickened_indicator δ_pos E x = 1 :=
thickened_indicator_one_of_mem_closure _ _ (subset_closure x_in_E)

lemma thickened_indicator_zero
  {δ : ℝ} (δ_pos : 0 < δ) (E : set α) {x : α} (x_out : x ∉ thickening δ E) :
  thickened_indicator δ_pos E x = 0 :=
by rw [thickened_indicator_apply, thickened_indicator_aux_zero δ_pos E x_out, zero_to_nnreal]

lemma indicator_le_thickened_indicator {δ : ℝ} (δ_pos : 0 < δ) (E : set α) :
  E.indicator (λ _, (1 : ℝ≥0)) ≤ thickened_indicator δ_pos E :=
begin
  intro a,
  by_cases a ∈ E,
  { simp only [h, indicator_of_mem, thickened_indicator_one δ_pos E h, le_refl], },
  { simp only [h, indicator_of_not_mem, not_false_iff, zero_le], },
end

lemma thickened_indicator_mono {δ₁ δ₂ : ℝ}
  (δ₁_pos : 0 < δ₁) (δ₂_pos : 0 < δ₂) (hle : δ₁ ≤ δ₂) (E : set α) :
  ⇑(thickened_indicator δ₁_pos E) ≤ thickened_indicator δ₂_pos E :=
begin
  intro x,
  apply (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne
         thickened_indicator_aux_lt_top.ne).mpr,
  apply thickened_indicator_aux_mono hle,
end

lemma thickened_indicator_subset {δ : ℝ} (δ_pos : 0 < δ) {E₁ E₂ : set α} (subset : E₁ ⊆ E₂) :
  ⇑(thickened_indicator δ_pos E₁) ≤ thickened_indicator δ_pos E₂ :=
λ x, (to_nnreal_le_to_nnreal thickened_indicator_aux_lt_top.ne
      thickened_indicator_aux_lt_top.ne).mpr (thickened_indicator_aux_subset δ subset x)

/-- As the thickening radius δ tends to 0, the δ-thickened indicator of a set E (in α) tends
pointwise to the indicator function of the closure of E.

Note: This version is for the bundled bounded continuous functions, but the topology is not
the topology on `α →ᵇ ℝ≥0`. Coercions to functions `α → ℝ≥0` are done first, so the topology
instance is the product topology (the topology of pointwise convergence). -/
lemma thickened_indicator_tendsto_indicator_closure
  {δseq : ℕ → ℝ} (δseq_pos : ∀ n, 0 < δseq n) (δseq_lim : tendsto δseq at_top (𝓝 0)) (E : set α) :
  tendsto (λ (n : ℕ), (coe_fn : (α →ᵇ ℝ≥0) → (α → ℝ≥0)) (thickened_indicator (δseq_pos n) E))
    at_top (𝓝 (indicator (closure E) (λ x, (1 : ℝ≥0)))) :=
begin
  have key := thickened_indicator_aux_tendsto_indicator_closure δseq_lim E,
  rw tendsto_pi_nhds at *,
  intro x,
  rw (show indicator (closure E) (λ x, (1 : ℝ≥0)) x
         = (indicator (closure E) (λ x, (1 : ℝ≥0∞)) x).to_nnreal,
      by refine (congr_fun (comp_indicator_const 1 ennreal.to_nnreal zero_to_nnreal) x).symm),
  refine tendsto.comp (tendsto_to_nnreal _) (key x),
  by_cases x_mem : x ∈ closure E; simp [x_mem],
end

end thickened_indicator -- section

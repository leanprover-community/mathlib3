/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import analysis.normed_space.operator_norm
import topology.metric_space.baire
import topology.algebra.module.basic
/-!
# The Banach-Steinhaus theorem: Uniform Boundedness Principle

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Herein we prove the Banach-Steinhaus theorem: any collection of bounded linear maps
from a Banach space into a normed space which is pointwise bounded is uniformly bounded.

## TODO

For now, we only prove the standard version by appeal to the Baire category theorem.
Much more general versions exist (in particular, for maps from barrelled spaces to locally
convex spaces), but these are not yet in `mathlib`.
-/

open set

variables
{E F 𝕜 𝕜₂ : Type*}
[seminormed_add_comm_group E] [seminormed_add_comm_group F]
[nontrivially_normed_field 𝕜] [nontrivially_normed_field 𝕜₂]
[normed_space 𝕜 E] [normed_space 𝕜₂ F]
{σ₁₂ : 𝕜 →+* 𝕜₂} [ring_hom_isometric σ₁₂]


/-- This is the standard Banach-Steinhaus theorem, or Uniform Boundedness Principle.
If a family of continuous linear maps from a Banach space into a normed space is pointwise
bounded, then the norms of these linear maps are uniformly bounded. -/
theorem banach_steinhaus {ι : Type*} [complete_space E] {g : ι → E →SL[σ₁₂] F}
  (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
  ∃ C', ∀ i, ‖g i‖ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n` -/
  let e : ℕ → set E := λ n, (⋂ i : ι, { x : E | ‖g i x‖ ≤ n }),
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n), from λ i, is_closed_Inter (λ i,
    is_closed_le (continuous.norm (g i).cont) continuous_const),
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  { refine eq_univ_of_forall (λ x, _),
    cases h x with C hC,
    obtain ⟨m, hm⟩ := exists_nat_ge C,
    exact ⟨e m, mem_range_self m, mem_Inter.mpr (λ i, le_trans (hC i) hm)⟩ },
  /- apply the Baire category theorem to conclude that for some `m : ℕ`, `e m` contains some `x` -/
  rcases nonempty_interior_of_Union_of_closed hc hU with ⟨m, x, hx⟩,
  rcases metric.is_open_iff.mp is_open_interior x hx with ⟨ε, ε_pos, hε⟩,
  obtain ⟨k, hk⟩ := normed_field.exists_one_lt_norm 𝕜,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ z : E, z ∈ metric.ball x ε → ∀ i : ι, ‖g i z‖ ≤ m,
  { intros z hz i,
    replace hz := mem_Inter.mp (interior_Inter_subset _ (hε hz)) i,
    apply interior_subset hz },
  have εk_pos : 0 < ε / ‖k‖ := div_pos ε_pos (zero_lt_one.trans hk),
  refine ⟨(m + m : ℕ) / (ε / ‖k‖), λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  { exact div_nonneg (nat.cast_nonneg _) εk_pos.le },
  intros y le_y y_lt,
  calc ‖g i y‖
      = ‖g i (y + x) - g i x‖   : by rw [continuous_linear_map.map_add, add_sub_cancel]
  ... ≤ ‖g i (y + x)‖ + ‖g i x‖ : norm_sub_le _ _
  ... ≤ m + m : add_le_add (real_norm_le (y + x) (by rwa [add_comm, add_mem_ball_iff_norm]) i)
          (real_norm_le x (metric.mem_ball_self ε_pos) i)
  ... = (m + m : ℕ) : (m.cast_add m).symm
  ... ≤ (m + m : ℕ) * (‖y‖ / (ε / ‖k‖))
      : le_mul_of_one_le_right (nat.cast_nonneg _)
          ((one_le_div $ div_pos ε_pos (zero_lt_one.trans hk)).2 le_y)
  ... = (m + m : ℕ) / (ε / ‖k‖) * ‖y‖ : (mul_comm_div _ _ _).symm,
end

open_locale ennreal
open ennreal

/-- This version of Banach-Steinhaus is stated in terms of suprema of `↑‖⬝‖₊ : ℝ≥0∞`
for convenience. -/
theorem banach_steinhaus_supr_nnnorm {ι : Type*} [complete_space E] {g : ι → E →SL[σ₁₂] F}
  (h : ∀ x, (⨆ i, ↑‖g i x‖₊) < ∞) :
  (⨆ i, ↑‖g i‖₊) < ∞ :=
begin
  have h' : ∀ x : E, ∃ C : ℝ, ∀ i : ι, ‖g i x‖ ≤ C,
  { intro x,
    rcases lt_iff_exists_coe.mp (h x) with ⟨p, hp₁, _⟩,
    refine ⟨p, (λ i, _)⟩,
    exact_mod_cast
    calc (‖g i x‖₊ : ℝ≥0∞) ≤ ⨆ j,  ‖g j x‖₊ : le_supr _ i
      ...                  = p              : hp₁ },
  cases banach_steinhaus h' with C' hC',
  refine (supr_le $ λ i, _).trans_lt (@coe_lt_top C'.to_nnreal),
  rw ←norm_to_nnreal,
  exact coe_mono (real.to_nnreal_le_to_nnreal $ hC' i),
end

open_locale topology
open filter

/-- Given a *sequence* of continuous linear maps which converges pointwise and for which the
domain is complete, the Banach-Steinhaus theorem is used to guarantee that the limit map
is a *continuous* linear map as well. -/
def continuous_linear_map_of_tendsto [complete_space E] [t2_space F]
  (g : ℕ → E →SL[σ₁₂] F) {f : E → F} (h : tendsto (λ n x, g n x) at_top (𝓝 f)) :
  E →SL[σ₁₂] F :=
{ to_fun := f,
  map_add' := (linear_map_of_tendsto _ _ h).map_add',
  map_smul' := (linear_map_of_tendsto _ _ h).map_smul',
  cont :=
    begin
      /- show that the maps are pointwise bounded and apply `banach_steinhaus`-/
      have h_point_bdd : ∀ x : E, ∃ C : ℝ, ∀ n : ℕ, ‖g n x‖ ≤ C,
      { intro x,
        rcases cauchy_seq_bdd (tendsto_pi_nhds.mp h x).cauchy_seq with ⟨C, C_pos, hC⟩,
        refine ⟨C + ‖g 0 x‖, (λ n, _)⟩,
        simp_rw dist_eq_norm at hC,
        calc ‖g n x‖ ≤ ‖g 0 x‖ + ‖g n x - g 0 x‖ : norm_le_insert' _ _
          ...        ≤ C + ‖g 0 x‖               : by linarith [hC n 0] },
      cases banach_steinhaus h_point_bdd with C' hC',
      /- show the uniform bound from `banach_steinhaus` is a norm bound of the limit map
         by allowing "an `ε` of room." -/
      refine add_monoid_hom_class.continuous_of_bound (linear_map_of_tendsto _ _ h) C'
        (λ x, le_of_forall_pos_lt_add (λ ε ε_pos, _)),
      cases metric.tendsto_at_top.mp (tendsto_pi_nhds.mp h x) ε ε_pos with n hn,
      have lt_ε : ‖g n x - f x‖ < ε, by {rw ←dist_eq_norm, exact hn n (le_refl n)},
      calc ‖f x‖ ≤ ‖g n x‖ + ‖g n x - f x‖ : norm_le_insert _ _
        ...      < ‖g n‖ * ‖x‖ + ε        : by linarith [lt_ε, (g n).le_op_norm x]
        ...      ≤ C' * ‖x‖ + ε           : by nlinarith [hC' n, norm_nonneg x],
    end }

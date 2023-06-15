/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import algebra.direct_sum.decomposition
import analysis.convex.basic
import analysis.inner_product_space.orthogonal
import analysis.inner_product_space.symmetric
import analysis.normed_space.is_R_or_C
import data.is_R_or_C.lemmas

/-!
# The orthogonal projection

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`orthogonal_projection K : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = orthogonal_projection K u` in `K` minimizes the
distance `‖u - v‖` to `u`.

Also a linear isometry equivalence `reflection K : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `reflection K u` to satisfy
`u + (reflection K u) = 2 • orthogonal_projection K u`.

Basic API for `orthogonal_projection` and `reflection` is developed.

Next, the orthogonal projection is used to prove a series of more subtle lemmas about the
the orthogonal complement of complete subspaces of `E` (the orthogonal complement itself was
defined in `analysis.inner_product_space.basic`); the lemma
`submodule.sup_orthogonal_of_is_complete`, stating that for a complete subspace `K` of `E` we have
`K ⊔ Kᗮ = ⊤`, is a typical example.

## References

The orthogonal projection construction is adapted from
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable theory

open is_R_or_C real filter linear_map (ker range)
open_locale big_operators topology

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [normed_add_comm_group E] [normed_add_comm_group F]
variables [inner_product_space 𝕜 E] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y
local notation `absR` := has_abs.abs

/-! ### Orthogonal projection in inner product spaces -/

/--
Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
theorem exists_norm_eq_infi_of_complete_convex {K : set F} (ne : K.nonempty) (h₁ : is_complete K)
  (h₂ : convex ℝ K) : ∀ u : F, ∃ v ∈ K, ‖u - v‖ = ⨅ w : K, ‖u - w‖ := assume u,
begin
  let δ := ⨅ w : K, ‖u - w‖,
  letI : nonempty K := ne.to_subtype,
  have zero_le_δ : 0 ≤ δ := le_cinfi (λ _, norm_nonneg _),
  have δ_le : ∀ w : K, δ ≤ ‖u - w‖,
    from cinfi_le ⟨0, set.forall_range_iff.2 $ λ _, norm_nonneg _⟩,
  have δ_le' : ∀ w ∈ K, δ ≤ ‖u - w‖ := assume w hw, δ_le ⟨w, hw⟩,
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `‖u - w n‖ < δ + 1 / (n + 1)` (which implies `‖u - w n‖ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ‖u - w n‖ < δ + 1 / (n + 1),
  { have hδ : ∀n:ℕ, δ < δ + 1 / (n + 1), from
      λ n, lt_add_of_le_of_pos le_rfl nat.one_div_pos_of_nat,
    have h := λ n, exists_lt_of_cinfi_lt (hδ n),
    let w : ℕ → K := λ n, classical.some (h n),
    exact ⟨w, λ n, classical.some_spec (h n)⟩ },
  rcases exists_seq with ⟨w, hw⟩,
  have norm_tendsto : tendsto (λ n, ‖u - w n‖) at_top (nhds δ),
  { have h : tendsto (λ n:ℕ, δ) at_top (nhds δ) := tendsto_const_nhds,
    have h' : tendsto (λ n:ℕ, δ + 1 / (n + 1)) at_top (nhds δ),
    { convert h.add tendsto_one_div_add_at_top_nhds_0_nat, simp only [add_zero] },
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h h'
      (λ x, δ_le _) (λ x, le_of_lt (hw _)) },
  -- Step 2: Prove that the sequence `w : ℕ → K` is a Cauchy sequence
  have seq_is_cauchy : cauchy_seq (λ n, ((w n):F)),
  { rw cauchy_seq_iff_le_tendsto_0, -- splits into three goals
    let b := λ n:ℕ, (8 * δ * (1/(n+1)) + 4 * (1/(n+1)) * (1/(n+1))),
    use (λn, sqrt (b n)),
    split,
    -- first goal :  `∀ (n : ℕ), 0 ≤ sqrt (b n)`
    assume n, exact sqrt_nonneg _,
    split,
    -- second goal : `∀ (n m N : ℕ), N ≤ n → N ≤ m → dist ↑(w n) ↑(w m) ≤ sqrt (b N)`
    assume p q N hp hq,
    let wp := ((w p):F), let wq := ((w q):F),
    let a := u - wq, let b := u - wp,
    let half := 1 / (2:ℝ), let div := 1 / ((N:ℝ) + 1),
    have : 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖ =
      2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) :=
    calc
      4 * ‖u - half•(wq + wp)‖ * ‖u - half•(wq + wp)‖ + ‖wp - wq‖ * ‖wp - wq‖
          = (2*‖u - half•(wq + wp)‖) * (2 * ‖u - half•(wq + wp)‖) + ‖wp-wq‖*‖wp-wq‖ : by ring
      ... = (absR ((2:ℝ)) * ‖u - half•(wq + wp)‖) * (absR ((2:ℝ)) * ‖u - half•(wq+wp)‖) +
            ‖wp-wq‖*‖wp-wq‖ :
      by { rw _root_.abs_of_nonneg, exact zero_le_two }
      ... = ‖(2:ℝ) • (u - half • (wq + wp))‖ * ‖(2:ℝ) • (u - half • (wq + wp))‖ +
            ‖wp-wq‖ * ‖wp-wq‖ :
      by simp [norm_smul]
      ... = ‖a + b‖ * ‖a + b‖ + ‖a - b‖ * ‖a - b‖ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0),
            ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b, from (sub_sub_sub_cancel_left _ _ _).symm,
        have eq₂ : u + u - (wq + wp) = a + b, show u + u - (wq + wp) = (u - wq) + (u - wp), abel,
        rw [eq₁, eq₂],
      end
      ... = 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) : parallelogram_law_with_norm ℝ _ _,
    have eq : δ ≤ ‖u - half • (wq + wp)‖,
    { rw smul_add,
      apply δ_le', apply h₂,
        repeat {exact subtype.mem _},
        repeat {exact le_of_lt one_half_pos},
        exact add_halves 1 },
    have eq₁ : 4 * δ * δ ≤ 4 * ‖u - half • (wq + wp)‖ * ‖u - half • (wq + wp)‖,
    { simp_rw mul_assoc,
      exact mul_le_mul_of_nonneg_left (mul_self_le_mul_self zero_le_δ eq) zero_le_four },
    have eq₂ : ‖a‖ * ‖a‖ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw q) (add_le_add_left (nat.one_div_le_one_div hq) _)),
    have eq₂' : ‖b‖ * ‖b‖ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw p) (add_le_add_left (nat.one_div_le_one_div hp) _)),
    rw dist_eq_norm,
    apply nonneg_le_nonneg_of_sq_le_sq, { exact sqrt_nonneg _ },
    rw mul_self_sqrt,
    calc
      ‖wp - wq‖ * ‖wp - wq‖ = 2 * (‖a‖*‖a‖ + ‖b‖*‖b‖) -
        4 * ‖u - half • (wq+wp)‖ * ‖u - half • (wq+wp)‖ : by { rw ← this, simp }
      ... ≤ 2 * (‖a‖ * ‖a‖ + ‖b‖ * ‖b‖) - 4 * δ * δ : sub_le_sub_left eq₁ _
      ... ≤ 2 * ((δ + div) * (δ + div) + (δ + div) * (δ + div)) - 4 * δ * δ :
        sub_le_sub_right (mul_le_mul_of_nonneg_left (add_le_add eq₂ eq₂') (by norm_num)) _
      ... = 8 * δ * div + 4 * div * div : by ring,
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) zero_le_δ) (le_of_lt nat.one_div_pos_of_nat))
      (mul_nonneg (mul_nonneg (by norm_num) nat.one_div_pos_of_nat.le) nat.one_div_pos_of_nat.le),
    -- third goal : `tendsto (λ (n : ℕ), sqrt (b n)) at_top (𝓝 0)`
    apply tendsto.comp,
    { convert continuous_sqrt.continuous_at, exact sqrt_zero.symm },
    have eq₁ : tendsto (λ (n : ℕ), 8 * δ * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (8 * δ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert (@tendsto_const_nhds _ _ _ (4:ℝ) _).mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    have eq₂ : tendsto (λ (n : ℕ), (4:ℝ) * (1 / (n + 1)) * (1 / (n + 1))) at_top (nhds (0:ℝ)),
    { convert this.mul tendsto_one_div_add_at_top_nhds_0_nat,
      simp only [mul_zero] },
    convert eq₁.add eq₂, simp only [add_zero] },
  -- Step 3: By completeness of `K`, let `w : ℕ → K` converge to some `v : K`.
  -- Prove that it satisfies all requirements.
  rcases cauchy_seq_tendsto_of_is_complete h₁ (λ n, _) seq_is_cauchy with ⟨v, hv, w_tendsto⟩,
  use v, use hv,
  have h_cont : continuous (λ v, ‖u - v‖) :=
    continuous.comp continuous_norm (continuous.sub continuous_const continuous_id),
  have : tendsto (λ n, ‖u - w n‖) at_top (nhds ‖u - v‖),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero {K : set F} (h : convex ℝ K) {u : F} {v : F}
  (hv : v ∈ K) : ‖u - v‖ = (⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 :=
iff.intro
begin
  assume eq w hw,
  let δ := ⨅ w : K, ‖u - w‖, let p := ⟪u - v, w - v⟫_ℝ, let q := ‖w - v‖^2,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ‖u - w‖,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ‖u - w‖ := assume w hw, δ_le ⟨w, hw⟩,
  have : ∀θ:ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q,
    assume θ hθ₁ hθ₂,
    have : ‖u - v‖^2 ≤ ‖u - v‖^2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ*θ*‖w - v‖^2 :=
    calc
      ‖u - v‖^2 ≤ ‖u - (θ•w + (1-θ)•v)‖^2 :
      begin
        simp only [sq], apply mul_self_le_mul_self (norm_nonneg _),
        rw [eq], apply δ_le',
        apply h hw hv,
        exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _],
      end
      ... = ‖(u - v) - θ • (w - v)‖^2 :
      begin
        have : u - (θ•w + (1-θ)•v) = (u - v) - θ • (w - v),
        { rw [smul_sub, sub_smul, one_smul],
          simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev] },
        rw this
      end
      ... = ‖u - v‖^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*‖w - v‖^2 :
      begin
        rw [@norm_sub_sq ℝ, inner_smul_right, norm_smul],
        simp only [sq],
        show ‖u-v‖*‖u-v‖-2*(θ*inner(u-v)(w-v))+absR (θ)*‖w-v‖*(absR (θ)*‖w-v‖)=
                ‖u-v‖*‖u-v‖-2*θ*inner(u-v)(w-v)+θ*θ*(‖w-v‖*‖w-v‖),
        rw abs_of_pos hθ₁, ring
      end,
    have eq₁ : ‖u-v‖^2-2*θ*inner(u-v)(w-v)+θ*θ*‖w-v‖^2=‖u-v‖^2+(θ*θ*‖w-v‖^2-2*θ*inner(u-v)(w-v)),
      by abel,
    rw [eq₁, le_add_iff_nonneg_right] at this,
    have eq₂ : θ*θ*‖w-v‖^2-2*θ*inner(u-v)(w-v)=θ*(θ*‖w-v‖^2-2*inner(u-v)(w-v)), ring,
    rw eq₂ at this,
    have := le_of_sub_nonneg (nonneg_of_mul_nonneg_right this hθ₁),
    exact this,
  by_cases hq : q = 0,
  { rw hq at this,
    have : p ≤ 0,
      have := this (1:ℝ) (by norm_num) (by norm_num),
      linarith,
    exact this },
  { have q_pos : 0 < q,
      apply lt_of_le_of_ne, exact sq_nonneg _, intro h, exact hq h.symm,
    by_contradiction hp, rw not_le at hp,
    let θ := min (1:ℝ) (p / q),
    have eq₁ : θ*q ≤ p := calc
      θ*q ≤ (p/q) * q : mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
      ... = p : div_mul_cancel _ hq,
    have : 2 * p ≤ p := calc
      2 * p ≤ θ*q : by { refine this θ (lt_min (by norm_num) (div_pos hp q_pos)) (by norm_num) }
      ... ≤ p : eq₁,
    linarith }
end
begin
  assume h,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  apply le_antisymm,
  { apply le_cinfi, assume w,
    apply nonneg_le_nonneg_of_sq_le_sq (norm_nonneg _),
    have := h w w.2,
    calc
      ‖u - v‖ * ‖u - v‖ ≤ ‖u - v‖ * ‖u - v‖ - 2 * inner (u - v) ((w:F) - v) : by linarith
      ... ≤ ‖u - v‖^2 - 2 * inner (u - v) ((w:F) - v) + ‖(w:F) - v‖^2 :
        by { rw sq, refine le_add_of_nonneg_right _, exact sq_nonneg _ }
      ... = ‖(u - v) - (w - v)‖^2 : (@norm_sub_sq ℝ _ _ _ _ _ _).symm
      ... = ‖u - w‖ * ‖u - w‖ :
        by { have : (u - v) - (w - v) = u - w, abel, rw [this, sq] } },
  { show (⨅ (w : K), ‖u - w‖) ≤ (λw:K, ‖u - w‖) ⟨v, hv⟩,
      apply cinfi_le, use 0, rintros y ⟨z, rfl⟩, exact norm_nonneg _ }
end

variables (K : submodule 𝕜 E)

/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `‖u - v‖` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace
  (h : is_complete (↑K : set E)) : ∀ u : E, ∃ v ∈ K, ‖u - v‖ = ⨅ w : (K : set E), ‖u - w‖ :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.module ℝ 𝕜 E,
  let K' : submodule ℝ E := submodule.restrict_scalars ℝ K,
  exact exists_norm_eq_infi_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex
end

/--
Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero (K : submodule ℝ F) {u : F} {v : F}
  (hv : v ∈ K) : ‖u - v‖ = (⨅ w : (↑K : set F), ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
iff.intro
begin
  assume h,
  have h : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0,
  { rwa [norm_eq_infi_iff_real_inner_le_zero] at h, exacts [K.convex, hv] },
  assume w hw,
  have le : ⟪u - v, w⟫_ℝ ≤ 0,
    let w' := w + v,
    have : w' ∈ K := submodule.add_mem _ hw hv,
    have h₁ := h w' this,
    have h₂ : w' - v = w, simp only [add_neg_cancel_right, sub_eq_add_neg],
    rw h₂ at h₁, exact h₁,
  have ge : ⟪u - v, w⟫_ℝ ≥ 0,
    let w'' := -w + v,
    have : w'' ∈ K := submodule.add_mem _ (submodule.neg_mem _ hw) hv,
    have h₁ := h w'' this,
    have h₂ : w'' - v = -w, simp only [neg_inj, add_neg_cancel_right, sub_eq_add_neg],
    rw [h₂, inner_neg_right] at h₁,
    linarith,
    exact le_antisymm le ge
end
begin
  assume h,
  have : ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0,
    assume w hw,
    let w' := w - v,
    have : w' ∈ K := submodule.sub_mem _ hw hv,
    have h₁ := h w' this,
    exact le_of_eq h₁,
  rwa norm_eq_infi_iff_real_inner_le_zero,
  exacts [submodule.convex _, hv]
end

/--
Characterization of minimizers in the projection on a subspace.
Let `u` be a point in an inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `‖u - v‖` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero {u : E} {v : E}
  (hv : v ∈ K) : ‖u - v‖ = (⨅ w : K, ‖u - w‖) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.module ℝ 𝕜 E,
  let K' : submodule ℝ E := K.restrict_scalars ℝ,
  split,
  { assume H,
    have A : ∀ w ∈ K, re ⟪u - v, w⟫ = 0 := (norm_eq_infi_iff_real_inner_eq_zero K' hv).1 H,
    assume w hw,
    apply ext,
    { simp [A w hw] },
    { symmetry, calc
      im (0 : 𝕜) = 0 : im.map_zero
      ... = re ⟪u - v, (-I) • w⟫ : (A _ (K.smul_mem (-I) hw)).symm
      ... = re ((-I) * ⟪u - v, w⟫) : by rw inner_smul_right
      ... = im ⟪u - v, w⟫ : by simp } },
  { assume H,
    have : ∀ w ∈ K', ⟪u - v, w⟫_ℝ = 0,
    { assume w hw,
      rw [real_inner_eq_re_inner, H w hw],
      exact zero_re' },
    exact (norm_eq_infi_iff_real_inner_eq_zero K' hv).2 this }
end

section orthogonal_projection
variables [complete_space K]

/-- The orthogonal projection onto a complete subspace, as an
unbundled function.  This definition is only intended for use in
setting up the bundled version `orthogonal_projection` and should not
be used once that is defined. -/
def orthogonal_projection_fn (v : E) :=
(exists_norm_eq_infi_of_complete_subspace K (complete_space_coe_iff_is_complete.mp ‹_›) v).some

variables {K}

/-- The unbundled orthogonal projection is in the given subspace.
This lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_mem (v : E) : orthogonal_projection_fn K v ∈ K :=
(exists_norm_eq_infi_of_complete_subspace K
  (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some

/-- The characterization of the unbundled orthogonal projection.  This
lemma is only intended for use in setting up the bundled version
and should not be used once that is defined. -/
lemma orthogonal_projection_fn_inner_eq_zero (v : E) :
  ∀ w ∈ K, ⟪v - orthogonal_projection_fn K v, w⟫ = 0 :=
begin
  rw ←norm_eq_infi_iff_inner_eq_zero K (orthogonal_projection_fn_mem v),
  exact (exists_norm_eq_infi_of_complete_subspace K
    (complete_space_coe_iff_is_complete.mp ‹_›) v).some_spec.some_spec
end

/-- The unbundled orthogonal projection is the unique point in `K`
with the orthogonality property.  This lemma is only intended for use
in setting up the bundled version and should not be used once that is
defined. -/
lemma eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero
  {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  orthogonal_projection_fn K u = v :=
begin
  rw [←sub_eq_zero, ←@inner_self_eq_zero 𝕜],
  have hvs : orthogonal_projection_fn K u - v ∈ K :=
    submodule.sub_mem K (orthogonal_projection_fn_mem u) hvm,
  have huo : ⟪u - orthogonal_projection_fn K u, orthogonal_projection_fn K u - v⟫ = 0 :=
    orthogonal_projection_fn_inner_eq_zero u _ hvs,
  have huv : ⟪u - v, orthogonal_projection_fn K u - v⟫ = 0 := hvo _ hvs,
  have houv : ⟪(u - v) - (u - orthogonal_projection_fn K u), orthogonal_projection_fn K u - v⟫ = 0,
  { rw [inner_sub_left, huo, huv, sub_zero] },
  rwa sub_sub_sub_cancel_left at houv
end

variables (K)

lemma orthogonal_projection_fn_norm_sq (v : E) :
  ‖v‖ * ‖v‖ = ‖v - (orthogonal_projection_fn K v)‖ * ‖v - (orthogonal_projection_fn K v)‖
            + ‖orthogonal_projection_fn K v‖ * ‖orthogonal_projection_fn K v‖ :=
begin
  set p := orthogonal_projection_fn K v,
  have h' : ⟪v - p, p⟫ = 0,
  { exact orthogonal_projection_fn_inner_eq_zero _ _ (orthogonal_projection_fn_mem v) },
  convert norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (v - p) p h' using 2;
  simp,
end

/-- The orthogonal projection onto a complete subspace. -/
def orthogonal_projection : E →L[𝕜] K :=
linear_map.mk_continuous
  { to_fun := λ v, ⟨orthogonal_projection_fn K v, orthogonal_projection_fn_mem v⟩,
    map_add' := λ x y, begin
      have hm : orthogonal_projection_fn K x + orthogonal_projection_fn K y ∈ K :=
        submodule.add_mem K (orthogonal_projection_fn_mem x) (orthogonal_projection_fn_mem y),
      have ho :
        ∀ w ∈ K, ⟪x + y - (orthogonal_projection_fn K x + orthogonal_projection_fn K y), w⟫ = 0,
      { intros w hw,
        rw [add_sub_add_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero _ w hw,
            orthogonal_projection_fn_inner_eq_zero _ w hw, add_zero] },
      ext,
      simp [eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho]
    end,
    map_smul' := λ c x, begin
      have hm : c • orthogonal_projection_fn K x ∈ K :=
        submodule.smul_mem K _ (orthogonal_projection_fn_mem x),
      have ho : ∀ w ∈ K, ⟪c • x - c • orthogonal_projection_fn K x, w⟫ = 0,
      { intros w hw,
        rw [←smul_sub, inner_smul_left, orthogonal_projection_fn_inner_eq_zero _ w hw, mul_zero] },
      ext,
      simp [eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hm ho]
    end }
  1
  (λ x, begin
    simp only [one_mul, linear_map.coe_mk],
    refine le_of_pow_le_pow 2 (norm_nonneg _) (by norm_num) _,
    change ‖orthogonal_projection_fn K x‖ ^ 2 ≤ ‖x‖ ^ 2,
    nlinarith [orthogonal_projection_fn_norm_sq K x]
  end)

variables {K}

@[simp]
lemma orthogonal_projection_fn_eq (v : E) :
  orthogonal_projection_fn K v = (orthogonal_projection K v : E) :=
rfl

/-- The characterization of the orthogonal projection.  -/
@[simp]
lemma orthogonal_projection_inner_eq_zero (v : E) :
  ∀ w ∈ K, ⟪v - orthogonal_projection K v, w⟫ = 0 :=
orthogonal_projection_fn_inner_eq_zero v

/-- The difference of `v` from its orthogonal projection onto `K` is in `Kᗮ`.  -/
@[simp] lemma sub_orthogonal_projection_mem_orthogonal (v : E) :
  v - orthogonal_projection K v ∈ Kᗮ :=
begin
  intros w hw,
  rw inner_eq_zero_symm,
  exact orthogonal_projection_inner_eq_zero _ _ hw
end

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
lemma eq_orthogonal_projection_of_mem_of_inner_eq_zero
  {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

/-- The orthogonal projection of `y` on `U` minimizes the distance `‖y - x‖` for `x ∈ U`. -/
lemma orthogonal_projection_minimal {U : submodule 𝕜 E} [complete_space U] (y : E) :
  ‖y - orthogonal_projection U y‖ = ⨅ x : U, ‖y - x‖ :=
begin
  rw norm_eq_infi_iff_inner_eq_zero _ (submodule.coe_mem _),
  exact orthogonal_projection_inner_eq_zero _
end

/-- The orthogonal projections onto equal subspaces are coerced back to the same point in `E`. -/
lemma eq_orthogonal_projection_of_eq_submodule
  {K' : submodule 𝕜 E} [complete_space K'] (h : K = K') (u : E) :
  (orthogonal_projection K u : E) = (orthogonal_projection K' u : E) :=
begin
  change orthogonal_projection_fn K u = orthogonal_projection_fn K' u,
  congr,
  exact h
end

/-- The orthogonal projection sends elements of `K` to themselves. -/
@[simp] lemma orthogonal_projection_mem_subspace_eq_self (v : K) : orthogonal_projection K v = v :=
by { ext, apply eq_orthogonal_projection_of_mem_of_inner_eq_zero; simp }

/-- A point equals its orthogonal projection if and only if it lies in the subspace. -/
lemma orthogonal_projection_eq_self_iff {v : E} :
  (orthogonal_projection K v : E) = v ↔ v ∈ K :=
begin
  refine ⟨λ h, _, λ h, eq_orthogonal_projection_of_mem_of_inner_eq_zero h _⟩,
  { rw ← h,
    simp },
  { simp }
end

lemma linear_isometry.map_orthogonal_projection {E E' : Type*}
  [normed_add_comm_group E] [normed_add_comm_group E']
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E →ₗᵢ[𝕜] E') (p : submodule 𝕜 E) [complete_space p]
  (x : E) :
  f (orthogonal_projection p x) = orthogonal_projection (p.map f.to_linear_map) (f x) :=
begin
  refine (eq_orthogonal_projection_of_mem_of_inner_eq_zero _ $
    λ y hy, _).symm,
  refine submodule.apply_coe_mem_map _ _,
  rcases hy with ⟨x', hx', rfl : f x' = y⟩,
  rw [← f.map_sub, f.inner_map_map, orthogonal_projection_inner_eq_zero x x' hx']
end

lemma linear_isometry.map_orthogonal_projection' {E E' : Type*}
  [normed_add_comm_group E] [normed_add_comm_group E']
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E →ₗᵢ[𝕜] E') (p : submodule 𝕜 E) [complete_space p]
  (x : E) :
  f (orthogonal_projection p x) = orthogonal_projection (p.map f) (f x) :=
begin
  refine (eq_orthogonal_projection_of_mem_of_inner_eq_zero _ $
    λ y hy, _).symm,
  refine submodule.apply_coe_mem_map _ _,
  rcases hy with ⟨x', hx', rfl : f x' = y⟩,
  rw [← f.map_sub, f.inner_map_map, orthogonal_projection_inner_eq_zero x x' hx']
end

/-- Orthogonal projection onto the `submodule.map` of a subspace. -/
lemma orthogonal_projection_map_apply {E E' : Type*}
  [normed_add_comm_group E] [normed_add_comm_group E']
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (p : submodule 𝕜 E) [complete_space p]
  (x : E') :
  (orthogonal_projection (p.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x : E')
  = f (orthogonal_projection p (f.symm x)) :=
by simpa only [f.coe_to_linear_isometry, f.apply_symm_apply]
  using (f.to_linear_isometry.map_orthogonal_projection p (f.symm x)).symm

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp] lemma orthogonal_projection_bot : orthogonal_projection (⊥ : submodule 𝕜 E) = 0 :=
by ext

variables (K)

/-- The orthogonal projection has norm `≤ 1`. -/
lemma orthogonal_projection_norm_le : ‖orthogonal_projection K‖ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (by norm_num) _

variables (𝕜)

lemma smul_orthogonal_projection_singleton {v : E} (w : E) :
  (‖v‖ ^ 2 : 𝕜) • (orthogonal_projection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v :=
begin
  suffices : ↑(orthogonal_projection (𝕜 ∙ v) ((‖v‖ ^ 2 : 𝕜) • w)) = ⟪v, w⟫ • v,
  { simpa using this },
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero,
  { rw submodule.mem_span_singleton,
    use ⟪v, w⟫ },
  { intros x hx,
    obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.mp hx,
    have hv : ↑‖v‖ ^ 2 = ⟪v, v⟫ := by { norm_cast, simp [@norm_sq_eq_inner 𝕜] },
    simp [inner_sub_left, inner_smul_left, inner_smul_right, map_div₀, mul_comm, hv,
      inner_product_space.conj_symm, hv] }
end

/-- Formula for orthogonal projection onto a single vector. -/
lemma orthogonal_projection_singleton {v : E} (w : E) :
  (orthogonal_projection (𝕜 ∙ v) w : E) = (⟪v, w⟫ / ‖v‖ ^ 2) • v :=
begin
  by_cases hv : v = 0,
  { rw [hv, eq_orthogonal_projection_of_eq_submodule (submodule.span_zero_singleton 𝕜)],
    { simp },
    { apply_instance } },
  have hv' : ‖v‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv),
  have key : ((‖v‖ ^ 2 : 𝕜)⁻¹ * ‖v‖ ^ 2) • ↑(orthogonal_projection (𝕜 ∙ v) w)
              = ((‖v‖ ^ 2 : 𝕜)⁻¹ * ⟪v, w⟫) • v,
  { simp [mul_smul, smul_orthogonal_projection_singleton 𝕜 w] },
  convert key;
  field_simp [hv']
end

/-- Formula for orthogonal projection onto a single unit vector. -/
lemma orthogonal_projection_unit_singleton {v : E} (hv : ‖v‖ = 1) (w : E) :
  (orthogonal_projection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v :=
by { rw ← smul_orthogonal_projection_singleton 𝕜 w, simp [hv] }

end orthogonal_projection

section reflection
variables {𝕜} (K) [complete_space K]

/-- Auxiliary definition for `reflection`: the reflection as a linear equivalence. -/
def reflection_linear_equiv : E ≃ₗ[𝕜] E :=
linear_equiv.of_involutive
  (bit0 (K.subtype.comp (orthogonal_projection K).to_linear_map) - linear_map.id)
  (λ x, by simp [bit0])

/-- Reflection in a complete subspace of an inner product space.  The word "reflection" is
sometimes understood to mean specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point.  The definition here, of
reflection in a subspace, is a more general sense of the word that includes both those common
cases. -/
def reflection : E ≃ₗᵢ[𝕜] E :=
{ norm_map' := begin
    intros x,
    let w : K := orthogonal_projection K x,
    let v := x - w,
    have : ⟪v, w⟫ = 0 := orthogonal_projection_inner_eq_zero x w w.2,
    convert norm_sub_eq_norm_add this using 2,
    { rw [linear_equiv.coe_mk, reflection_linear_equiv,
        linear_equiv.to_fun_eq_coe, linear_equiv.coe_of_involutive,
        linear_map.sub_apply, linear_map.id_apply, bit0, linear_map.add_apply,
        linear_map.comp_apply, submodule.subtype_apply,
        continuous_linear_map.to_linear_map_eq_coe, continuous_linear_map.coe_coe],
      dsimp [w, v],
      abel, },
    { simp only [add_sub_cancel'_right, eq_self_iff_true], }
  end,
  ..reflection_linear_equiv K }

variables {K}

/-- The result of reflecting. -/
lemma reflection_apply (p : E) : reflection K p = bit0 ↑(orthogonal_projection K p) - p := rfl

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_symm : (reflection K).symm = reflection K := rfl

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_inv : (reflection K)⁻¹ = reflection K := rfl

variables (K)

/-- Reflecting twice in the same subspace. -/
@[simp] lemma reflection_reflection (p : E) : reflection K (reflection K p) = p :=
(reflection K).left_inv p

/-- Reflection is involutive. -/
lemma reflection_involutive : function.involutive (reflection K) := reflection_reflection K

/-- Reflection is involutive. -/
@[simp] lemma reflection_trans_reflection :
  (reflection K).trans (reflection K) = linear_isometry_equiv.refl 𝕜 E :=
linear_isometry_equiv.ext $ reflection_involutive K

/-- Reflection is involutive. -/
@[simp] lemma reflection_mul_reflection : reflection K * reflection K = 1 :=
reflection_trans_reflection _

variables {K}

/-- A point is its own reflection if and only if it is in the subspace. -/
lemma reflection_eq_self_iff (x : E) : reflection K x = x ↔ x ∈ K :=
begin
  rw [←orthogonal_projection_eq_self_iff, reflection_apply, sub_eq_iff_eq_add', ← two_smul 𝕜,
    ← two_smul' 𝕜],
  refine (smul_right_injective E _).eq_iff,
  exact two_ne_zero
end

lemma reflection_mem_subspace_eq_self {x : E} (hx : x ∈ K) : reflection K x = x :=
(reflection_eq_self_iff x).mpr hx

/-- Reflection in the `submodule.map` of a subspace. -/
lemma reflection_map_apply {E E' : Type*}
  [normed_add_comm_group E] [normed_add_comm_group E']
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (K : submodule 𝕜 E) [complete_space K] (x : E') :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x = f (reflection K (f.symm x)) :=
by simp [bit0, reflection_apply, orthogonal_projection_map_apply f K x]

/-- Reflection in the `submodule.map` of a subspace. -/
lemma reflection_map {E E' : Type*}
  [normed_add_comm_group E] [normed_add_comm_group E']
  [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (K : submodule 𝕜 E) [complete_space K] :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) = f.symm.trans ((reflection K).trans f) :=
linear_isometry_equiv.ext $ reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp] lemma reflection_bot : reflection (⊥ : submodule 𝕜 E) = linear_isometry_equiv.neg 𝕜 :=
by ext; simp [reflection_apply]

end reflection

section orthogonal

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
lemma submodule.sup_orthogonal_inf_of_complete_space {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂)
  [complete_space K₁] : K₁ ⊔ (K₁ᗮ ⊓ K₂) = K₂ :=
begin
  ext x,
  rw submodule.mem_sup,
  let v : K₁ := orthogonal_projection K₁ x,
  have hvm : x - v ∈ K₁ᗮ := sub_orthogonal_projection_mem_orthogonal x,
  split,
  { rintro ⟨y, hy, z, hz, rfl⟩,
    exact K₂.add_mem (h hy) hz.2 },
  { exact λ hx, ⟨v, v.prop, x - v, ⟨hvm, K₂.sub_mem hx (h v.prop)⟩, add_sub_cancel'_right _ _⟩ }
end

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
lemma submodule.sup_orthogonal_of_complete_space [complete_space K] : K ⊔ Kᗮ = ⊤ :=
begin
  convert submodule.sup_orthogonal_inf_of_complete_space (le_top : K ≤ ⊤),
  simp
end

variables (K)

/-- If `K` is complete, any `v` in `E` can be expressed as a sum of elements of `K` and `Kᗮ`. -/
lemma submodule.exists_sum_mem_mem_orthogonal [complete_space K] (v : E) :
  ∃ (y ∈ K) (z ∈ Kᗮ), v = y + z :=
begin
  have h_mem : v ∈ K ⊔ Kᗮ := by simp [submodule.sup_orthogonal_of_complete_space],
  obtain ⟨y, hy, z, hz, hyz⟩ := submodule.mem_sup.mp h_mem,
  exact ⟨y, hy, z, hz, hyz.symm⟩
end

/-- If `K` is complete, then the orthogonal complement of its orthogonal complement is itself. -/
@[simp] lemma submodule.orthogonal_orthogonal [complete_space K] : Kᗮᗮ = K :=
begin
  ext v,
  split,
  { obtain ⟨y, hy, z, hz, rfl⟩ := K.exists_sum_mem_mem_orthogonal v,
    intros hv,
    have hz' : z = 0,
    { have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_symm],
      simpa [inner_add_right, hyz] using hv z hz },
    simp [hy, hz'] },
  { intros hv w hw,
    rw inner_eq_zero_symm,
    exact hw v hv }
end

lemma submodule.orthogonal_orthogonal_eq_closure [complete_space E] :
  Kᗮᗮ = K.topological_closure :=
begin
  refine le_antisymm _ _,
  { convert submodule.orthogonal_orthogonal_monotone K.le_topological_closure,
    haveI : complete_space K.topological_closure :=
      K.is_closed_topological_closure.complete_space_coe,
    rw K.topological_closure.orthogonal_orthogonal },
  { exact K.topological_closure_minimal K.le_orthogonal_orthogonal Kᗮ.is_closed_orthogonal }
end

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
lemma submodule.is_compl_orthogonal_of_complete_space [complete_space K] : is_compl K Kᗮ :=
⟨K.orthogonal_disjoint, codisjoint_iff.2 submodule.sup_orthogonal_of_complete_space⟩

@[simp] lemma submodule.orthogonal_eq_bot_iff [complete_space (K : set E)] :
  Kᗮ = ⊥ ↔ K = ⊤ :=
begin
  refine ⟨_, λ h, by rw [h, submodule.top_orthogonal_eq_bot] ⟩,
  intro h,
  have : K ⊔ Kᗮ = ⊤ := submodule.sup_orthogonal_of_complete_space,
  rwa [h, sup_comm, bot_sup_eq] at this,
end

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
lemma eq_orthogonal_projection_of_mem_orthogonal
  [complete_space K] {u v : E} (hv : v ∈ K) (hvo : u - v ∈ Kᗮ) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv (λ w, inner_eq_zero_symm.mp ∘ (hvo w))

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
lemma eq_orthogonal_projection_of_mem_orthogonal'
  [complete_space K] {u v z : E} (hv : v ∈ K) (hz : z ∈ Kᗮ) (hu : u = v + z) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_of_mem_orthogonal hv (by simpa [hu])

/-- The orthogonal projection onto `K` of an element of `Kᗮ` is zero. -/
lemma orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
  [complete_space K] {v : E} (hv : v ∈ Kᗮ) :
  orthogonal_projection K v = 0 :=
by { ext, convert eq_orthogonal_projection_of_mem_orthogonal _ _; simp [hv] }

/-- The projection into `U` from an orthogonal submodule `V` is the zero map. -/
lemma submodule.is_ortho.orthogonal_projection_comp_subtypeL {U V : submodule 𝕜 E}
  [complete_space U] (h : U ⟂ V) :
  orthogonal_projection U ∘L V.subtypeL = 0 :=
continuous_linear_map.ext $ λ v,
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero $ h.symm v.prop

/-- The projection into `U` from `V` is the zero map if and only if `U` and `V` are orthogonal. -/
lemma orthogonal_projection_comp_subtypeL_eq_zero_iff {U V : submodule 𝕜 E}
  [complete_space U] :
  orthogonal_projection U ∘L V.subtypeL = 0 ↔ U ⟂ V :=
⟨λ h u hu v hv, begin
  convert orthogonal_projection_inner_eq_zero v u hu using 2,
  have : orthogonal_projection U v = 0 := fun_like.congr_fun h ⟨_, hv⟩,
  rw [this, submodule.coe_zero, sub_zero]
end, submodule.is_ortho.orthogonal_projection_comp_subtypeL⟩

lemma orthogonal_projection_eq_linear_proj [complete_space K] (x : E) :
  orthogonal_projection K x =
    K.linear_proj_of_is_compl _ submodule.is_compl_orthogonal_of_complete_space x :=
begin
  have : is_compl K Kᗮ := submodule.is_compl_orthogonal_of_complete_space,
  nth_rewrite 0 [← submodule.linear_proj_add_linear_proj_of_is_compl_eq_self this x],
  rw [map_add, orthogonal_projection_mem_subspace_eq_self,
      orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (submodule.coe_mem _),
      add_zero]
end

lemma orthogonal_projection_coe_linear_map_eq_linear_proj [complete_space K] :
  (orthogonal_projection K : E →ₗ[𝕜] K) =
    K.linear_proj_of_is_compl _ submodule.is_compl_orthogonal_of_complete_space :=
linear_map.ext $ orthogonal_projection_eq_linear_proj

/-- The reflection in `K` of an element of `Kᗮ` is its negation. -/
lemma reflection_mem_subspace_orthogonal_complement_eq_neg
  [complete_space K] {v : E} (hv : v ∈ Kᗮ) :
  reflection K v = - v :=
by simp [reflection_apply, orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero hv]

/-- The orthogonal projection onto `Kᗮ` of an element of `K` is zero. -/
lemma orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
  [complete_space E] {v : E} (hv : v ∈ K) :
  orthogonal_projection Kᗮ v = 0 :=
orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero (K.le_orthogonal_orthogonal hv)

/-- If `U ≤ V`, then projecting on `V` and then on `U` is the same as projecting on `U`. -/
lemma orthogonal_projection_orthogonal_projection_of_le {U V : submodule 𝕜 E} [complete_space U]
  [complete_space V] (h : U ≤ V) (x : E) :
  orthogonal_projection U (orthogonal_projection V x) = orthogonal_projection U x :=
eq.symm $ by simpa only [sub_eq_zero, map_sub] using
  orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero
  (submodule.orthogonal_le h (sub_orthogonal_projection_mem_orthogonal x))

/-- Given a monotone family `U` of complete submodules of `E` and a fixed `x : E`,
the orthogonal projection of `x` on `U i` tends to the orthogonal projection of `x` on
`(⨆ i, U i).topological_closure` along `at_top`. -/
lemma orthogonal_projection_tendsto_closure_supr [complete_space E] {ι : Type*}
  [semilattice_sup ι] (U : ι → submodule 𝕜 E) [∀ i, complete_space (U i)]
  (hU : monotone U) (x : E) :
  filter.tendsto (λ i, (orthogonal_projection (U i) x : E)) at_top
    (𝓝 (orthogonal_projection (⨆ i, U i).topological_closure x : E)) :=
begin
  casesI is_empty_or_nonempty ι,
  { rw filter_eq_bot_of_is_empty (at_top : filter ι),
    exact tendsto_bot },
  let y := (orthogonal_projection (⨆ i, U i).topological_closure x : E),
  have proj_x : ∀ i, orthogonal_projection (U i) x = orthogonal_projection (U i) y :=
    λ i, (orthogonal_projection_orthogonal_projection_of_le
      ((le_supr U i).trans (supr U).le_topological_closure) _).symm,
  suffices : ∀ ε > 0, ∃ I, ∀ i ≥ I, ‖(orthogonal_projection (U i) y : E) - y‖ < ε,
  { simpa only [proj_x, normed_add_comm_group.tendsto_at_top] using this },
  intros ε hε,
  obtain ⟨a, ha, hay⟩ : ∃ a ∈ ⨆ i, U i, dist y a < ε,
  { have y_mem : y ∈ (⨆ i, U i).topological_closure := submodule.coe_mem _,
    rw [← set_like.mem_coe, submodule.topological_closure_coe, metric.mem_closure_iff] at y_mem,
    exact y_mem ε hε },
  rw dist_eq_norm at hay,
  obtain ⟨I, hI⟩ : ∃ I, a ∈ U I,
  { rwa [submodule.mem_supr_of_directed _ (hU.directed_le)] at ha },
  refine ⟨I, λ i (hi : I ≤ i), _⟩,
  rw [norm_sub_rev, orthogonal_projection_minimal],
  refine lt_of_le_of_lt _ hay,
  change _ ≤ ‖y - (⟨a, hU hi hI⟩ : U i)‖,
  exact cinfi_le ⟨0, set.forall_range_iff.mpr $ λ _, norm_nonneg _⟩ _,
end

/-- Given a monotone family `U` of complete submodules of `E` with dense span supremum,
and a fixed `x : E`, the orthogonal projection of `x` on `U i` tends to `x` along `at_top`. -/
lemma orthogonal_projection_tendsto_self [complete_space E] {ι : Type*} [semilattice_sup ι]
  (U : ι → submodule 𝕜 E) [∀ t, complete_space (U t)] (hU : monotone U)
  (x : E) (hU' : ⊤ ≤ (⨆ t, U t).topological_closure) :
  filter.tendsto (λ t, (orthogonal_projection (U t) x : E)) at_top (𝓝 x) :=
begin
  rw ← eq_top_iff at hU',
  convert orthogonal_projection_tendsto_closure_supr U hU x,
  rw orthogonal_projection_eq_self_iff.mpr _,
  rw hU',
  trivial
end

/-- The orthogonal complement satisfies `Kᗮᗮᗮ = Kᗮ`. -/
lemma submodule.triorthogonal_eq_orthogonal [complete_space E] : Kᗮᗮᗮ = Kᗮ :=
begin
  rw Kᗮ.orthogonal_orthogonal_eq_closure,
  exact K.is_closed_orthogonal.submodule_topological_closure_eq,
end

/-- The closure of `K` is the full space iff `Kᗮ` is trivial. -/
lemma submodule.topological_closure_eq_top_iff [complete_space E] :
  K.topological_closure = ⊤ ↔ Kᗮ = ⊥ :=
begin
  rw ←submodule.orthogonal_orthogonal_eq_closure,
  split; intro h,
  { rw [←submodule.triorthogonal_eq_orthogonal, h, submodule.top_orthogonal_eq_bot] },
  { rw [h, submodule.bot_orthogonal_eq_top] }
end

namespace dense

open submodule

variables {x y : E} [complete_space E]

/-- If `S` is dense and `x - y ∈ Kᗮ`, then `x = y`. -/
lemma eq_of_sub_mem_orthogonal (hK : dense (K : set E)) (h : x - y ∈ Kᗮ) : x = y :=
begin
  rw [dense_iff_topological_closure_eq_top, topological_closure_eq_top_iff] at hK,
  rwa [hK, submodule.mem_bot, sub_eq_zero] at h,
end

lemma eq_zero_of_mem_orthogonal (hK : dense (K : set E)) (h : x ∈ Kᗮ) : x = 0 :=
hK.eq_of_sub_mem_orthogonal (by rwa [sub_zero])

lemma eq_of_inner_left (hK : dense (K : set E)) (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) : x = y :=
hK.eq_of_sub_mem_orthogonal (submodule.sub_mem_orthogonal_of_inner_left h)

lemma eq_zero_of_inner_left (hK : dense (K : set E)) (h : ∀ v : K, ⟪x, v⟫ = 0) : x = 0 :=
hK.eq_of_inner_left (λ v, by rw [inner_zero_left, h v])

lemma eq_of_inner_right (hK : dense (K : set E))
  (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x = y :=
hK.eq_of_sub_mem_orthogonal (submodule.sub_mem_orthogonal_of_inner_right h)

lemma eq_zero_of_inner_right (hK : dense (K : set E))
  (h : ∀ v : K, ⟪(v : E), x⟫ = 0) : x = 0 :=
hK.eq_of_inner_right (λ v, by rw [inner_zero_right, h v])

end dense

/-- The reflection in `Kᗮ` of an element of `K` is its negation. -/
lemma reflection_mem_subspace_orthogonal_precomplement_eq_neg
  [complete_space E] {v : E} (hv : v ∈ K) :
  reflection Kᗮ v = -v :=
reflection_mem_subspace_orthogonal_complement_eq_neg (K.le_orthogonal_orthogonal hv)

/-- The orthogonal projection onto `(𝕜 ∙ v)ᗮ` of `v` is zero. -/
lemma orthogonal_projection_orthogonal_complement_singleton_eq_zero [complete_space E] (v : E) :
  orthogonal_projection (𝕜 ∙ v)ᗮ v = 0 :=
orthogonal_projection_mem_subspace_orthogonal_precomplement_eq_zero
  (submodule.mem_span_singleton_self v)

/-- The reflection in `(𝕜 ∙ v)ᗮ` of `v` is `-v`. -/
lemma reflection_orthogonal_complement_singleton_eq_neg [complete_space E] (v : E) :
  reflection (𝕜 ∙ v)ᗮ v = -v :=
reflection_mem_subspace_orthogonal_precomplement_eq_neg (submodule.mem_span_singleton_self v)

lemma reflection_sub [complete_space F] {v w : F} (h : ‖v‖ = ‖w‖) :
  reflection (ℝ ∙ (v - w))ᗮ v = w :=
begin
  set R : F ≃ₗᵢ[ℝ] F := reflection (ℝ ∙ (v - w))ᗮ,
  suffices : R v + R v = w + w,
  { apply smul_right_injective F (by norm_num : (2:ℝ) ≠ 0),
    simpa [two_smul] using this },
  have h₁ : R (v - w) = -(v - w) := reflection_orthogonal_complement_singleton_eq_neg (v - w),
  have h₂ : R (v + w) = v + w,
  { apply reflection_mem_subspace_eq_self,
    rw submodule.mem_orthogonal_singleton_iff_inner_left,
    rw real_inner_add_sub_eq_zero_iff,
    exact h },
  convert congr_arg2 (+) h₂ h₁ using 1,
  { simp },
  { abel }
end

variables (K)

/-- In a complete space `E`, a vector splits as the sum of its orthogonal projections onto a
complete submodule `K` and onto the orthogonal complement of `K`.-/
lemma eq_sum_orthogonal_projection_self_orthogonal_complement
  [complete_space E] [complete_space K] (w : E) :
  w = (orthogonal_projection K w : E) + (orthogonal_projection Kᗮ w : E) :=
begin
  obtain ⟨y, hy, z, hz, hwyz⟩ := K.exists_sum_mem_mem_orthogonal w,
  convert hwyz,
  { exact eq_orthogonal_projection_of_mem_orthogonal' hy hz hwyz },
  { rw add_comm at hwyz,
    refine eq_orthogonal_projection_of_mem_orthogonal' hz _ hwyz,
    simp [hy] }
end

/-- The Pythagorean theorem, for an orthogonal projection.-/
lemma norm_sq_eq_add_norm_sq_projection
  (x : E) (S : submodule 𝕜 E) [complete_space E] [complete_space S] :
  ‖x‖^2 = ‖orthogonal_projection S x‖^2 + ‖orthogonal_projection Sᗮ x‖^2 :=
begin
  let p1 := orthogonal_projection S,
  let p2 := orthogonal_projection Sᗮ,
  have x_decomp : x = p1 x + p2 x :=
    eq_sum_orthogonal_projection_self_orthogonal_complement S x,
  have x_orth : ⟪ (p1 x : E), p2 x ⟫ = 0 :=
    submodule.inner_right_of_mem_orthogonal (set_like.coe_mem (p1 x)) (set_like.coe_mem (p2 x)),
  nth_rewrite 0 [x_decomp],
  simp only [sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((p1 x) : E) (p2 x) x_orth,
             add_left_inj, mul_eq_mul_left_iff, norm_eq_zero, true_or, eq_self_iff_true,
             submodule.coe_norm, submodule.coe_eq_zero]
end

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
lemma id_eq_sum_orthogonal_projection_self_orthogonal_complement
  [complete_space E] [complete_space K] :
  continuous_linear_map.id 𝕜 E
  = K.subtypeL.comp (orthogonal_projection K)
  + Kᗮ.subtypeL.comp (orthogonal_projection Kᗮ) :=
by { ext w, exact eq_sum_orthogonal_projection_self_orthogonal_complement K w }

@[simp] lemma inner_orthogonal_projection_eq_of_mem_right [complete_space K] (u : K) (v : E) :
  ⟪orthogonal_projection K v, u⟫ = ⟪v, u⟫ :=
calc ⟪orthogonal_projection K v, u⟫
    = ⟪(orthogonal_projection K v : E), u⟫ : K.coe_inner _ _
... = ⟪(orthogonal_projection K v : E), u⟫ + ⟪v - orthogonal_projection K v, u⟫ :
      by rw [orthogonal_projection_inner_eq_zero _ _ (submodule.coe_mem _), add_zero]
... = ⟪v, u⟫ :
      by rw [← inner_add_left, add_sub_cancel'_right]

@[simp] lemma inner_orthogonal_projection_eq_of_mem_left [complete_space K] (u : K) (v : E) :
  ⟪u, orthogonal_projection K v⟫ = ⟪(u : E), v⟫ :=
by rw [← inner_conj_symm, ← inner_conj_symm (u : E), inner_orthogonal_projection_eq_of_mem_right]

/-- The orthogonal projection is self-adjoint. -/
lemma inner_orthogonal_projection_left_eq_right
  [complete_space K] (u v : E) :
  ⟪↑(orthogonal_projection K u), v⟫ = ⟪u, orthogonal_projection K v⟫ :=
by rw [← inner_orthogonal_projection_eq_of_mem_left, inner_orthogonal_projection_eq_of_mem_right]

/-- The orthogonal projection is symmetric. -/
lemma orthogonal_projection_is_symmetric
  [complete_space K] :
  (K.subtypeL ∘L orthogonal_projection K : E →ₗ[𝕜] E).is_symmetric :=
inner_orthogonal_projection_left_eq_right K

open finite_dimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.finrank_add_inf_finrank_orthogonal {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
  finrank 𝕜 K₁ + finrank 𝕜 (K₁ᗮ ⊓ K₂ : submodule 𝕜 E) = finrank 𝕜 K₂ :=
begin
  haveI := submodule.finite_dimensional_of_le h,
  haveI := proper_is_R_or_C 𝕜 K₁,
  have hd := submodule.finrank_sup_add_finrank_inf_eq K₁ (K₁ᗮ ⊓ K₂),
  rw [←inf_assoc, (submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, finrank_bot,
      submodule.sup_orthogonal_inf_of_complete_space h] at hd,
  rw add_zero at hd,
  exact hd.symm
end

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.finrank_add_inf_finrank_orthogonal' {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) {n : ℕ} (h_dim : finrank 𝕜 K₁ + n = finrank 𝕜 K₂) :
  finrank 𝕜 (K₁ᗮ ⊓ K₂ : submodule 𝕜 E) = n :=
by { rw ← add_right_inj (finrank 𝕜 K₁),
     simp [submodule.finrank_add_inf_finrank_orthogonal h, h_dim] }

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
lemma submodule.finrank_add_finrank_orthogonal [finite_dimensional 𝕜 E] (K : submodule 𝕜 E) :
  finrank 𝕜 K + finrank 𝕜 Kᗮ = finrank 𝕜 E :=
begin
  convert submodule.finrank_add_inf_finrank_orthogonal (le_top : K ≤ ⊤) using 1,
  { rw inf_top_eq },
  { simp }
end

/-- Given a finite-dimensional space `E` and subspace `K`, the dimensions of `K` and `Kᗮ` add to
that of `E`. -/
lemma submodule.finrank_add_finrank_orthogonal' [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} {n : ℕ}
  (h_dim : finrank 𝕜 K + n = finrank 𝕜 E) :
  finrank 𝕜 Kᗮ = n :=
by { rw ← add_right_inj (finrank 𝕜 K), simp [submodule.finrank_add_finrank_orthogonal, h_dim] }

local attribute [instance] fact_finite_dimensional_of_finrank_eq_succ

/-- In a finite-dimensional inner product space, the dimension of the orthogonal complement of the
span of a nonzero vector is one less than the dimension of the space. -/
lemma finrank_orthogonal_span_singleton {n : ℕ} [_i : fact (finrank 𝕜 E = n + 1)]
  {v : E} (hv : v ≠ 0) :
  finrank 𝕜 (𝕜 ∙ v)ᗮ = n :=
submodule.finrank_add_finrank_orthogonal' $ by simp [finrank_span_singleton hv, _i.elim, add_comm]

/-- An element `φ` of the orthogonal group of `F` can be factored as a product of reflections, and
specifically at most as many reflections as the dimension of the complement of the fixed subspace
of `φ`. -/
lemma linear_isometry_equiv.reflections_generate_dim_aux [finite_dimensional ℝ F] {n : ℕ}
  (φ : F ≃ₗᵢ[ℝ] F)
  (hn : finrank ℝ (ker (continuous_linear_map.id ℝ F - φ))ᗮ ≤ n) :
  ∃ l : list F, l.length ≤ n ∧ φ = (l.map (λ v, reflection (ℝ ∙ v)ᗮ)).prod :=
begin
  -- We prove this by strong induction on `n`, the dimension of the orthogonal complement of the
  -- fixed subspace of the endomorphism `φ`
  induction n with n IH generalizing φ,
  { -- Base case: `n = 0`, the fixed subspace is the whole space, so `φ = id`
    refine ⟨[], rfl.le, show φ = 1, from _⟩,
    have : ker (continuous_linear_map.id ℝ F - φ) = ⊤,
    { rwa [le_zero_iff, finrank_eq_zero, submodule.orthogonal_eq_bot_iff] at hn },
    symmetry,
    ext x,
    have := linear_map.congr_fun (linear_map.ker_eq_top.mp this) x,
    simpa only [sub_eq_zero, continuous_linear_map.to_linear_map_eq_coe,
                continuous_linear_map.coe_sub, linear_map.sub_apply, linear_map.zero_apply]
                using this },
  { -- Inductive step.  Let `W` be the fixed subspace of `φ`.  We suppose its complement to have
    -- dimension at most n + 1.
    let W := ker (continuous_linear_map.id ℝ F - φ),
    have hW : ∀ w ∈ W, φ w = w := λ w hw, (sub_eq_zero.mp hw).symm,
    by_cases hn' : finrank ℝ Wᗮ ≤ n,
    { obtain ⟨V, hV₁, hV₂⟩ := IH φ hn',
      exact ⟨V, hV₁.trans n.le_succ, hV₂⟩ },
    -- Take a nonzero element `v` of the orthogonal complement of `W`.
    haveI : nontrivial Wᗮ := nontrivial_of_finrank_pos (by linarith [zero_le n] : 0 < finrank ℝ Wᗮ),
    obtain ⟨v, hv⟩ := exists_ne (0 : Wᗮ),
    have hφv : φ v ∈ Wᗮ,
    { intros w hw,
      rw [← hW w hw, linear_isometry_equiv.inner_map_map],
      exact v.prop w hw },
    have hv' : (v:F) ∉ W,
    { intros h,
      exact hv ((submodule.mem_left_iff_eq_zero_of_disjoint W.orthogonal_disjoint).mp h) },
    -- Let `ρ` be the reflection in `v - φ v`; this is designed to swap `v` and `φ v`
    let x : F := v - φ v,
    let ρ := reflection (ℝ ∙ x)ᗮ,
    -- Notation: Let `V` be the fixed subspace of `φ.trans ρ`
    let V := ker (continuous_linear_map.id ℝ F - (φ.trans ρ)),
    have hV : ∀ w, ρ (φ w) = w → w ∈ V,
    { intros w hw,
      change w - ρ (φ w) = 0,
      rw [sub_eq_zero, hw] },
    -- Everything fixed by `φ` is fixed by `φ.trans ρ`
    have H₂V : W ≤ V,
    { intros w hw,
      apply hV,
      rw hW w hw,
      refine reflection_mem_subspace_eq_self _,
      rw submodule.mem_orthogonal_singleton_iff_inner_left,
      exact submodule.sub_mem _ v.prop hφv _ hw },
    -- `v` is also fixed by `φ.trans ρ`
    have H₁V : (v : F) ∈ V,
    { apply hV,
      have : ρ v = φ v := reflection_sub (φ.norm_map v).symm,
      rw ←this,
      exact reflection_reflection _ _, },
    -- By dimension-counting, the complement of the fixed subspace of `φ.trans ρ` has dimension at
    -- most `n`
    have : finrank ℝ Vᗮ ≤ n,
    { change finrank ℝ Wᗮ ≤ n + 1 at hn,
      have : finrank ℝ W + 1 ≤ finrank ℝ V :=
        submodule.finrank_lt_finrank_of_lt (set_like.lt_iff_le_and_exists.2 ⟨H₂V, v, H₁V, hv'⟩),
      have : finrank ℝ V + finrank ℝ Vᗮ = finrank ℝ F := V.finrank_add_finrank_orthogonal,
      have : finrank ℝ W + finrank ℝ Wᗮ = finrank ℝ F := W.finrank_add_finrank_orthogonal,
      linarith },
    -- So apply the inductive hypothesis to `φ.trans ρ`
    obtain ⟨l, hl, hφl⟩ := IH (ρ * φ) this,
    -- Prepend `ρ` to the factorization into reflections obtained for `φ.trans ρ`; this gives a
    -- factorization into reflections for `φ`.
    refine ⟨x :: l, nat.succ_le_succ hl, _⟩,
    rw [list.map_cons, list.prod_cons],
    have := congr_arg ((*) ρ) hφl,
    rwa [←mul_assoc, reflection_mul_reflection, one_mul] at this, }
end

/-- The orthogonal group of `F` is generated by reflections; specifically each element `φ` of the
orthogonal group is a product of at most as many reflections as the dimension of `F`.

Special case of the **Cartan–Dieudonné theorem**. -/
lemma linear_isometry_equiv.reflections_generate_dim [finite_dimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
  ∃ l : list F, l.length ≤ finrank ℝ F ∧ φ = (l.map (λ v, reflection (ℝ ∙ v)ᗮ)).prod :=
let ⟨l, hl₁, hl₂⟩ := φ.reflections_generate_dim_aux le_rfl in
⟨l, hl₁.trans (submodule.finrank_le _), hl₂⟩

/-- The orthogonal group of `F` is generated by reflections. -/
lemma linear_isometry_equiv.reflections_generate [finite_dimensional ℝ F] :
  subgroup.closure (set.range (λ v : F, reflection (ℝ ∙ v)ᗮ)) = ⊤ :=
begin
  rw subgroup.eq_top_iff',
  intros φ,
  rcases φ.reflections_generate_dim with ⟨l, _, rfl⟩,
  apply (subgroup.closure _).list_prod_mem,
  intros x hx,
  rcases list.mem_map.mp hx with ⟨a, _, hax⟩,
  exact subgroup.subset_closure ⟨a, hax⟩,
end

end orthogonal

section orthogonal_family
variables {ι : Type*}

/-- An orthogonal family of subspaces of `E` satisfies `direct_sum.is_internal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
lemma orthogonal_family.is_internal_iff_of_is_complete [decidable_eq ι]
  {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ))
  (hc : is_complete (↑(supr V) : set E)) :
  direct_sum.is_internal V ↔ (supr V)ᗮ = ⊥ :=
begin
  haveI : complete_space ↥(supr V) := hc.complete_space_coe,
  simp only [direct_sum.is_internal_submodule_iff_independent_and_supr_eq_top, hV.independent,
    true_and, submodule.orthogonal_eq_bot_iff]
end

/-- An orthogonal family of subspaces of `E` satisfies `direct_sum.is_internal` (that is,
they provide an internal direct sum decomposition of `E`) if and only if their span has trivial
orthogonal complement. -/
lemma orthogonal_family.is_internal_iff [decidable_eq ι] [finite_dimensional 𝕜 E]
  {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ)) :
  direct_sum.is_internal V ↔ (supr V)ᗮ = ⊥ :=
begin
  haveI h := finite_dimensional.proper_is_R_or_C 𝕜 ↥(supr V),
  exact hV.is_internal_iff_of_is_complete
    (complete_space_coe_iff_is_complete.mp infer_instance)
end

open_locale direct_sum

/-- If `x` lies within an orthogonal family `v`, it can be expressed as a sum of projections. -/
lemma orthogonal_family.sum_projection_of_mem_supr [fintype ι]
  {V : ι → submodule 𝕜 E} [∀ i, complete_space ↥(V i)]
  (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ)) (x : E) (hx : x ∈ supr V) :
  ∑ i, (orthogonal_projection (V i) x : E) = x :=
begin
  refine submodule.supr_induction _ hx (λ i x hx, _) _ (λ x y hx hy, _),
  { refine (finset.sum_eq_single_of_mem i (finset.mem_univ _) $ λ j _ hij, _).trans
      (orthogonal_projection_eq_self_iff.mpr hx),
    rw [orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero, submodule.coe_zero],
    exact hV.is_ortho hij.symm hx },
  { simp_rw [map_zero, submodule.coe_zero, finset.sum_const_zero] },
  { simp_rw [map_add, submodule.coe_add, finset.sum_add_distrib],
    exact congr_arg2 (+) hx hy },
end

/-- If a family of submodules is orthogonal, then the `orthogonal_projection` on a direct sum
is just the coefficient of that direct sum. -/
lemma orthogonal_family.projection_direct_sum_coe_add_hom [decidable_eq ι]
  {V : ι → submodule 𝕜 E} (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ))
  (x : ⨁ i, V i) (i : ι) [complete_space ↥(V i)] :
    orthogonal_projection (V i) (direct_sum.coe_add_monoid_hom V x) = x i :=
begin
  induction x using direct_sum.induction_on with j x x y hx hy,
  { simp },
  { simp_rw [direct_sum.coe_add_monoid_hom_of, direct_sum.of, dfinsupp.single_add_hom_apply],
    obtain rfl | hij := decidable.eq_or_ne i j,
    { rw [orthogonal_projection_mem_subspace_eq_self, dfinsupp.single_eq_same] },
    { rw [orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero,
        dfinsupp.single_eq_of_ne hij.symm],
      exact hV.is_ortho hij.symm x.prop } },
  { simp_rw [map_add, dfinsupp.add_apply],
    exact congr_arg2 (+) hx hy },
end

/-- If a family of submodules is orthogonal and they span the whole space, then the orthogonal
projection provides a means to decompose the space into its submodules.

The projection function is `decompose V x i = orthogonal_projection (V i) x`.

See note [reducible non-instances]. -/
@[reducible]
def orthogonal_family.decomposition [decidable_eq ι] [fintype ι] {V : ι → submodule 𝕜 E}
  [∀ i, complete_space ↥(V i)]
  (hV : orthogonal_family 𝕜 (λ i, V i) (λ i, (V i).subtypeₗᵢ)) (h : supr V = ⊤) :
  direct_sum.decomposition V :=
{ decompose' := λ x, dfinsupp.equiv_fun_on_fintype.symm $ λ i, orthogonal_projection (V i) x,
  left_inv := λ x, begin
    dsimp only,
    letI := λ i, classical.dec_eq (V i),
    rw [direct_sum.coe_add_monoid_hom, direct_sum.to_add_monoid, dfinsupp.lift_add_hom_apply,
      dfinsupp.sum_add_hom_apply, dfinsupp.sum_eq_sum_fintype],
    { simp_rw [equiv.apply_symm_apply, add_submonoid_class.coe_subtype],
      exact hV.sum_projection_of_mem_supr _ ((h.ge : _) submodule.mem_top),},
    { intro i,
      exact map_zero _ },
  end,
  right_inv := λ x, begin
    dsimp only,
    simp_rw [hV.projection_direct_sum_coe_add_hom, dfinsupp.equiv_fun_on_fintype_symm_coe],
  end }

end orthogonal_family

section orthonormal_basis

variables {𝕜 E} {v : set E}

open finite_dimensional submodule set

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the orthogonal
complement of its span is empty. -/
lemma maximal_orthonormal_iff_orthogonal_complement_eq_bot (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ (span 𝕜 v)ᗮ = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  split,
  { contrapose!,
    -- ** direction 1: nonempty orthogonal complement implies nonmaximal
    rintros ⟨x, hx', hx⟩,
    -- take a nonzero vector and normalize it
    let e := (‖x‖⁻¹ : 𝕜) • x,
    have he : ‖e‖ = 1 := by simp [e, norm_smul_inv_norm hx],
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx',
    have he'' : e ∉ v,
    { intros hev,
      have : e = 0,
      { have : e ∈ (span 𝕜 v) ⊓ (span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩,
        simpa [(span 𝕜 v).inf_orthogonal_eq_bot] using this },
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩,
      contradiction },
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine ⟨insert e v, v.subset_insert e, ⟨_, _⟩, (v.ne_insert_of_not_mem he'').symm⟩,
    { -- show that the elements of `insert e v` have unit length
      rintros ⟨a, ha'⟩,
      cases eq_or_mem_of_mem_insert ha' with ha ha,
      { simp [ha, he] },
      { exact hv.1 ⟨a, ha⟩ } },
    { -- show that the elements of `insert e v` are orthogonal
      have h_end : ∀ a ∈ v, ⟪a, e⟫ = 0,
      { intros a ha,
        exact he' a (submodule.subset_span ha) },
      rintros ⟨a, ha'⟩,
      cases eq_or_mem_of_mem_insert ha' with ha ha,
      { rintros ⟨b, hb'⟩ hab',
        have hb : b ∈ v,
        { refine mem_of_mem_insert_of_ne hb' _,
          intros hbe',
          apply hab',
          simp [ha, hbe'] },
        rw inner_eq_zero_symm,
        simpa [ha] using h_end b hb },
      rintros ⟨b, hb'⟩ hab',
      cases eq_or_mem_of_mem_insert hb' with hb hb,
      { simpa [hb] using h_end a ha },
      have : (⟨a, ha⟩ : v) ≠ ⟨b, hb⟩,
      { intros hab'',
        apply hab',
        simpa using hab'' },
      exact hv.2 this } },
    { -- ** direction 2: empty orthogonal complement implies maximal
      simp only [subset.antisymm_iff],
      rintros h u (huv : v ⊆ u) hu,
      refine ⟨_, huv⟩,
      intros x hxu,
      refine ((mt (h x)) (hu.ne_zero ⟨x, hxu⟩)).imp_symm _,
      intros hxv y hy,
      have hxv' : (⟨x, hxu⟩ : u) ∉ (coe ⁻¹' v : set u) := by simp [huv, hxv],
      obtain ⟨l, hl, rfl⟩ :
        ∃ l ∈ finsupp.supported 𝕜 𝕜 (coe ⁻¹' v : set u), (finsupp.total ↥u E 𝕜 coe) l = y,
      { rw ← finsupp.mem_span_image_iff_total,
        simp [huv, inter_eq_self_of_subset_left, hy] },
      exact hu.inner_finsupp_eq_zero hxv' hl }
end

variables [finite_dimensional 𝕜 E]

/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
lemma maximal_orthonormal_iff_basis_of_finite_dimensional
  (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ ∃ b : basis v 𝕜 E, ⇑b = coe :=
begin
  haveI := proper_is_R_or_C 𝕜 (span 𝕜 v),
  rw maximal_orthonormal_iff_orthogonal_complement_eq_bot hv,
  have hv_compl : is_complete (span 𝕜 v : set E) := (span 𝕜 v).complete_of_finite_dimensional,
  rw submodule.orthogonal_eq_bot_iff,
  have hv_coe : range (coe : v → E) = v := by simp,
  split,
  { refine λ h, ⟨basis.mk hv.linear_independent _, basis.coe_mk _ _⟩,
    convert h.ge },
  { rintros ⟨h, coe_h⟩,
    rw [← h.span_eq, coe_h, hv_coe] }
end

end orthonormal_basis

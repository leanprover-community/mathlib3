/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Frédéric Dupuis, Heather Macbeth
-/
import analysis.inner_product_space.basic
import analysis.convex.basic

/-!
# The orthogonal projection

Given a nonempty complete subspace `K` of an inner product space `E`, this file constructs
`orthogonal_projection K : E →L[𝕜] K`, the orthogonal projection of `E` onto `K`.  This map
satisfies: for any point `u` in `E`, the point `v = orthogonal_projection K u` in `K` minimizes the
distance `∥u - v∥` to `u`.

Also a linear isometry equivalence `reflection K : E ≃ₗᵢ[𝕜] E` is constructed, by choosing, for
each `u : E`, the point `reflection K u` to satisfy
`u + (reflection K u) = 2 • orthogonal_projection K u`.

Basic API for `orthogonal_projection` and `reflection` is developed.

Next, the orthogonal projection is used to prove a series of more subtle lemmas about the
the orthogonal complement of complete subspaces of `E` (the orthogonal complement itself was
defined in `analysis.inner_product_space.basic`); the lemma
`submodule.sup_orthogonal_of_is_complete`, stating that for a complete subspace `K` of `E` we have
`K ⊔ Kᗮ = ⊤`, is a typical example.

The last section covers orthonormal bases, Hilbert bases, etc. The lemma
`maximal_orthonormal_iff_dense_span`, whose proof requires the theory on the orthogonal complement
developed earlier in this file, states that an orthonormal set in an inner product space is
maximal, if and only if its span is dense (i.e., iff it is Hilbert basis, although we do not make
that definition).  Various consequences are stated, including that if `E` is finite-dimensional
then a maximal orthonormal set is a basis (`maximal_orthonormal_iff_basis_of_finite_dimensional`).

## References

The orthogonal projection construction is adapted from
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/

noncomputable theory

open is_R_or_C real filter
open_locale big_operators classical topological_space

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y
local notation `absR` := has_abs.abs

/-! ### Orthogonal projection in inner product spaces -/

/--
Existence of minimizers
Let `u` be a point in a real inner product space, and let `K` be a nonempty complete convex subset.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
 -/
-- FIXME this monolithic proof causes a deterministic timeout with `-T50000`
-- It should be broken in a sequence of more manageable pieces,
-- perhaps with individual statements for the three steps below.
theorem exists_norm_eq_infi_of_complete_convex {K : set F} (ne : K.nonempty) (h₁ : is_complete K)
  (h₂ : convex ℝ K) : ∀ u : F, ∃ v ∈ K, ∥u - v∥ = ⨅ w : K, ∥u - w∥ := assume u,
begin
  let δ := ⨅ w : K, ∥u - w∥,
  letI : nonempty K := ne.to_subtype,
  have zero_le_δ : 0 ≤ δ := le_cinfi (λ _, norm_nonneg _),
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    from cinfi_le ⟨0, set.forall_range_iff.2 $ λ _, norm_nonneg _⟩,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  -- Step 1: since `δ` is the infimum, can find a sequence `w : ℕ → K` in `K`
  -- such that `∥u - w n∥ < δ + 1 / (n + 1)` (which implies `∥u - w n∥ --> δ`);
  -- maybe this should be a separate lemma
  have exists_seq : ∃ w : ℕ → K, ∀ n, ∥u - w n∥ < δ + 1 / (n + 1),
  { have hδ : ∀n:ℕ, δ < δ + 1 / (n + 1), from
      λ n, lt_add_of_le_of_pos (le_refl _) nat.one_div_pos_of_nat,
    have h := λ n, exists_lt_of_cinfi_lt (hδ n),
    let w : ℕ → K := λ n, classical.some (h n),
    exact ⟨w, λ n, classical.some_spec (h n)⟩ },
  rcases exists_seq with ⟨w, hw⟩,
  have norm_tendsto : tendsto (λ n, ∥u - w n∥) at_top (nhds δ),
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
    have : 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥ =
      2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) :=
    calc
      4 * ∥u - half•(wq + wp)∥ * ∥u - half•(wq + wp)∥ + ∥wp - wq∥ * ∥wp - wq∥
          = (2*∥u - half•(wq + wp)∥) * (2 * ∥u - half•(wq + wp)∥) + ∥wp-wq∥*∥wp-wq∥ : by ring
      ... = (absR ((2:ℝ)) * ∥u - half•(wq + wp)∥) * (absR ((2:ℝ)) * ∥u - half•(wq+wp)∥) +
            ∥wp-wq∥*∥wp-wq∥ :
      by { rw _root_.abs_of_nonneg, exact zero_le_two }
      ... = ∥(2:ℝ) • (u - half • (wq + wp))∥ * ∥(2:ℝ) • (u - half • (wq + wp))∥ +
            ∥wp-wq∥ * ∥wp-wq∥ :
      by simp [norm_smul]
      ... = ∥a + b∥ * ∥a + b∥ + ∥a - b∥ * ∥a - b∥ :
      begin
        rw [smul_sub, smul_smul, mul_one_div_cancel (_root_.two_ne_zero : (2 : ℝ) ≠ 0),
            ← one_add_one_eq_two, add_smul],
        simp only [one_smul],
        have eq₁ : wp - wq = a - b, from (sub_sub_sub_cancel_left _ _ _).symm,
        have eq₂ : u + u - (wq + wp) = a + b, show u + u - (wq + wp) = (u - wq) + (u - wp), abel,
        rw [eq₁, eq₂],
      end
      ... = 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) : parallelogram_law_with_norm,
    have eq : δ ≤ ∥u - half • (wq + wp)∥,
    { rw smul_add,
      apply δ_le', apply h₂,
        repeat {exact subtype.mem _},
        repeat {exact le_of_lt one_half_pos},
        exact add_halves 1 },
    have eq₁ : 4 * δ * δ ≤ 4 * ∥u - half • (wq + wp)∥ * ∥u - half • (wq + wp)∥,
    { mono, mono, norm_num, apply mul_nonneg, norm_num, exact norm_nonneg _ },
    have eq₂ : ∥a∥ * ∥a∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw q) (add_le_add_left (nat.one_div_le_one_div hq) _)),
    have eq₂' : ∥b∥ * ∥b∥ ≤ (δ + div) * (δ + div) :=
      mul_self_le_mul_self (norm_nonneg _)
        (le_trans (le_of_lt $ hw p) (add_le_add_left (nat.one_div_le_one_div hp) _)),
    rw dist_eq_norm,
    apply nonneg_le_nonneg_of_sq_le_sq, { exact sqrt_nonneg _ },
    rw mul_self_sqrt,
    exact calc
      ∥wp - wq∥ * ∥wp - wq∥ = 2 * (∥a∥*∥a∥ + ∥b∥*∥b∥) -
        4 * ∥u - half • (wq+wp)∥ * ∥u - half • (wq+wp)∥ : by { rw ← this, simp }
      ... ≤ 2 * (∥a∥ * ∥a∥ + ∥b∥ * ∥b∥) - 4 * δ * δ : sub_le_sub_left eq₁ _
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
  have h_cont : continuous (λ v, ∥u - v∥) :=
    continuous.comp continuous_norm (continuous.sub continuous_const continuous_id),
  have : tendsto (λ n, ∥u - w n∥) at_top (nhds ∥u - v∥),
    convert (tendsto.comp h_cont.continuous_at w_tendsto),
  exact tendsto_nhds_unique this norm_tendsto,
  exact subtype.mem _
end

/-- Characterization of minimizers for the projection on a convex set in a real inner product
space. -/
theorem norm_eq_infi_iff_real_inner_le_zero {K : set F} (h : convex ℝ K) {u : F} {v : F}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : K, ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w - v⟫_ℝ ≤ 0 :=
iff.intro
begin
  assume eq w hw,
  let δ := ⨅ w : K, ∥u - w∥, let p := ⟪u - v, w - v⟫_ℝ, let q := ∥w - v∥^2,
  letI : nonempty K := ⟨⟨v, hv⟩⟩,
  have zero_le_δ : 0 ≤ δ,
    apply le_cinfi, intro, exact norm_nonneg _,
  have δ_le : ∀ w : K, δ ≤ ∥u - w∥,
    assume w, apply cinfi_le, use (0:ℝ), rintros _ ⟨_, rfl⟩, exact norm_nonneg _,
  have δ_le' : ∀ w ∈ K, δ ≤ ∥u - w∥ := assume w hw, δ_le ⟨w, hw⟩,
  have : ∀θ:ℝ, 0 < θ → θ ≤ 1 → 2 * p ≤ θ * q,
    assume θ hθ₁ hθ₂,
    have : ∥u - v∥^2 ≤ ∥u - v∥^2 - 2 * θ * ⟪u - v, w - v⟫_ℝ + θ*θ*∥w - v∥^2 :=
    calc
      ∥u - v∥^2 ≤ ∥u - (θ•w + (1-θ)•v)∥^2 :
      begin
        simp only [sq], apply mul_self_le_mul_self (norm_nonneg _),
        rw [eq], apply δ_le',
        apply h hw hv,
        exacts [le_of_lt hθ₁, sub_nonneg.2 hθ₂, add_sub_cancel'_right _ _],
      end
      ... = ∥(u - v) - θ • (w - v)∥^2 :
      begin
        have : u - (θ•w + (1-θ)•v) = (u - v) - θ • (w - v),
        { rw [smul_sub, sub_smul, one_smul],
          simp only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, neg_add_rev] },
        rw this
      end
      ... = ∥u - v∥^2 - 2 * θ * inner (u - v) (w - v) + θ*θ*∥w - v∥^2 :
      begin
        rw [norm_sub_sq, inner_smul_right, norm_smul],
        simp only [sq],
        show ∥u-v∥*∥u-v∥-2*(θ*inner(u-v)(w-v))+absR (θ)*∥w-v∥*(absR (θ)*∥w-v∥)=
                ∥u-v∥*∥u-v∥-2*θ*inner(u-v)(w-v)+θ*θ*(∥w-v∥*∥w-v∥),
        rw abs_of_pos hθ₁, ring
      end,
    have eq₁ : ∥u-v∥^2-2*θ*inner(u-v)(w-v)+θ*θ*∥w-v∥^2=∥u-v∥^2+(θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)),
      by abel,
    rw [eq₁, le_add_iff_nonneg_right] at this,
    have eq₂ : θ*θ*∥w-v∥^2-2*θ*inner(u-v)(w-v)=θ*(θ*∥w-v∥^2-2*inner(u-v)(w-v)), ring,
    rw eq₂ at this,
    have := le_of_sub_nonneg (nonneg_of_mul_nonneg_left this hθ₁),
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
    exact calc
      ∥u - v∥ * ∥u - v∥ ≤ ∥u - v∥ * ∥u - v∥ - 2 * inner (u - v) ((w:F) - v) : by linarith
      ... ≤ ∥u - v∥^2 - 2 * inner (u - v) ((w:F) - v) + ∥(w:F) - v∥^2 :
        by { rw sq, refine le_add_of_nonneg_right _, exact sq_nonneg _ }
      ... = ∥(u - v) - (w - v)∥^2 : norm_sub_sq.symm
      ... = ∥u - w∥ * ∥u - w∥ :
        by { have : (u - v) - (w - v) = u - w, abel, rw [this, sq] } },
  { show (⨅ (w : K), ∥u - w∥) ≤ (λw:K, ∥u - w∥) ⟨v, hv⟩,
      apply cinfi_le, use 0, rintros y ⟨z, rfl⟩, exact norm_nonneg _ }
end

variables (K : submodule 𝕜 E)

/--
Existence of projections on complete subspaces.
Let `u` be a point in an inner product space, and let `K` be a nonempty complete subspace.
Then there exists a (unique) `v` in `K` that minimizes the distance `∥u - v∥` to `u`.
This point `v` is usually called the orthogonal projection of `u` onto `K`.
-/
theorem exists_norm_eq_infi_of_complete_subspace
  (h : is_complete (↑K : set E)) : ∀ u : E, ∃ v ∈ K, ∥u - v∥ = ⨅ w : (K : set E), ∥u - w∥ :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.module ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
  let K' : submodule ℝ E := submodule.restrict_scalars ℝ K,
  exact exists_norm_eq_infi_of_complete_convex ⟨0, K'.zero_mem⟩ h K'.convex
end

/--
Characterization of minimizers in the projection on a subspace, in the real case.
Let `u` be a point in a real inner product space, and let `K` be a nonempty subspace.
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`).
This is superceded by `norm_eq_infi_iff_inner_eq_zero` that gives the same conclusion over
any `is_R_or_C` field.
-/
theorem norm_eq_infi_iff_real_inner_eq_zero (K : submodule ℝ F) {u : F} {v : F}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set F), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫_ℝ = 0 :=
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
Then point `v` minimizes the distance `∥u - v∥` over points in `K` if and only if
for all `w ∈ K`, `⟪u - v, w⟫ = 0` (i.e., `u - v` is orthogonal to the subspace `K`)
-/
theorem norm_eq_infi_iff_inner_eq_zero {u : E} {v : E}
  (hv : v ∈ K) : ∥u - v∥ = (⨅ w : (↑K : set E), ∥u - w∥) ↔ ∀ w ∈ K, ⟪u - v, w⟫ = 0 :=
begin
  letI : inner_product_space ℝ E := inner_product_space.is_R_or_C_to_real 𝕜 E,
  letI : module ℝ E := restrict_scalars.module ℝ 𝕜 E,
  letI : is_scalar_tower ℝ 𝕜 E := restrict_scalars.is_scalar_tower _ _ _,
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
  rw [←sub_eq_zero, ←inner_self_eq_zero],
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
  ∥v∥ * ∥v∥ = ∥v - (orthogonal_projection_fn K v)∥ * ∥v - (orthogonal_projection_fn K v)∥
            + ∥orthogonal_projection_fn K v∥ * ∥orthogonal_projection_fn K v∥ :=
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
        rw [add_sub_comm, inner_add_left, orthogonal_projection_fn_inner_eq_zero _ w hw,
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
    change ∥orthogonal_projection_fn K x∥ ^ 2 ≤ ∥x∥ ^ 2,
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

/-- The orthogonal projection is the unique point in `K` with the
orthogonality property. -/
lemma eq_orthogonal_projection_of_mem_of_inner_eq_zero
  {u v : E} (hvm : v ∈ K) (hvo : ∀ w ∈ K, ⟪u - v, w⟫ = 0) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hvm hvo

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

/-- Orthogonal projection onto the `submodule.map` of a subspace. -/
lemma orthogonal_projection_map_apply {E E' : Type*} [inner_product_space 𝕜 E]
  [inner_product_space 𝕜 E'] (f : E ≃ₗᵢ[𝕜] E') (p : submodule 𝕜 E) [finite_dimensional 𝕜 p]
  (x : E') :
  (orthogonal_projection (p.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x : E')
  = f (orthogonal_projection p (f.symm x)) :=
begin
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero,
  { exact ⟨orthogonal_projection p (f.symm x), submodule.coe_mem _, by simp⟩, },
  rintros w ⟨a, ha, rfl⟩,
  suffices : inner (f (f.symm x - orthogonal_projection p (f.symm x))) (f a) = (0:𝕜),
  { simpa using this },
  rw f.inner_map_map,
  exact orthogonal_projection_inner_eq_zero _ _ ha,
end

/-- The orthogonal projection onto the trivial submodule is the zero map. -/
@[simp] lemma orthogonal_projection_bot : orthogonal_projection (⊥ : submodule 𝕜 E) = 0 :=
by ext

variables (K)

/-- The orthogonal projection has norm `≤ 1`. -/
lemma orthogonal_projection_norm_le : ∥orthogonal_projection K∥ ≤ 1 :=
linear_map.mk_continuous_norm_le _ (by norm_num) _

variables (𝕜)

lemma smul_orthogonal_projection_singleton {v : E} (w : E) :
  (∥v∥ ^ 2 : 𝕜) • (orthogonal_projection (𝕜 ∙ v) w : E) = ⟪v, w⟫ • v :=
begin
  suffices : ↑(orthogonal_projection (𝕜 ∙ v) ((∥v∥ ^ 2 : 𝕜) • w)) = ⟪v, w⟫ • v,
  { simpa using this },
  apply eq_orthogonal_projection_of_mem_of_inner_eq_zero,
  { rw submodule.mem_span_singleton,
    use ⟪v, w⟫ },
  { intros x hx,
    obtain ⟨c, rfl⟩ := submodule.mem_span_singleton.mp hx,
    have hv : ↑∥v∥ ^ 2 = ⟪v, v⟫ := by { norm_cast, simp [norm_sq_eq_inner] },
    simp [inner_sub_left, inner_smul_left, inner_smul_right, is_R_or_C.conj_div, mul_comm, hv,
      inner_product_space.conj_sym, hv] }
end

/-- Formula for orthogonal projection onto a single vector. -/
lemma orthogonal_projection_singleton {v : E} (w : E) :
  (orthogonal_projection (𝕜 ∙ v) w : E) = (⟪v, w⟫ / ∥v∥ ^ 2) • v :=
begin
  by_cases hv : v = 0,
  { rw [hv, eq_orthogonal_projection_of_eq_submodule submodule.span_zero_singleton],
    { simp },
    { apply_instance } },
  have hv' : ∥v∥ ≠ 0 := ne_of_gt (norm_pos_iff.mpr hv),
  have key : ((∥v∥ ^ 2 : 𝕜)⁻¹ * ∥v∥ ^ 2) • ↑(orthogonal_projection (𝕜 ∙ v) w)
              = ((∥v∥ ^ 2 : 𝕜)⁻¹ * ⟪v, w⟫) • v,
  { simp [mul_smul, smul_orthogonal_projection_singleton 𝕜 w] },
  convert key;
  field_simp [hv']
end

/-- Formula for orthogonal projection onto a single unit vector. -/
lemma orthogonal_projection_unit_singleton {v : E} (hv : ∥v∥ = 1) (w : E) :
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
      abel,
      },
    { simp only [add_sub_cancel'_right, eq_self_iff_true], }
  end,
  ..reflection_linear_equiv K }

variables {K}

/-- The result of reflecting. -/
lemma reflection_apply (p : E) : reflection K p = bit0 ↑(orthogonal_projection K p) - p := rfl

/-- Reflection is its own inverse. -/
@[simp] lemma reflection_symm : (reflection K).symm = reflection K := rfl

variables (K)

/-- Reflecting twice in the same subspace. -/
@[simp] lemma reflection_reflection (p : E) : reflection K (reflection K p) = p :=
(reflection K).left_inv p

/-- Reflection is involutive. -/
lemma reflection_involutive : function.involutive (reflection K) := reflection_reflection K

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
lemma reflection_map_apply {E E' : Type*} [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (K : submodule 𝕜 E) [finite_dimensional 𝕜 K] (x : E') :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) x = f (reflection K (f.symm x)) :=
by simp [bit0, reflection_apply, orthogonal_projection_map_apply f K x]

/-- Reflection in the `submodule.map` of a subspace. -/
lemma reflection_map {E E' : Type*} [inner_product_space 𝕜 E] [inner_product_space 𝕜 E']
  (f : E ≃ₗᵢ[𝕜] E') (K : submodule 𝕜 E) [finite_dimensional 𝕜 K] :
  reflection (K.map (f.to_linear_equiv : E →ₗ[𝕜] E')) = f.symm.trans ((reflection K).trans f) :=
linear_isometry_equiv.ext $ reflection_map_apply f K

/-- Reflection through the trivial subspace {0} is just negation. -/
@[simp] lemma reflection_bot : reflection (⊥ : submodule 𝕜 E) = linear_isometry_equiv.neg 𝕜 :=
by ext; simp [reflection_apply]

end reflection

section orthogonal

/-- If `K₁` is complete and contained in `K₂`, `K₁` and `K₁ᗮ ⊓ K₂` span `K₂`. -/
lemma submodule.sup_orthogonal_inf_of_is_complete {K₁ K₂ : submodule 𝕜 E} (h : K₁ ≤ K₂)
  (hc : is_complete (K₁ : set E)) : K₁ ⊔ (K₁ᗮ ⊓ K₂) = K₂ :=
begin
  ext x,
  rw submodule.mem_sup,
  rcases exists_norm_eq_infi_of_complete_subspace K₁ hc x with ⟨v, hv, hvm⟩,
  rw norm_eq_infi_iff_inner_eq_zero K₁ hv at hvm,
  split,
  { rintro ⟨y, hy, z, hz, rfl⟩,
    exact K₂.add_mem (h hy) hz.2 },
  { exact λ hx, ⟨v, hv, x - v, ⟨(K₁.mem_orthogonal' _).2 hvm, K₂.sub_mem hx (h hv)⟩,
                 add_sub_cancel'_right _ _⟩ }
end

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. -/
lemma submodule.sup_orthogonal_of_is_complete (h : is_complete (K : set E)) : K ⊔ Kᗮ = ⊤ :=
begin
  convert submodule.sup_orthogonal_inf_of_is_complete (le_top : K ≤ ⊤) h,
  simp
end

/-- If `K` is complete, `K` and `Kᗮ` span the whole space. Version using `complete_space`. -/
lemma submodule.sup_orthogonal_of_complete_space [complete_space K] : K ⊔ Kᗮ = ⊤ :=
submodule.sup_orthogonal_of_is_complete (complete_space_coe_iff_is_complete.mp ‹_›)

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
    { have hyz : ⟪z, y⟫ = 0 := by simp [hz y hy, inner_eq_zero_sym],
      simpa [inner_add_right, hyz] using hv z hz },
    simp [hy, hz'] },
  { intros hv w hw,
    rw inner_eq_zero_sym,
    exact hw v hv }
end

lemma submodule.orthogonal_orthogonal_eq_closure [complete_space E] :
  Kᗮᗮ = K.topological_closure :=
begin
  refine le_antisymm _ _,
  { convert submodule.orthogonal_orthogonal_monotone K.submodule_topological_closure,
    haveI : complete_space K.topological_closure :=
      K.is_closed_topological_closure.complete_space_coe,
    rw K.topological_closure.orthogonal_orthogonal },
  { exact K.topological_closure_minimal K.le_orthogonal_orthogonal Kᗮ.is_closed_orthogonal }
end

variables {K}

/-- If `K` is complete, `K` and `Kᗮ` are complements of each other. -/
lemma submodule.is_compl_orthogonal_of_is_complete (h : is_complete (K : set E)) : is_compl K Kᗮ :=
⟨K.orthogonal_disjoint, le_of_eq (submodule.sup_orthogonal_of_is_complete h).symm⟩

@[simp] lemma submodule.orthogonal_eq_bot_iff (hK : is_complete (K : set E)) :
  Kᗮ = ⊥ ↔ K = ⊤ :=
begin
  refine ⟨_, by { rintro rfl, exact submodule.top_orthogonal_eq_bot }⟩,
  intro h,
  have : K ⊔ Kᗮ = ⊤ := submodule.sup_orthogonal_of_is_complete hK,
  rwa [h, sup_comm, bot_sup_eq] at this,
end

/-- A point in `K` with the orthogonality property (here characterized in terms of `Kᗮ`) must be the
orthogonal projection. -/
lemma eq_orthogonal_projection_of_mem_orthogonal
  [complete_space K] {u v : E} (hv : v ∈ K) (hvo : u - v ∈ Kᗮ) :
  (orthogonal_projection K u : E) = v :=
eq_orthogonal_projection_fn_of_mem_of_inner_eq_zero hv (λ w, inner_eq_zero_sym.mp ∘ (hvo w))

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

/-- In a complete space `E`, the projection maps onto a complete subspace `K` and its orthogonal
complement sum to the identity. -/
lemma id_eq_sum_orthogonal_projection_self_orthogonal_complement
  [complete_space E] [complete_space K] :
  continuous_linear_map.id 𝕜 E
  = K.subtypeL.comp (orthogonal_projection K)
  + Kᗮ.subtypeL.comp (orthogonal_projection Kᗮ) :=
by { ext w, exact eq_sum_orthogonal_projection_self_orthogonal_complement K w }

/-- The orthogonal projection is self-adjoint. -/
lemma inner_orthogonal_projection_left_eq_right [complete_space E]
  [complete_space K] (u v : E) :
  ⟪↑(orthogonal_projection K u), v⟫ = ⟪u, orthogonal_projection K v⟫ :=
begin
  nth_rewrite 0 eq_sum_orthogonal_projection_self_orthogonal_complement K v,
  nth_rewrite 1 eq_sum_orthogonal_projection_self_orthogonal_complement K u,
  rw [inner_add_left, inner_add_right,
    submodule.inner_right_of_mem_orthogonal (submodule.coe_mem (orthogonal_projection K u))
      (submodule.coe_mem (orthogonal_projection Kᗮ v)),
    submodule.inner_left_of_mem_orthogonal (submodule.coe_mem (orthogonal_projection K v))
      (submodule.coe_mem (orthogonal_projection Kᗮ u))],
end

open finite_dimensional

/-- Given a finite-dimensional subspace `K₂`, and a subspace `K₁`
containined in it, the dimensions of `K₁` and the intersection of its
orthogonal subspace with `K₂` add to that of `K₂`. -/
lemma submodule.finrank_add_inf_finrank_orthogonal {K₁ K₂ : submodule 𝕜 E}
  [finite_dimensional 𝕜 K₂] (h : K₁ ≤ K₂) :
  finrank 𝕜 K₁ + finrank 𝕜 (K₁ᗮ ⊓ K₂ : submodule 𝕜 E) = finrank 𝕜 K₂ :=
begin
  haveI := submodule.finite_dimensional_of_le h,
  have hd := submodule.dim_sup_add_dim_inf_eq K₁ (K₁ᗮ ⊓ K₂),
  rw [←inf_assoc, (submodule.orthogonal_disjoint K₁).eq_bot, bot_inf_eq, finrank_bot,
      submodule.sup_orthogonal_inf_of_is_complete h
        (submodule.complete_of_finite_dimensional _)] at hd,
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
lemma submodule.finrank_add_finrank_orthogonal [finite_dimensional 𝕜 E] {K : submodule 𝕜 E} :
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

end orthogonal


section orthonormal_basis

/-! ### Existence of Hilbert basis, orthonormal basis, etc. -/

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
    let e := (∥x∥⁻¹ : 𝕜) • x,
    have he : ∥e∥ = 1 := by simp [e, norm_smul_inv_norm hx],
    have he' : e ∈ (span 𝕜 v)ᗮ := smul_mem' _ _ hx',
    have he'' : e ∉ v,
    { intros hev,
      have : e = 0,
      { have : e ∈ (span 𝕜 v) ⊓ (span 𝕜 v)ᗮ := ⟨subset_span hev, he'⟩,
        simpa [(span 𝕜 v).inf_orthogonal_eq_bot] using this },
      have : e ≠ 0 := hv.ne_zero ⟨e, hev⟩,
      contradiction },
    -- put this together with `v` to provide a candidate orthonormal basis for the whole space
    refine ⟨v.insert e, v.subset_insert e, ⟨_, _⟩, (v.ne_insert_of_not_mem he'').symm⟩,
    { -- show that the elements of `v.insert e` have unit length
      rintros ⟨a, ha'⟩,
      cases eq_or_mem_of_mem_insert ha' with ha ha,
      { simp [ha, he] },
      { exact hv.1 ⟨a, ha⟩ } },
    { -- show that the elements of `v.insert e` are orthogonal
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
        rw inner_eq_zero_sym,
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

/-- An orthonormal set in an `inner_product_space` is maximal, if and only if the closure of its
span is the whole space. -/
lemma maximal_orthonormal_iff_dense_span [complete_space E] (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ (span 𝕜 v).topological_closure = ⊤ :=
by rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hv, ← submodule.orthogonal_eq_top_iff,
  (span 𝕜 v).orthogonal_orthogonal_eq_closure]

/-- Any orthonormal subset can be extended to an orthonormal set whose span is dense. -/
lemma exists_subset_is_orthonormal_dense_span
  [complete_space E] (hv : orthonormal 𝕜 (coe : v → E)) :
  ∃ u ⊇ v, orthonormal 𝕜 (coe : u → E) ∧ (span 𝕜 u).topological_closure = ⊤ :=
begin
  obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv,
  rw maximal_orthonormal_iff_dense_span hu at hu_max,
  exact ⟨u, hus, hu, hu_max⟩
end

variables (𝕜 E)
/-- An inner product space admits an orthonormal set whose span is dense. -/
lemma exists_is_orthonormal_dense_span [complete_space E] :
  ∃ u : set E, orthonormal 𝕜 (coe : u → E) ∧ (span 𝕜 u).topological_closure = ⊤ :=
let ⟨u, hus, hu, hu_max⟩ := exists_subset_is_orthonormal_dense_span (orthonormal_empty 𝕜 E) in
⟨u, hu, hu_max⟩
variables {𝕜 E}

/-- An orthonormal set in a finite-dimensional `inner_product_space` is maximal, if and only if it
is a basis. -/
lemma maximal_orthonormal_iff_basis_of_finite_dimensional
  [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 (coe : v → E)) :
  (∀ u ⊇ v, orthonormal 𝕜 (coe : u → E) → u = v) ↔ ∃ b : basis v 𝕜 E, ⇑b = coe :=
begin
  rw maximal_orthonormal_iff_orthogonal_complement_eq_bot hv,
  have hv_compl : is_complete (span 𝕜 v : set E) := (span 𝕜 v).complete_of_finite_dimensional,
  rw submodule.orthogonal_eq_bot_iff hv_compl,
  have hv_coe : range (coe : v → E) = v := by simp,
  split,
  { refine λ h, ⟨basis.mk hv.linear_independent _, basis.coe_mk _ _⟩,
    convert h },
  { rintros ⟨h, coe_h⟩,
    rw [← h.span_eq, coe_h, hv_coe] }
end

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
lemma exists_subset_is_orthonormal_basis
  [finite_dimensional 𝕜 E] (hv : orthonormal 𝕜 (coe : v → E)) :
  ∃ (u ⊇ v) (b : basis u 𝕜 E), orthonormal 𝕜 b ∧ ⇑b = coe :=
begin
  obtain ⟨u, hus, hu, hu_max⟩ := exists_maximal_orthonormal hv,
  obtain ⟨b, hb⟩ := (maximal_orthonormal_iff_basis_of_finite_dimensional hu).mp hu_max,
  exact ⟨u, hus, b, by rwa hb, hb⟩
end

variables (𝕜 E)

/-- Index for an arbitrary orthonormal basis on a finite-dimensional `inner_product_space`. -/
def orthonormal_basis_index [finite_dimensional 𝕜 E] : set E :=
classical.some (exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E))

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
def orthonormal_basis [finite_dimensional 𝕜 E] :
  basis (orthonormal_basis_index 𝕜 E) 𝕜 E :=
(exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some

lemma orthonormal_basis_orthonormal [finite_dimensional 𝕜 E] :
  orthonormal 𝕜 (orthonormal_basis 𝕜 E) :=
(exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some_spec.1

@[simp] lemma coe_orthonormal_basis [finite_dimensional 𝕜 E] :
  ⇑(orthonormal_basis 𝕜 E) = coe :=
(exists_subset_is_orthonormal_basis (orthonormal_empty 𝕜 E)).some_spec.some_spec.some_spec.2

instance [finite_dimensional 𝕜 E] : fintype (orthonormal_basis_index 𝕜 E) :=
is_noetherian.fintype_basis_index (orthonormal_basis 𝕜 E)

variables {𝕜 E}

/-- An `n`-dimensional `inner_product_space` has an orthonormal basis indexed by `fin n`. -/
def fin_orthonormal_basis [finite_dimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  basis (fin n) 𝕜 E :=
have h : fintype.card (orthonormal_basis_index 𝕜 E) = n,
by rw [← finrank_eq_card_basis (orthonormal_basis 𝕜 E), hn],
(orthonormal_basis 𝕜 E).reindex (fintype.equiv_fin_of_card_eq h)

lemma fin_orthonormal_basis_orthonormal [finite_dimensional 𝕜 E] {n : ℕ} (hn : finrank 𝕜 E = n) :
  orthonormal 𝕜 (fin_orthonormal_basis hn) :=
suffices orthonormal 𝕜 (orthonormal_basis _ _ ∘ equiv.symm _),
by { simp only [fin_orthonormal_basis, basis.coe_reindex], assumption }, -- why doesn't simpa work?
(orthonormal_basis_orthonormal 𝕜 E).comp _ (equiv.injective _)

end orthonormal_basis

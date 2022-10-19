/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.specific_functions

/-!
# Arbitrary support

We show that any open set is the support of a smooth function taking values in `[0, 1]`
-/
open set metric topological_space function asymptotics
open_locale topological_space nnreal big_operators

@[to_additive]
lemma continuous.is_open_mul_support {α β : Type*} [topological_space α] [topological_space β]
  [t2_space β] [has_one β]
  {f : α → β} (hf : continuous f) : is_open (mul_support f) :=
is_open_ne_fun hf continuous_const

section
variables {α β E F : Type*}
  [pseudo_metric_space β]
  [normed_add_comm_group E] [normed_space ℝ E]
  [normed_add_comm_group F] [normed_space ℝ F] [complete_space F]

lemma cont_diff_iff_forall_nat_le
  {𝕜 : Type*} [nontrivially_normed_field 𝕜] {E F : Type*}
  [normed_add_comm_group E] [normed_space 𝕜 E]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  {f : E → F} {n : ℕ∞} :
  cont_diff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → cont_diff 𝕜 m f :=
begin
  simp_rw [← cont_diff_on_univ],
  exact cont_diff_on_iff_forall_nat_le
end

lemma summable.to_nnreal {f : α → ℝ} (hf : summable f) :
  summable (λ n, (f n).to_nnreal) :=
begin
  apply nnreal.summable_coe.1,
  refine summable_of_nonneg_of_le (λ n, nnreal.coe_nonneg _) (λ n, _) (summable_norm_iff.2 hf),
  simp only [le_abs_self, real.coe_to_nnreal', real.norm_eq_abs, max_le_iff, abs_nonneg, and_self]
end

lemma summable_of_summable_of_lipschitz_on_with
  {F : Type*} [normed_add_comm_group F] [complete_space F]
  {f : α → β → F} {s : set β} {x y : β}
  (hx : x ∈ s) (hy : y ∈ s) (hfx : summable (λ n, f n x)) {C : α → ℝ≥0}
  (hf : ∀ n, lipschitz_on_with (C n) (f n) s) (hC : summable C) :
  summable (λ n, f n y) :=
begin
  have A : ∀ n, ∥f n y - f n x∥ ≤ C n * dist y x,
  { assume n,
    rw ← dist_eq_norm,
    exact ((hf n).dist_le_mul _ hy _ hx) },
  have S : summable (λ n, f n y - f n x),
  { apply summable_of_norm_bounded _ _ A,
    exact (nnreal.summable_coe.2 hC).mul_right _ },
  convert hfx.add S,
  simp only [add_sub_cancel'_right],
end

/-- Consider a series of functions `∑' n, f n x` on a convex set. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
lemma summable_of_summable_has_fderiv_within_at
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  {s : set E} (hs : convex ℝ s)
  (hf : ∀ n x, x ∈ s → has_fderiv_within_at (f n) (f' n x) s x)
  (hf' : ∀ n x, x ∈ s → ∥f' n x∥ ≤ u n)
  {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : summable (λ n, f n x₀)) {x : E} (hx : x ∈ s) :
  summable (λ n, f n x) :=
begin
  have u_nonneg : ∀ n, 0 ≤ u n, from λ n, (norm_nonneg _).trans (hf' n x₀ hx₀),
  have hf'_nn : ∀ n x, x ∈ s → ∥f' n x∥₊ ≤ (u n).to_nnreal,
  { assume n x hx,
    rw [← nnreal.coe_le_coe, coe_nnnorm, real.coe_to_nnreal _ (u_nonneg n)],
    exact hf' n x hx },
  have L : ∀ n, lipschitz_on_with (u n).to_nnreal (f n) s,
    from λ n, hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (hf n) (hf'_nn n),
  exact summable_of_summable_of_lipschitz_on_with hx₀ hx hf0 L hu.to_nnreal,
end

/-- Consider a series of functions `∑' n, f n x` on a convex set. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
lemma has_fderiv_within_at_tsum
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  {s : set E} (hs : convex ℝ s)
  (hf : ∀ n x, x ∈ s → has_fderiv_within_at (f n) (f' n x) s x)
  (hf' : ∀ n x, x ∈ s → ∥f' n x∥ ≤ u n)
  {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : summable (λ n, f n x₀)) {x : E} (hx : x ∈ s) :
  has_fderiv_within_at (λ y, ∑' n, f n y) (∑' n, f' n x) s x :=
begin
  classical,
  have u_nonneg : ∀ n, 0 ≤ u n, from λ n, (norm_nonneg _).trans (hf' n x₀ hx₀),
  have hf'_nn : ∀ n x, x ∈ s → ∥f' n x∥₊ ≤ (u n).to_nnreal,
  { assume n x hx,
    rw [← nnreal.coe_le_coe, coe_nnnorm, real.coe_to_nnreal _ (u_nonneg n)],
    exact hf' n x hx },
  have L : ∀ n, lipschitz_on_with (u n).to_nnreal (f n) s,
    from λ n, hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le (hf n) (hf'_nn n),
  have S : ∀ y, y ∈ s → summable (λ n, f n y),
    from λ y hy, summable_of_summable_has_fderiv_within_at hu hs hf hf' hx₀ hf0 hy,
  simp only [has_fderiv_within_at, has_fderiv_at_filter, is_o, is_O_with],
  assume ε εpos,
  set δ : ℝ := ε / 3 with δ_def,
  have δpos : 0 < δ, { rw [δ_def], linarith },
  obtain ⟨t, ht⟩ : ∃ (t : finset α), ∑' (n : {n // n ∉ t}), u n < δ, from
    ((tendsto_order.1 (tendsto_tsum_compl_at_top_zero u)).2 _ δpos).exists,
  have A : is_O_with δ (𝓝[s] x)
    (λ y, ∑ n in t, f n y - ∑ n in t, f n x - (∑ n in t, f' n x) (y - x)) (λ (x' : E), x' - x),
  { have : has_fderiv_within_at (λ y, ∑ n in t, f n y) (∑ n in t, f' n x) s x,
      from has_fderiv_within_at.sum (λ n hn, (hf n x hx)),
    simp only [has_fderiv_within_at, has_fderiv_at_filter, is_o] at this,
    exact this δpos },
  filter_upwards [is_O_with_iff.1 A, self_mem_nhds_within] with y Hy hy,
  have YX : ∀ n, ∥f n y - f n x∥ ≤ u n * ∥y - x∥,
  { assume n,
    rw [← dist_eq_norm, ← dist_eq_norm],
    convert (L n).dist_le_mul _ hy _ hx,
    rw real.coe_to_nnreal _ (u_nonneg n) },
  calc
  ∥∑' (n : α), f n y - ∑' (n : α), f n x - (∑' (n : α), f' n x) (y - x)∥
  = ∥(∑ n in t, f n y - ∑ n in t, f n x - (∑ n in t, f' n x) (y - x))
    + (∑' n : {n // n ∉ t}, f n y - ∑' n : {n // n ∉ t}, f n x
        - (∑' n : {n // n ∉ t}, f' n x) (y - x))∥ :
    begin
      congr' 1,
      have C : summable (λ n, f' n x), from summable_of_norm_bounded _ hu (λ n, hf' n x hx),
      rw [← sum_add_tsum_subtype_compl (S y hy) t, ← sum_add_tsum_subtype_compl (S x hx) t,
        ← sum_add_tsum_subtype_compl C t],
      simp only [continuous_linear_map.add_apply],
      abel,
    end
  ... ≤ ∥∑ n in t, f n y - ∑ n in t, f n x - (∑ n in t, f' n x) (y - x)∥
    + ∥(∑' n : {n // n ∉ t}, f n y - ∑' n : {n // n ∉ t}, f n x )
        - (∑' n : {n // n ∉ t}, f' n x) (y - x)∥ :
    norm_add_le _ _
  ... ≤ δ * ∥y - x∥ + ∥∑' n : {n // n ∉ t}, f n y - ∑' n : {n // n ∉ t}, f n x∥
              + ∥∑' n : {n // n ∉ t}, f' n x∥ * ∥y - x∥ :
    begin
      rw add_assoc,
      apply add_le_add Hy,
      apply (norm_sub_le _ _).trans (add_le_add_left _ _),
      apply continuous_linear_map.le_op_norm,
    end
  ... ≤ δ * ∥y - x∥ + ∑' n : {n // n ∉ t}, ∥f n y - f n x∥ + (∑' n : {n // n ∉ t}, u n) * ∥y - x∥ :
    begin
      refine add_le_add (add_le_add_left _ _) _,
      { rw ← tsum_sub,
        rotate, { exact (S y hy).subtype _ }, { exact (S x hx).subtype _ },
        apply norm_tsum_le_tsum_norm,
        have : summable (λ n, ∥f n y - f n x∥),
          from summable_of_nonneg_of_le (λ n, norm_nonneg _) YX (hu.mul_right _),
        exact this.subtype _ },
      { have S' : summable (λ n, ∥f' n x∥),
          from summable_of_nonneg_of_le (λ n, norm_nonneg _) (λ n, hf' n x hx) hu,
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _),
        refine (norm_tsum_le_tsum_norm (S'.subtype _)).trans _,
        apply tsum_le_tsum,
        { assume n, exact hf' n x hx },
        { exact S'.subtype _ },
        { exact hu.subtype _ } }
    end
  ... ≤ δ * ∥y - x∥ + ∑' n : {n // n ∉ t}, u n * ∥y - x∥ + (∑' n : {n // n ∉ t}, u n) * ∥y - x∥ :
    begin
      refine add_le_add_right (add_le_add_left _ _) _,
      apply tsum_le_tsum,
      { assume n, apply YX },
      { have : summable (λ n, ∥f n y - f n x∥),
          from summable_of_nonneg_of_le (λ n, norm_nonneg _) YX (hu.mul_right _),
        exact this.subtype _ },
      { apply summable.mul_right,
        exact hu.subtype _ }
    end
  ... ≤ δ * ∥y - x∥ + δ * ∥y - x∥ + δ * ∥y - x∥ :
    begin
      rw [tsum_mul_right],
      refine add_le_add (add_le_add_left _ _) _;
      exact mul_le_mul_of_nonneg_right ht.le (norm_nonneg _),
    end
  ... = ε * ∥y - x∥ : by { rw [δ_def], ring }
end

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere. -/
lemma summable_of_summable_has_fderiv_at
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  (hf : ∀ n x, has_fderiv_at (f n) (f' n x) x) (hf' : ∀ n x, ∥f' n x∥ ≤ u n)
  {x₀ : E} (hf0 : summable (λ n, f n x₀)) (x : E) :
  summable (λ n, f n x) :=
begin
  simp_rw [← has_fderiv_within_at_univ] at hf,
  exact summable_of_summable_has_fderiv_within_at hu convex_univ (λ n x hx, hf n x)
    (λ n x hx, hf' n x) (mem_univ _) hf0 (mem_univ _),
end

/-- Consider a series of functions `∑' n, f n x`. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable and its derivative is the sum of the derivatives. -/
lemma has_fderiv_at_tsum
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  (hf : ∀ n x, has_fderiv_at (f n) (f' n x) x) (hf' : ∀ n x, ∥f' n x∥ ≤ u n)
  {x₀ : E} (hf0 : summable (λ n, f n x₀)) (x : E) :
  has_fderiv_at (λ y, ∑' n, f n y) (∑' n, f' n x) x :=
begin
  simp_rw [← has_fderiv_within_at_univ] at hf ⊢,
  exact has_fderiv_within_at_tsum hu convex_univ (λ n x hx, hf n x)
    (λ n x hx, hf' n x) (mem_univ _) hf0 (mem_univ _),
end

/-- Consider a series of functions `∑' n, f n x`. If all functions in the series are differentiable
with a summable bound on the derivatives, then the series is differentiable.
Note that our assumptions do not ensure the pointwise convergence, but if there is no pointwise
convergence then the series is zero everywhere so the result still holds. -/
lemma differentiable_tsum
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  (hf : ∀ n x, has_fderiv_at (f n) (f' n x) x) (hf' : ∀ n x, ∥f' n x∥ ≤ u n) :
  differentiable ℝ (λ y, ∑' n, f n y) :=
begin
  by_cases h : ∃ x₀, summable (λ n, f n x₀),
  { rcases h with ⟨x₀, hf0⟩,
    assume x,
    exact (has_fderiv_at_tsum hu hf hf' hf0 x).differentiable_at },
  { push_neg at h,
    have : (λ x, ∑' n, f n x) = 0,
    { ext1 x, exact tsum_eq_zero_of_not_summable (h x) },
    rw this,
    exact differentiable_const 0 }
end

lemma fderiv_tsum_apply {f : α → E → F} {u : α → ℝ} (hu : summable u)
  (hf : ∀ n, differentiable ℝ (f n)) (hf' : ∀ n x, ∥fderiv ℝ (f n) x∥ ≤ u n)
  {x₀ : E} (hf0 : summable (λ n, f n x₀)) (x : E) :
  fderiv ℝ (λ y, ∑' n, f n y) x = ∑' n, fderiv ℝ (f n) x :=
(has_fderiv_at_tsum hu (λ n x, (hf n x).has_fderiv_at) hf' hf0 _).fderiv

lemma fderiv_tsum {f : α → E → F} {u : α → ℝ} (hu : summable u)
  (hf : ∀ n, differentiable ℝ (f n)) (hf' : ∀ n x, ∥fderiv ℝ (f n) x∥ ≤ u n)
  {x₀ : E} (hf0 : summable (λ n, f n x₀)) :
  fderiv ℝ (λ y, ∑' n, f n y) = (λ x, ∑' n, fderiv ℝ (f n) x) :=
by { ext1 x, exact fderiv_tsum_apply hu hf hf' hf0 x}

lemma iterated_fderiv_tsum
  {f : ℕ → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → ℝ} (hu : summable u)
  (h'f : ∀ (k i : ℕ) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u i)
  {k : ℕ} (hk : (k : ℕ∞) ≤ N) :
  iterated_fderiv ℝ k (λ y, ∑' n, f n y) = (λ x, ∑' n, iterated_fderiv ℝ k (f n) x) :=
begin
  induction k with k IH,
  { ext1 x,
    simp_rw [iterated_fderiv_zero_eq_comp],
    exact (continuous_multilinear_curry_fin0 ℝ E F).symm.to_continuous_linear_equiv.map_tsum },
  { have h'k : (k : ℕ∞) < N,
      from lt_of_lt_of_le (with_top.coe_lt_coe.2 (nat.lt_succ_self _)) hk,
    have A : summable (λ n, iterated_fderiv ℝ k (f n) 0),
      from summable_of_norm_bounded u hu (λ n, h'f k n 0 h'k.le),
    simp_rw [iterated_fderiv_succ_eq_comp_left, IH h'k.le],
    rw fderiv_tsum hu (λ n, (hf n).differentiable_iterated_fderiv h'k) _ A,
    { ext1 x,
      exact (continuous_multilinear_curry_left_equiv ℝ (λ (i : fin (k + 1)), E) F)
        .to_continuous_linear_equiv.map_tsum },
    { assume n x,
      simpa only [iterated_fderiv_succ_eq_comp_left, linear_isometry_equiv.norm_map]
        using h'f k.succ n x hk } }
end

lemma iterated_fderiv_tsum_apply
  {f : ℕ → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → ℝ} (hu : summable u)
  (h'f : ∀ (k i : ℕ) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u i)
  {k : ℕ} (hk : (k : ℕ∞) ≤ N) (x : E) :
  iterated_fderiv ℝ k (λ y, ∑' n, f n y) x = ∑' n, iterated_fderiv ℝ k (f n) x :=
by rw iterated_fderiv_tsum hf hu h'f hk

lemma cont_diff_tsum
  {f : ℕ → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → ℝ} (hu : summable u)
  (h'f : ∀ (k i : ℕ) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u i) :
  cont_diff ℝ N (λ x, ∑' i, f i x) :=
begin
  rw cont_diff_iff_continuous_differentiable,
  split,
  sorry,
  { assume m hm,
    rw iterated_fderiv_tsum hf hu h'f hm.le,
    have : ∀ n x, has_fderiv_at (iterated_fderiv ℝ m (f n)) (iterated_fderiv ℝ (m+1) (f n) x) x

  }
end

#exit

lemma cont_diff_tsum_of_eventually
  {f : ℕ → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → ℝ} (hu : summable u)
  (h'f : ∀ (k : ℕ), (k : ℕ∞) ≤ N → ∀ᶠ i in (filter.at_top : filter ℕ), ∀ (x : E),
     ∥iterated_fderiv ℝ k (f i) x∥ ≤ u i) :
  cont_diff ℝ N (λ x, ∑' i, f i x) :=
begin
  apply cont_diff_iff_forall_nat_le.2 (λ m hm, _),
  simp only [nat.cast_with_bot, filter.eventually_at_top, ge_iff_le] at h'f,
  choose! d hd using h'f,
  obtain ⟨D, hD⟩ : ∃ D, ∀ k, k ≤ m → d k < D,
  { let D := (finset.image d (finset.range (m+1))).max'
      (by simp only [finset.nonempty.image_iff, finset.nonempty_range_iff, ne.def, nat.succ_ne_zero,
        not_false_iff]) + 1,
    refine ⟨D, λ k hk, lt_of_le_of_lt
      (finset.le_max' _ _ (finset.mem_image_of_mem _ _)) (nat.lt_succ_self _)⟩,
    rw [finset.mem_range],
    exact nat.lt_succ_iff.2 hk },
  have A : ∀ (k i : ℕ) (x : E), k ≤ m → D ≤ i → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u i,
  { assume k i x hk hi,
    exact hd k (le_trans (with_top.coe_le_coe.2 hk) hm) i ((hD k hk).le.trans hi) x },
  have S : (λ x, ∑' i, f i x) = (λ x, ∑ i in finset.range D, f i x) + (λ x, ∑' i, f (i + D) x),
  { ext x,
    refine (sum_add_tsum_nat_add _ _).symm,
    refine summable_of_norm_bounded_eventually _ hu _,
    rw nat.cofinite_eq_at_top,
    simp only [filter.eventually_at_top, ge_iff_le],
    exact ⟨D, λ n hn, by simpa only [norm_iterated_fderiv_zero] using A 0 n x (zero_le _) hn⟩ },
  rw S,
  apply (cont_diff.sum (λ i hi, (hf i).of_le hm)).add,
  refine cont_diff_tsum (λ i, (hf (i + D)).of_le hm) ((summable_nat_add_iff D).2 hu) _,
  assume k i hk x,
  apply A k (i + D) x (with_top.coe_le_coe.1 hk) le_add_self,
end

variables {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [finite_dimensional ℝ E]

theorem exists_smooth_support_subset {s : set E} {x : E} (hs : s ∈ 𝓝 x) :
  ∃ (f : E → ℝ), f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1 ∧ f x = 1 :=
begin
  obtain ⟨d, d_pos, hd⟩ : ∃ (d : ℝ) (hr : 0 < d), euclidean.ball x d ⊆ s,
    from euclidean.nhds_basis_ball.mem_iff.1 hs,
  let c : cont_diff_bump_of_inner (to_euclidean x) :=
  { r := d/2,
    R := d,
    r_pos := half_pos d_pos,
    r_lt_R := half_lt_self d_pos },
  let f : E → ℝ := c ∘ to_euclidean,
  have f_supp : f.support ⊆ euclidean.ball x d,
  { assume y hy,
    have : to_euclidean y ∈ function.support c,
      by simpa only [f, function.mem_support, function.comp_app, ne.def] using hy,
    rwa c.support_eq at this },
  refine ⟨f, f_supp.trans hd, _, _, _, _⟩,
  { refine is_compact_of_is_closed_bounded is_closed_closure _,
    have : bounded (euclidean.closed_ball x d), from euclidean.is_compact_closed_ball.bounded,
    apply this.mono _,
    refine (is_closed.closure_subset_iff euclidean.is_closed_closed_ball).2 _,
    exact f_supp.trans euclidean.ball_subset_closed_ball },
  { apply c.cont_diff.comp,
    exact continuous_linear_equiv.cont_diff _ },
  { rintros t ⟨y, rfl⟩,
    exact ⟨c.nonneg, c.le_one⟩ },
  { apply c.one_of_mem_closed_ball,
    apply mem_closed_ball_self,
    exact (half_pos d_pos).le }
end

theorem is_open.exists_smooth_support_eq {s : set E} (hs : is_open s) :
  ∃ (f : E → ℝ), f.support = s ∧ cont_diff ℝ ⊤ f ∧ set.range f ⊆ set.Icc 0 1 :=
begin
  rcases eq_empty_or_nonempty s with rfl|h's,
  { exact ⟨(λ x, 0), function.support_zero, cont_diff_const,
      by simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩ },
  let ι := {f : E → ℝ // f.support ⊆ s ∧ has_compact_support f ∧ cont_diff ℝ ⊤ f ∧
    range f ⊆ Icc 0 1},
  obtain ⟨T, T_count, hT⟩ : ∃ T : set ι, T.countable ∧ (⋃ f ∈ T, support (f : E → ℝ)) = s,
  { have : (⋃ (f : ι), (f : E → ℝ).support) = s,
    { refine subset.antisymm (Union_subset (λ f, f.2.1)) _,
      assume x hx,
      rcases exists_smooth_support_subset (hs.mem_nhds hx) with ⟨f, hf⟩,
      let g : ι := ⟨f, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩,
      have : x ∈ support (g : E → ℝ),
        by simp only [hf.2.2.2.2, subtype.coe_mk, mem_support, ne.def, one_ne_zero, not_false_iff],
      exact mem_Union_of_mem _ this },
    simp_rw ← this,
    apply is_open_Union_countable,
    rintros ⟨f, hf⟩,
    exact hf.2.2.1.continuous.is_open_support },
  obtain ⟨g0, hg⟩ : ∃ (g0 : ℕ → ι), T = range g0,
  { apply countable.exists_eq_range T_count,
    rcases eq_empty_or_nonempty T with rfl|hT,
    { simp only [Union_false, Union_empty] at hT,
      simp only [←hT, not_nonempty_empty] at h's,
      exact h's.elim },
    { exact hT } },
  let g : ℕ → E → ℝ := λ n, (g0 n).1,
  have g_s : ∀ n, support (g n) ⊆ s := λ n, (g0 n).2.1,
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n),
  { assume x hx,
    rw ← hT at hx,
    obtain ⟨i, iT, hi⟩ : ∃ (i : ι) (hi : i ∈ T), x ∈ support (i : E → ℝ),
      by simpa only [mem_Union] using hx,
    rw [hg, mem_range] at iT,
    rcases iT with ⟨n, hn⟩,
    rw ← hn at hi,
    exact ⟨n, hi⟩ },
  have g_smooth : ∀ n, cont_diff ℝ ⊤ (g n) := λ n, (g0 n).2.2.2.1,
  have g_comp_supp : ∀ n, has_compact_support (g n) := λ n, (g0 n).2.2.1,
  have g_nonneg : ∀ n x, 0 ≤ g n x,
    from λ n x, ((g0 n).2.2.2.2 (mem_range_self x)).1,
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
    ∃ (δ : ℕ → ℝ≥0), (∀ (i : ℕ), 0 < δ i) ∧ ∃ (c : nnreal), has_sum δ c ∧ c < 1,
    from nnreal.exists_pos_sum_of_countable one_ne_zero ℕ,
  have : ∀ (n : ℕ), ∃ (r : ℝ),
    0 < r ∧ ∀ i ≤ n, ∀ x, ∥iterated_fderiv ℝ i (r • g n) x∥ ≤ δ n,
  { assume n,
    have : ∀ i, ∃ R, ∀ x, ∥iterated_fderiv ℝ i (λ x, g n x) x∥ ≤ R,
    { assume i,
      have : bdd_above (range (λ x, ∥iterated_fderiv ℝ i (λ (x : E), g n x) x∥)),
      { apply ((g_smooth n).continuous_iterated_fderiv le_top).norm
          .bdd_above_range_of_has_compact_support,
        apply has_compact_support.comp_left _ norm_zero,
        apply (g_comp_supp n).iterated_fderiv },
      rcases this with ⟨R, hR⟩,
      exact ⟨R, λ x, hR (mem_range_self _)⟩ },
    choose R hR using this,
    let M := max (((finset.range (n+1)).image R).max' (by simp)) 1,
    have M_pos : 0 < M := zero_lt_one.trans_le (le_max_right _ _),
    have δnpos : 0 < δ n := δpos n,
    have IR : ∀ i ≤ n, R i ≤ M,
    { assume i hi,
      refine le_trans _ (le_max_left _ _),
      apply finset.le_max',
      apply finset.mem_image_of_mem,
      simp only [finset.mem_range],
      linarith },
    refine ⟨M⁻¹ * δ n, by positivity, λ i hi x, _⟩,
    calc ∥iterated_fderiv ℝ i ((M⁻¹ * δ n) • g n) x∥
        = ∥(M⁻¹ * δ n) • iterated_fderiv ℝ i (g n) x∥ :
      by { rw iterated_fderiv_const_smul_apply, exact (g_smooth n).of_le le_top }
    ... = M⁻¹ * δ n * ∥iterated_fderiv ℝ i (g n) x∥ :
      by { rw [norm_smul, real.norm_of_nonneg], positivity }
    ... ≤ M⁻¹ * δ n * M :
      mul_le_mul_of_nonneg_left ((hR i x).trans (IR i hi)) (by positivity)
    ... = δ n : by field_simp [M_pos.ne'] },
  choose r rpos hr using this,
  have S : ∀ x, summable (λ n, (r n • g n) x),
  { assume x,
    refine summable_of_nnnorm_bounded _ δc.summable (λ n, _),
    rw [← nnreal.coe_le_coe, coe_nnnorm],
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) x },
  refine ⟨λ x, (∑' n, (r n • g n) x), _, _, _⟩,
  { apply subset.antisymm,
    { assume x hx,
      simp only [pi.smul_apply, algebra.id.smul_eq_mul, mem_support, ne.def] at hx,
      contrapose! hx,
      have : ∀ n, g n x = 0,
      { assume n,
        contrapose! hx,
        exact g_s n hx },
      simp only [this, mul_zero, tsum_zero] },
    { assume x hx,
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n), from s_g x hx,
      have I : 0 < r n * g n x,
        from mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (ne.symm hn)),
      exact ne_of_gt (tsum_pos (S x) (λ i, mul_nonneg (rpos i).le (g_nonneg i x)) n I) } },
  { refine cont_diff_tsum (λ n, (g_smooth n).const_smul _) (nnreal.has_sum_coe.2 δc).summable _,
    assume i hi,
    simp only [pi.smul_apply, algebra.id.smul_eq_mul, filter.eventually_at_top, ge_iff_le],
    exact ⟨i, λ n hn x, hr _ _ hn _⟩ },
  { rintros - ⟨y, rfl⟩,
    refine ⟨tsum_nonneg (λ n, mul_nonneg (rpos n).le (g_nonneg n y)), le_trans _ c_lt.le⟩,
    have A : has_sum (λ n, (δ n : ℝ)) c, from nnreal.has_sum_coe.2 δc,
    rw ← A.tsum_eq,
    apply tsum_le_tsum _ (S y) A.summable,
    assume n,
    apply (le_abs_self _).trans,
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) y }
end

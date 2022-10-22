/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.uniform_limits_deriv

/-!
# Smoothness of series

We show that series of functions are continuous, or differentiable, or smooth, when each individual
function in the series is and additionally suitable uniform summable bounds are satisfied.

More specifically,
* `continuous_tsum` ensures that a series of continuous functions is continuous.
* `differentiable_tsum` ensures that a series of differentiable functions is differentiable.
* `cont_diff_tsum` ensures that a series of smooth functions is smooth.

We also give versions of these statements which are localized to a set.
-/

open set metric topological_space function asymptotics filter
open_locale topological_space nnreal big_operators

variables {α β E F : Type*}
  [normed_add_comm_group E] [normed_space ℝ E]
  [normed_add_comm_group F] [complete_space F]

/-! ### Continuity -/

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with general index set. -/
lemma tendsto_uniformly_on_tsum {f : α → β → F} {u : α → ℝ} (hu : summable u) {s : set β}
  (hfu : ∀ n x, x ∈ s → ∥f n x∥ ≤ u n) :
  tendsto_uniformly_on (λ (t : finset α), (λ x, ∑ n in t, f n x)) (λ x, ∑' n, f n x) at_top s :=
begin
  refine tendsto_uniformly_on_iff.2 (λ ε εpos, _),
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_at_top_zero u)).2 _ εpos] with t ht x hx,
  have A : summable (λ n, ∥f n x∥),
    from summable_of_nonneg_of_le (λ n, norm_nonneg _) (λ n, hfu n x hx) hu,
  rw [dist_eq_norm, ← sum_add_tsum_subtype_compl (summable_of_summable_norm A) t, add_sub_cancel'],
  apply lt_of_le_of_lt _ ht,
  apply (norm_tsum_le_tsum_norm (A.subtype _)).trans,
  exact tsum_le_tsum (λ n, hfu _ _ hx) (A.subtype _) (hu.subtype _)
end

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version relative to a set, with index set `ℕ`. -/
lemma tendsto_uniformly_on_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : summable u) {s : set β}
  (hfu : ∀ n x, x ∈ s → ∥f n x∥ ≤ u n) :
  tendsto_uniformly_on (λ N, (λ x, ∑ n in finset.range N, f n x)) (λ x, ∑' n, f n x) at_top s :=
λ v hv, tendsto_finset_range.eventually (tendsto_uniformly_on_tsum hu hfu v hv)

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with general index set. -/
lemma tendsto_uniformly_tsum {f : α → β → F} {u : α → ℝ} (hu : summable u)
  (hfu : ∀ n x, ∥f n x∥ ≤ u n) :
  tendsto_uniformly (λ (t : finset α), (λ x, ∑ n in t, f n x)) (λ x, ∑' n, f n x) at_top :=
by { rw ← tendsto_uniformly_on_univ, exact tendsto_uniformly_on_tsum hu (λ n x hx, hfu n x) }

/-- An infinite sum of functions with summable sup norm is the uniform limit of its partial sums.
Version with index set `ℕ`. -/
lemma tendsto_uniformly_tsum_nat {f : ℕ → β → F} {u : ℕ → ℝ} (hu : summable u)
  (hfu : ∀ n x, ∥f n x∥ ≤ u n) :
  tendsto_uniformly (λ N, (λ x, ∑ n in finset.range N, f n x)) (λ x, ∑' n, f n x) at_top :=
λ v hv, tendsto_finset_range.eventually (tendsto_uniformly_tsum hu hfu v hv)

/-- An infinite sum of functions with summable sup norm is continuous on a set if each individual
function is. -/
lemma continuous_on_tsum [topological_space β]
  {f : α → β → F} {s : set β} (hf : ∀ i, continuous_on (f i) s) {u : α → ℝ} (hu : summable u)
  (hfu : ∀ n x, x ∈ s → ∥f n x∥ ≤ u n) :
  continuous_on (λ x, ∑' n, f n x) s :=
begin
  classical,
  refine (tendsto_uniformly_on_tsum hu hfu).continuous_on (eventually_of_forall _),
  assume t,
  exact continuous_on_finset_sum _ (λ i hi, hf i),
end

/-- An infinite sum of functions with summable sup norm is continuous if each individual
function is. -/
lemma continuous_tsum [topological_space β]
  {f : α → β → F} (hf : ∀ i, continuous (f i)) {u : α → ℝ} (hu : summable u)
  (hfu : ∀ n x, ∥f n x∥ ≤ u n) :
  continuous (λ x, ∑' n, f n x) :=
begin
  simp_rw [continuous_iff_continuous_on_univ] at hf ⊢,
  exact continuous_on_tsum hf hu (λ n x hx, hfu n x),
end


/-! ### Differentiability -/

lemma summable_of_summable_of_lipschitz_on_with [pseudo_metric_space β]
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

variables [normed_space ℝ F]

/-- Consider a series of functions `∑' n, f n x` on a convex set. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series converges everywhere on the set. -/
lemma summable_of_summable_has_fderiv_at
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  {s : set E} (hs : convex ℝ s)
  (hf : ∀ n x, x ∈ s → has_fderiv_at (f n) (f' n x) x)
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
    from λ n, hs.lipschitz_on_with_of_nnnorm_has_fderiv_within_le
      (λ x hx, (hf n x hx).has_fderiv_within_at) (hf'_nn n),
  exact summable_of_summable_of_lipschitz_on_with hx₀ hx hf0 L hu.to_nnreal,
end

/-- Consider a series of functions `∑' n, f n x` on a convex set. If the series converges at a
point, and all functions in the series are differentiable with a summable bound on the derivatives,
then the series is differentiable on the set and its derivative is the sum of the derivatives. -/
lemma has_fderiv_within_at_tsum
  {f : α → E → F} {f' : α → E → (E →L[ℝ] F)} {u : α → ℝ} (hu : summable u)
  {s : set E} (hs : convex ℝ s) (h's : is_open s)
  (hf : ∀ n x, x ∈ s → has_fderiv_at (f n) (f' n x) x)
  (hf' : ∀ n x, x ∈ s → ∥f' n x∥ ≤ u n)
  {x₀ : E} (hx₀ : x₀ ∈ s) (hf0 : summable (λ n, f n x₀)) {x : E} (hx : x ∈ s) :
  has_fderiv_at (λ y, ∑' n, f n y) (∑' n, f' n x) x :=
begin
  classical,
  apply has_fderiv_at_of_tendsto_uniformly_on h's (tendsto_uniformly_on_tsum hu hf') _ _ _ hx,
end

#exit

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


/-! ### Higher smoothness -/

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
lemma iterated_fderiv_tsum
  {f : α → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → α → ℝ}
  (hu : ∀ (k : ℕ), (k : ℕ∞) ≤ N → summable (u k))
  (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i)
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
      from summable_of_norm_bounded (u k) (hu k h'k.le) (λ n, h'f k n 0 h'k.le),
    simp_rw [iterated_fderiv_succ_eq_comp_left, IH h'k.le],
    rw fderiv_tsum (hu _ hk) (λ n, (hf n).differentiable_iterated_fderiv h'k) _ A,
    { ext1 x,
      exact (continuous_multilinear_curry_left_equiv ℝ (λ (i : fin (k + 1)), E) F)
        .to_continuous_linear_equiv.map_tsum },
    { assume n x,
      simpa only [iterated_fderiv_succ_eq_comp_left, linear_isometry_equiv.norm_map]
        using h'f k.succ n x hk } }
end

/-- Consider a series of smooth functions, with summable uniform bounds on the successive
derivatives. Then the iterated derivative of the sum is the sum of the iterated derivative. -/
lemma iterated_fderiv_tsum_apply
  {f : α → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → α → ℝ}
  (hu : ∀ (k : ℕ), (k : ℕ∞) ≤ N → summable (u k))
  (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i)
  {k : ℕ} (hk : (k : ℕ∞) ≤ N) (x : E) :
  iterated_fderiv ℝ k (λ y, ∑' n, f n y) x = ∑' n, iterated_fderiv ℝ k (f n) x :=
by rw iterated_fderiv_tsum hf hu h'f hk

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N`. Then the series is also `C^N`. -/
lemma cont_diff_tsum
  {f : α → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → α → ℝ}
  (hu : ∀ (k : ℕ), (k : ℕ∞) ≤ N → summable (u k))
  (h'f : ∀ (k : ℕ) (i : α) (x : E), (k : ℕ∞) ≤ N → ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i) :
  cont_diff ℝ N (λ x, ∑' i, f i x) :=
begin
  rw cont_diff_iff_continuous_differentiable,
  split,
  { assume m hm,
    rw iterated_fderiv_tsum hf hu h'f hm,
    refine continuous_tsum _ (hu m hm) _,
    { assume i,
      exact cont_diff.continuous_iterated_fderiv hm (hf i) },
    { assume n x,
      exact h'f _ _ _ hm } },
  { assume m hm,
    have h'm : ((m+1 : ℕ) : ℕ∞) ≤ N,
      by simpa only [enat.coe_add, nat.cast_with_bot, enat.coe_one] using enat.add_one_le_of_lt hm,
    rw iterated_fderiv_tsum hf hu h'f hm.le,
    have A : ∀ n x, has_fderiv_at (iterated_fderiv ℝ m (f n))
      (fderiv ℝ (iterated_fderiv ℝ m (f n)) x) x, from λ n x,
        (cont_diff.differentiable_iterated_fderiv hm (hf n)).differentiable_at.has_fderiv_at,
    apply differentiable_tsum (hu _ h'm) A (λ n x, _),
    rw [fderiv_iterated_fderiv, linear_isometry_equiv.norm_map],
    exact h'f _ _ _ h'm }
end

/-- Consider a series of functions `∑' i, f i x`. Assume that each individual function `f i` is of
class `C^N`, and moreover there is a uniform summable upper bound on the `k`-th derivative
for each `k ≤ N` (except maybe for finitely many `i`s). Then the series is also `C^N`. -/
lemma cont_diff_tsum_of_eventually
  {f : α → E → F} {N : ℕ∞} (hf : ∀ i, cont_diff ℝ N (f i)) {u : ℕ → α → ℝ}
  (hu : ∀ (k : ℕ), (k : ℕ∞) ≤ N → summable (u k))
  (h'f : ∀ (k : ℕ), (k : ℕ∞) ≤ N → ∀ᶠ i in (filter.cofinite : filter α), ∀ (x : E),
     ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i) :
  cont_diff ℝ N (λ x, ∑' i, f i x) :=
begin
  classical,
  apply cont_diff_iff_forall_nat_le.2 (λ m hm, _),
  let t : set α :=
    {i : α | ¬∀ (k : ℕ), k ∈ finset.range (m + 1) → ∀ x, ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i},
  have ht : set.finite t,
  { have A : ∀ᶠ i in (filter.cofinite : filter α), ∀ (k : ℕ), k ∈ finset.range (m+1) →
      ∀ (x : E), ∥iterated_fderiv ℝ k (f i) x∥ ≤ u k i,
    { rw eventually_all_finset,
      assume i hi,
      apply h'f,
      simp only [finset.mem_range_succ_iff] at hi,
      exact (with_top.coe_le_coe.2 hi).trans hm },
    exact eventually_cofinite.2 A },
  let T : finset α := ht.to_finset,
  have : (λ x, ∑' i, f i x) = (λ x, ∑ i in T, f i x) + (λ x, ∑' i : {i // i ∉ T}, f i x),
  { ext1 x,
    refine (sum_add_tsum_subtype_compl _ T).symm,
    refine summable_of_norm_bounded_eventually _ (hu 0 (zero_le _)) _,
    filter_upwards [h'f 0 (zero_le _)] with i hi,
    simpa only [norm_iterated_fderiv_zero] using hi x },
  rw this,
  apply (cont_diff.sum (λ i hi, (hf i).of_le hm)).add,
  have h'u : ∀ (k : ℕ), (k : ℕ∞) ≤ m → summable ((u k) ∘ (coe : {i // i ∉ T} → α)),
    from λ k hk, (hu k (hk.trans hm)).subtype _,
  refine cont_diff_tsum (λ i, (hf i).of_le hm) h'u _,
  rintros k ⟨i, hi⟩ x hk,
  dsimp,
  simp only [finite.mem_to_finset, mem_set_of_eq, finset.mem_range, not_forall, not_le, exists_prop,
    not_exists, not_and, not_lt] at hi,
  exact hi k (nat.lt_succ_iff.2 (with_top.coe_le_coe.1 hk)) x,
end

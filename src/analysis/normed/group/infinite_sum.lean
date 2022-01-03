/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Heather Macbeth, Johannes Hölzl, Yury Kudryashov
-/
import analysis.normed.group.basic
import topology.instances.nnreal

/-!
# Infinite sums in (semi)normed groups

In a complete (semi)normed group,

- `summable_iff_vanishing_norm`: a series `∑' i, f i` is summable if and only if for any `ε > 0`,
  there exists a finite set `s` such that the sum `∑ i in t, f i` over any finite set `t` disjoint
  with `s` has norm less than `ε`;

- `summable_of_norm_bounded`, `summable_of_norm_bounded_eventually`: if `∥f i∥` is bounded above by
  a summable series `∑' i, g i`, then `∑' i, f i` is summable as well; the same is true if the
  inequality hold only off some finite set.

- `tsum_of_norm_bounded`, `has_sum.norm_le_of_bounded`: if `∥f i∥ ≤ g i`, where `∑' i, g i` is a
  summable series, then `∥∑' i, f i∥ ≤ ∑' i, g i`.

## Tags

infinite series, absolute convergence, normed group
-/

open_locale classical big_operators topological_space nnreal
open finset filter metric

variables {ι α E F : Type*} [semi_normed_group E] [semi_normed_group F]

lemma cauchy_seq_finset_iff_vanishing_norm {f : ι → E} :
  cauchy_seq (λ s : finset ι, ∑ i in s, f i) ↔
    ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
begin
  rw [cauchy_seq_finset_iff_vanishing, nhds_basis_ball.forall_iff],
  { simp only [ball_zero_eq, set.mem_set_of_eq] },
  { rintros s t hst ⟨s', hs'⟩,
    exact ⟨s', λ t' ht', hst $ hs' _ ht'⟩ }
end

lemma summable_iff_vanishing_norm [complete_space E] {f : ι → E} :
  summable f ↔ ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing_norm]

lemma cauchy_seq_finset_of_norm_bounded_eventually {f : ι → E} {g : ι → ℝ} (hg : summable g)
  (h : ∀ᶠ i in cofinite, ∥f i∥ ≤ g i) : cauchy_seq (λ s, ∑ i in s, f i) :=
begin
  refine cauchy_seq_finset_iff_vanishing_norm.2 (λ ε hε, _),
  rcases summable_iff_vanishing_norm.1 hg ε hε with ⟨s, hs⟩,
  refine ⟨s ∪ h.to_finset, λ t ht, _⟩,
  have : ∀ i ∈ t, ∥f i∥ ≤ g i,
  { intros i hi,
    simp only [disjoint_left, mem_union, not_or_distrib, h.mem_to_finset, set.mem_compl_iff,
      not_not] at ht,
    exact (ht hi).2 },
  calc ∥∑ i in t, f i∥ ≤ ∑ i in t, g i    : norm_sum_le_of_le _ this
                    ... ≤ ∥∑ i in t, g i∥ : le_abs_self _
                    ... < ε               : hs _ (ht.mono_right le_sup_left),
end

lemma cauchy_seq_finset_of_norm_bounded {f : ι → E} (g : ι → ℝ) (hg : summable g)
  (h : ∀i, ∥f i∥ ≤ g i) : cauchy_seq (λ s : finset ι, ∑ i in s, f i) :=
cauchy_seq_finset_of_norm_bounded_eventually hg $ eventually_of_forall h

lemma cauchy_seq_finset_of_summable_norm {f : ι → E} (hf : summable (λa, ∥f a∥)) :
  cauchy_seq (λ s : finset ι, ∑ a in s, f a) :=
cauchy_seq_finset_of_norm_bounded _ hf (assume i, le_refl _)

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
lemma has_sum_of_subseq_of_summable {f : ι → E} (hf : summable (λa, ∥f a∥))
  {s : α → finset ι} {p : filter α} [ne_bot p]
  (hs : tendsto s p at_top) {a : E} (ha : tendsto (λ b, ∑ i in s b, f i) p (𝓝 a)) :
  has_sum f a :=
tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

lemma has_sum_iff_tendsto_nat_of_summable_norm {f : ℕ → E} {a : E} (hf : summable (λi, ∥f i∥)) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
⟨λ h, h.tendsto_sum_nat,
λ h, has_sum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded
  [complete_space E] {f : ι → E} (g : ι → ℝ) (hg : summable g) (h : ∀i, ∥f i∥ ≤ g i) :
  summable f :=
by { rw summable_iff_cauchy_seq_finset, exact cauchy_seq_finset_of_norm_bounded g hg h }

lemma has_sum.norm_le_of_bounded {f : ι → E} {g : ι → ℝ} {a : E} {b : ℝ}
  (hf : has_sum f a) (hg : has_sum g b) (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥a∥ ≤ b :=
le_of_tendsto_of_tendsto' hf.norm hg $ λ s, norm_sum_le_of_le _ $ λ i hi, h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma tsum_of_norm_bounded {f : ι → E} {g : ι → ℝ} {a : ℝ} (hg : has_sum g a)
  (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥∑' i : ι, f i∥ ≤ a :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.norm_le_of_bounded hg h },
  { rw [tsum_eq_zero_of_not_summable hf, norm_zero],
    exact ge_of_tendsto' hg (λ s, sum_nonneg $ λ i hi, (norm_nonneg _).trans (h i)) }
end

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma norm_tsum_le_tsum_norm {f : ι → E} (hf : summable (λi, ∥f i∥)) :
  ∥∑' i, f i∥ ≤ ∑' i, ∥f i∥ :=
tsum_of_norm_bounded hf.has_sum $ λ i, le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `∥f i∥₊ ≤ g i`, then `∥∑' i, f i∥₊ ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma tsum_of_nnnorm_bounded {f : ι → E} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : has_sum g a)
  (h : ∀ i, ∥f i∥₊ ≤ g i) :
  ∥∑' i : ι, f i∥₊ ≤ a :=
begin
  simp only [← nnreal.coe_le_coe, ← nnreal.has_sum_coe, coe_nnnorm] at *,
  exact tsum_of_norm_bounded hg h
end

/-- If `∑' i, ∥f i∥₊` is summable, then `∥∑' i, f i∥₊ ≤ ∑' i, ∥f i∥₊`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma nnnorm_tsum_le {f : ι → E} (hf : summable (λi, ∥f i∥₊)) :
  ∥∑' i, f i∥₊ ≤ ∑' i, ∥f i∥₊ :=
tsum_of_nnnorm_bounded hf.has_sum (λ i, le_rfl)

variable [complete_space E]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded_eventually {f : ι → E} (g : ι → ℝ) (hg : summable g)
  (h : ∀ᶠ i in cofinite, ∥f i∥ ≤ g i) : summable f :=
summable_iff_cauchy_seq_finset.2 $ cauchy_seq_finset_of_norm_bounded_eventually hg h

lemma summable_of_nnnorm_bounded {f : ι → E} (g : ι → ℝ≥0) (hg : summable g)
  (h : ∀i, ∥f i∥₊ ≤ g i) : summable f :=
summable_of_norm_bounded (λ i, (g i : ℝ)) (nnreal.summable_coe.2 hg) (λ i, by exact_mod_cast h i)

lemma summable_of_summable_norm {f : ι → E} (hf : summable (λa, ∥f a∥)) : summable f :=
summable_of_norm_bounded _ hf (assume i, le_refl _)

lemma summable_of_summable_nnnorm {f : ι → E} (hf : summable (λ a, ∥f a∥₊)) : summable f :=
summable_of_nnnorm_bounded _ hf (assume i, le_refl _)

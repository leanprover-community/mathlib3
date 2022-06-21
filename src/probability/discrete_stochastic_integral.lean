import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α β : Type*} {m0 : measurable_space α} {μ : measure α} [is_finite_measure μ]
  {f g : ℕ → α → ℝ} {ℱ : filtration ℕ m0} {ξ : ℕ → α → ℝ}

lemma foo (hf : submartingale f ℱ μ) (hξ : adapted ℱ (λ n, ξ (n + 1)))
  (hbdd : ∃ R, ∀ n x, ξ n x ≤ R) (hnonneg : ∀ n x, 0 ≤ ξ n x) :
  submartingale (λ n : ℕ, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)) ℱ μ :=
begin
  have hint : ∀ m, integrable (∑ k in finset.range m, ξ (k + 1) * (f (k + 1) - f k)) μ,
  { sorry },
  have hadp : adapted ℱ (λ (n : ℕ), ∑ (k : ℕ) in finset.range n, ξ (k + 1) * (f (k + 1) - f k)),
  { sorry },
  refine submartingale_nat hadp hint _,
  { intros i,
    suffices : 0 ≤ᵐ[μ]
      μ[∑ k in finset.range (i + 1), ξ (k + 1) * (f (k + 1) - f k) -
        ∑ k in finset.range i, ξ (k + 1) * (f (k + 1) - f k)|ℱ i],
    { sorry },
    simp only [← finset.sum_Ico_eq_sub _ (nat.le_succ _), finset.sum_apply, pi.mul_apply,
      pi.sub_apply, nat.Ico_succ_singleton, finset.sum_singleton],
    have : μ[ξ (i + 1) * (f (i + 1) - f i)|ℱ i] =ᵐ[μ] ξ (i + 1) * μ[f (i + 1) - f i|ℱ i],
    { sorry },
    refine eventually_le.trans _ this.symm.le,
    sorry,
    -- rw [← sub_nonneg, ← integral_sub (hint (i + 1)).integrable_on (hint i).integrable_on],
  }
end

-- lemma submartingale.submartingale_mul_sub_stopped_value
--   (hf : submartingale f ℱ μ) (hτ : is_stopping_time ℱ τ)
--   (hτη : measurable[hτ.measurable_space] ξ) (hbdd : ∃ R, ∀ x, ξ x ≤ R) :
--   submartingale (λ n, ξ * (f n - stopped_value f (λ x, min n (τ x)))) ℱ μ :=
-- begin
--   rw submartingale_iff_expected_stopped_value_mono,
--   { intros π η hπ hη hπη hbddη,

--   },
--   sorry,
--   sorry
-- end

end measure_theory

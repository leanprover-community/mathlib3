import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

variables {α β E ι : Type*} [preorder ι] [succ_order ι]
  {m0 : measurable_space α} {μ : measure α}
  [normed_group E] [normed_space ℝ E] [complete_space E]
  {f g : ι → α → E} {ℱ : filtration ι m0}

/-- A process -/
def predictable [measure_space β] [topological_space β] (ℱ : filtration ι m0) (f : ι → α → β) :=
∀ i, measurable[ℱ (order.succ i)] (f i)

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

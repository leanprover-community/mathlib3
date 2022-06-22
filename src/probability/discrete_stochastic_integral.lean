import probability.martingale

open topological_space filter
open_locale nnreal ennreal measure_theory probability_theory big_operators

namespace measure_theory

section

variables {α β : Type*} {m m0 : measurable_space α} {μ : measure α} {ξ ζ : α → ℝ}

lemma condexp_measurable_mul
  (hξm : strongly_measurable[m] ξ) (hζ : integrable ζ μ)
  -- (hξ : integrable ξ μ) hopefully won't need this
  (hζξ : integrable (ξ * ζ) μ) :
  μ[ξ * ζ | m] =ᵐ[μ] ξ * μ[ζ | m] :=
sorry

lemma integrable.bdd_mul (hζ : integrable ζ μ) (hξ : ∃ C, ∀ x, |ξ x| ≤ C) :
  integrable (ξ * ζ) μ :=
sorry

variables {l : filter α} {f g f₁ f₂ g₁ g₂ : α → β}

lemma eventually.mul_le_mul [ordered_semiring β]
  (hf : f₁ ≤ᶠ[l] f₂) (hg : g₁ ≤ᶠ[l] g₂) (hg' : 0 ≤ᶠ[l] g₁) (hf' : 0 ≤ᶠ[l] f₂) :
  f₁ * g₁ ≤ᶠ[l] f₂ * g₂ :=
begin
  filter_upwards [hf, hg, hf', hg'] with x hfle hgle hfzero hgzero,
  exact mul_le_mul hfle hgle hgzero hfzero,
end

lemma eventually.mul_nonneg [ordered_semiring β] (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
  0 ≤ᶠ[l] f * g :=
begin
  rw ← zero_mul (0 : α → β),
  exact eventually.mul_le_mul hf hg (eventually_le.refl _ _) hf,
end

lemma eventually_le_iff_sub_nonneg [ordered_ring β] :
  f ≤ᶠ[l] g ↔ 0 ≤ᶠ[l] g - f :=
begin
  refine ⟨λ h, _, λ h, _⟩;
  filter_upwards [h] with x hx,
  { exact sub_nonneg_of_le hx },
  { exact sub_nonneg.1 hx }
end

end

section submartingale

variables {α β ι : Type*} [preorder ι] [topological_space β] {m0 : measurable_space α}
  {μ : measure α} {ℱ : filtration ι m0}

lemma submartingale_of_condexp_sub_nonneg [is_finite_measure μ]
  {f : ι → α → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i j, i ≤ j → 0 ≤ᵐ[μ] μ[f j - f i| ℱ i]) :
  submartingale f ℱ μ :=
begin
  refine ⟨hadp, λ i j hij, _, hint⟩,
  rw [← condexp_of_strongly_measurable (ℱ.le _) (hadp _) (hint _), eventually_le_iff_sub_nonneg],
  exact eventually_le.trans (hf i j hij) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

lemma submartingale.condexp_sub_nonneg [is_finite_measure μ]
  {f : ι → α → ℝ} (hf : submartingale f ℱ μ) {i j : ι} (hij : i ≤ j) :
  0 ≤ᵐ[μ] μ[f j - f i| ℱ i] :=
begin
  refine eventually_le.trans _ (condexp_sub (hf.integrable _) (hf.integrable _)).symm.le,
  rw ← eventually_le_iff_sub_nonneg,
  rw condexp_of_strongly_measurable (ℱ.le _) (hf.adapted _) (hf.integrable _),
  exact hf.2.1 i j hij,
  apply_instance
end

lemma adapted.measurable {i j : ι} {f : ι → α → β} (hf : adapted ℱ f) (hij : i ≤ j) :
  strongly_measurable[ℱ j] (f i) :=
strongly_measurable.mono (hf i) (ℱ.mono hij)

end submartingale

variables {α β : Type*} {m m0 : measurable_space α} {μ : measure α} [is_finite_measure μ]
  {f g : ℕ → α → ℝ} {ℱ : filtration ℕ m0} {ξ : ℕ → α → ℝ}

lemma submartingale_of_condexp_sub_nonneg_nat [is_finite_measure μ]
  {f : ℕ → α → ℝ} (hadp : adapted ℱ f) (hint : ∀ i, integrable (f i) μ)
  (hf : ∀ i, 0 ≤ᵐ[μ] μ[f (i + 1) - f i| ℱ i]) :
  submartingale f ℱ μ :=
begin
  refine submartingale_nat hadp hint (λ i, _),
  rw [← condexp_of_strongly_measurable (ℱ.le _) (hadp _) (hint _), eventually_le_iff_sub_nonneg],
  exact eventually_le.trans (hf i) (condexp_sub (hint _) (hint _)).le,
  apply_instance
end

lemma submartingale.sum_mul_sub (hf : submartingale f ℱ μ) (hξ : adapted ℱ (λ n, ξ (n + 1)))
  (hbdd : ∃ R, ∀ n x, ξ n x ≤ R) (hnonneg : ∀ n x, 0 ≤ ξ n x) :
  submartingale (λ n : ℕ, ∑ k in finset.range n, ξ (k + 1) * (f (k + 1) - f k)) ℱ μ :=
begin
  have hξbdd : ∀ i, ∃ (C : ℝ), ∀ (x : α), |ξ (i + 1) x| ≤ C,
  { obtain ⟨C, hC⟩ := hbdd,
    intro i,
    refine ⟨C, λ x, abs_le.2 ⟨le_trans (neg_le.1 (le_trans _ (hC 0 x))) (hnonneg _ _), hC _ _⟩⟩,
    rw neg_zero,
    exact hnonneg 0 x },
  have hint : ∀ m, integrable (∑ k in finset.range m, ξ (k + 1) * (f (k + 1) - f k)) μ :=
    λ m, integrable_finset_sum' _
      (λ i hi, integrable.bdd_mul ((hf.integrable _).sub (hf.integrable _)) (hξbdd _)),
  have hadp : adapted ℱ (λ (n : ℕ), ∑ (k : ℕ) in finset.range n, ξ (k + 1) * (f (k + 1) - f k)),
  { intro m,
    refine finset.strongly_measurable_sum' _ (λ i hi, _),
    rw finset.mem_range at hi,
    exact (hξ.measurable hi.le).mul
      ((hf.adapted.measurable (nat.succ_le_of_lt hi)).sub (hf.adapted.measurable hi.le)) },
  refine submartingale_of_condexp_sub_nonneg_nat hadp hint (λ i, _),
  simp only [← finset.sum_Ico_eq_sub _ (nat.le_succ _), finset.sum_apply, pi.mul_apply,
    pi.sub_apply, nat.Ico_succ_singleton, finset.sum_singleton],
  have : μ[ξ (i + 1) * (f (i + 1) - f i)|ℱ i] =ᵐ[μ] ξ (i + 1) * μ[f (i + 1) - f i|ℱ i] :=
    condexp_measurable_mul (hξ _) ((hf.integrable _).sub (hf.integrable _))
      (((hf.integrable _).sub (hf.integrable _)).bdd_mul (hξbdd _)),
  exact eventually_le.trans (eventually.mul_nonneg (eventually_of_forall (hnonneg _))
    (hf.condexp_sub_nonneg (nat.le_succ _))) this.symm.le,
end

end measure_theory

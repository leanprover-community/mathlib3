import taoziegler.tomathlib.infinite_prod
import analysis.special_functions.log.basic

noncomputable theory
open finset filter function classical
open_locale topology classical big_operators nnreal

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

lemma proddable_of_summable_log (f : β → ℝ) (hf : ∀ b, 0 < f b) (h : summable (real.log ∘ f)) :
  proddable f :=
begin
  have : ∀ x, (real.exp ∘ λ (s : finset β), ∑ (b : β) in s, (real.log ∘ f) b) x =
    (λ (s : finset β), ∏ (b : β) in s, f b) x,
  { intros s,
    simp only [comp_app],
    rw real.exp_sum,
    exact prod_congr rfl (λ b hb, real.exp_log (hf _)) },
  obtain ⟨x, h⟩ := h,
  refine ⟨real.exp x, _⟩,
  exact (tendsto_congr this).mp ((real.continuous_exp.tendsto _).comp h)
end

-- needs to be strengthed, `hs` is too strong of a hypothesis
lemma summable_log_one_add_of_summable (s : β → ℝ) (hs : ∀ i, 0 ≤ s i) (h : summable s) :
  summable (λ i, real.log (1 + s i)) :=
begin
  refine summable_of_nonneg_of_le (λ b, real.log_nonneg _)
    (λ b, (real.log_le_sub_one_of_pos _).trans _) h;
  specialize hs b;
  linarith
end

lemma proddable_one_add_of_summable (s : β → ℝ) (hs : ∀ i, 0 < s i) (h : summable s) :
  proddable (λ i, 1 + s i) :=
begin
  refine proddable_of_summable_log _ (λ b, _) (summable_log_one_add_of_summable _ (λ b, _) h);
  specialize hs b;
  linarith
end

import probability_theory.density

/-
Right now, pdf is defined such that `μ.with_density f` must agree with
`map X ℙ` everywhere, while in introductory probability courses, is condition
is often relaxed such that they only need to agree on intervals of the form `(-∞, x]`.
While, these conditions are not equivalent in general, for finite measures, it is the case.

pf. Use Dykin's π-λ theorem.

With that in mind, we can show that if `F(x) := map X ℙ (-∞, x]` is differentiable,
by FTC `f := F'` satisfies `∫ x in a..b, f x ∂μ = F b - F a = map X ℙ (a, b]`, hence, implying
`μ.with_density f` equals `map X ℙ` and thus, `f =ᵐ[μ] pdf X`.

This allows us to use traditional methods for find the pdf of transformations, namely
`pdf g(X) x = pdf X (g⁻¹ x) * g'`.

-/

noncomputable theory
open_locale classical measure_theory nnreal ennreal interval

namespace measure_theory

open set topological_space measurable_space measure

variables {E : Type*} [normed_group E] [measurable_space E] [second_countable_topology E]
  [linear_order E] [order_topology E] [normed_space ℝ E] [complete_space E] [borel_space E]

#check ext_of_generate_finite
#check borel_eq_generate_Iio

section

variables (α : Type*) [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α]

#check Iio
#check measurable_space.measurable_set'

#check exists_seq_tendsto_Inf
-- def seq (x : α) : ℕ → set α
-- | 0 := ∅
-- | (n + 1) :=

lemma borel_eq_generate_Ioo : borel α = generate_from {S | ∃ l u, l < u ∧ Ioo l u = S} :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_Iio,
    refine generate_from_le _,
    rw forall_range_iff,
    intro x,
    sorry
   },
  { rintro - ⟨a, b, hlt, rfl⟩,
    exact generate_measurable.basic _ is_open_Ioo }
end

end

lemma ext_of_Iio (μ ν : measure E) [is_finite_measure μ]
  (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ioo a b) = ν (Ioo a b)) :
  μ = ν :=
begin
  refine ext_of_generate_finite {S | ∃ l u, l < u ∧ Ioo l u = S}
    (borel_eq_generate_Ioo E ▸ borel_space.measurable_eq) _ _ hμν,
  { convert is_pi_system_Ioo_mem univ univ,
    finish },
  { rintro - ⟨a, b, hlt, rfl⟩,
    exact h hlt }
end .

lemma ext_of_with_density_Iio
  (μ : measure E) [is_finite_measure μ] (f g : E → ℝ≥0∞) (hf : ∫⁻ (a : E), f a ∂μ ≠ ⊤)
  (h : ∀ ⦃a b⦄, a < b → μ.with_density f (Ioo a b) = μ.with_density g (Ioo a b)) :
  μ.with_density f = μ.with_density g :=
begin
  haveI : is_finite_measure (μ.with_density f) := is_finite_measure_with_density hf,
  refine ext_of_Iio _ _ _ h,
  sorry
end

end measure_theory

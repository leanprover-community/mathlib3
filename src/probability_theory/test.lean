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

section dense

variables {α : Type*} [nonempty α] [topological_space α] [separable_space α]

lemma dense_mem_open {s t : set α} (hs : s.nonempty) (ho : is_open s) (ht : dense t) :
  (s ∩ t).nonempty :=
begin
  cases hs with x hx,
  have : x ∈ closure t,
  { rw dense_iff_closure_eq.1 ht,
    exact mem_univ _ },
  rw mem_closure_iff at this,
  exact this s ho hx,
end

lemma exists_dense_seq_mem (s : set α) (hs : s.nonempty) (ho : is_open s) :
  ∃ n, dense_seq α n ∈ s :=
begin
  obtain ⟨-, hxs, n, rfl⟩ := dense_mem_open hs ho (dense_range_dense_seq α),
  exact ⟨n, hxs⟩
end

end dense

section

variables (α : Type*) [nonempty α] [topological_space α] [second_countable_topology α]
  [linear_order α] [order_topology α]

lemma exists_dense_seq_lt (hnlb : ∀ x : α, ∃ y, y < x) (x : α) : ∃ n, dense_seq α n < x :=
exists_dense_seq_mem (Iio x) (hnlb x) is_open_Iio

lemma Union_Ioo_dense_seq (hnlb : ∀ x : α, ∃ y, y < x) (x : α) :
  (⋃ n, Ico (dense_seq α n) x) = Iio x :=
begin
  ext y,
  rw [mem_Iio, mem_Union],
  split,
  { rintro ⟨n, hmem⟩,
    exact hmem.2 },
  { intro h,
    obtain ⟨n, hn⟩ := exists_dense_seq_lt α hnlb y,
    refine ⟨n, le_of_lt hn, h⟩ }
end

lemma borel_eq_generate_Ico : borel α = generate_from {S | ∃ l u, l < u ∧ Ico l u = S} :=
begin
  refine le_antisymm _ (generate_from_le _),
  { rw borel_eq_generate_Iio,
    refine generate_from_le _,
    rw forall_range_iff,
    intro x,
    by_cases hnlb : ∀ x : α, ∃ y, y < x,
    { rw ← Union_Ioo_dense_seq α hnlb x,
      refine @measurable_set.Union _ _ (generate_from {S | ∃ l u, l < u ∧ Ico l u = S}) _ _ _,
      intro n,
      by_cases hlt : dense_seq α n < x,
      { refine measurable_set_generate_from ⟨(dense_seq α n), x, hlt, rfl⟩ },
      { rw Ico_eq_empty hlt,
        exact @measurable_set.empty _ (generate_from {S | ∃ l u, l < u ∧ Ico l u = S}) } },
    { push_neg at hnlb,
      obtain ⟨l, hl⟩ := hnlb,
      by_cases hlx : l = x,
      { rw [(by { ext y, simp [mem_Iio, ← hlx, hl y] } : Iio x = ∅)],
        exact @measurable_set.empty _ (generate_from {S | ∃ l u, l < u ∧ Ico l u = S}) },
      { refine measurable_set_generate_from ⟨l, x, lt_of_le_of_ne (hl x) hlx, _⟩,
        ext y,
        simp only [mem_Iio, and_iff_right_iff_imp, mem_Ico],
        exact λ _, hl _ } } },
  { rintro - ⟨a, b, hlt, rfl⟩,
    haveI : @borel_space α _ (borel α) := { measurable_eq := rfl },
    exact @measurable_set_Ico _ _ (borel α) _ _ _ _ _ }
end

end

lemma ext_of_Iio (μ ν : measure E) [is_finite_measure μ]
  (hμν : μ univ = ν univ) (h : ∀ ⦃a b⦄, a < b → μ (Ico a b) = ν (Ico a b)) :
  μ = ν :=
begin
  refine ext_of_generate_finite {S | ∃ l u, l < u ∧ Ico l u = S}
    (borel_eq_generate_Ico E ▸ borel_space.measurable_eq) _ _ hμν,
  { rintro - - ⟨a, b, hab, rfl⟩ ⟨c, d, hcd, rfl⟩ hnempty,
    rw Ico_inter_Ico at hnempty ⊢,
    cases hnempty with x hx,
    exact ⟨a ⊔ c, b ⊓ d, lt_of_le_of_lt hx.1 hx.2, rfl⟩ },
  { rintro - ⟨a, b, hlt, rfl⟩,
    exact h hlt }
end

end measure_theory

import ring_theory.coprime.lemmas
open_locale big_operators

variables {R : Type*} {I : Type*} [comm_semiring R] [fintype I] {p : I → R} [decidable_eq I]

lemma exists_sum_eq_one_iff_pairwise_coprime :
  (∃ μ : I → R, ∑ (i : I), μ i * ∏ j in {i}ᶜ, p j = 1) ↔ pairwise (is_coprime on p) := sorry

lemma pairwise_coprime_iff_coprime_prod :
  pairwise (is_coprime on p) ↔ ∀ i, is_coprime (p i) (∏ j in {i}ᶜ, (p j)) :=
begin
  split; intro hp,
  { intro i, rw is_coprime.prod_right_iff, intros j hj,
    rw [finset.mem_compl, finset.mem_singleton] at hj, apply hp, symmetry, exact hj },
  { intros i j hj, specialize hp i, rw is_coprime.prod_right_iff at hp, apply hp,
    rw [finset.mem_compl, finset.mem_singleton], exact hj.symm }
end

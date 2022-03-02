import ring_theory.coprime.lemmas
open_locale big_operators

variables {R : Type*} {I : Type*} [comm_semiring R] {p : I → R} [decidable_eq I] {s : finset I}

lemma exists_sum_eq_one_iff_pairwise_coprime' :
  (∃ μ : I → R, ∑ i in s, μ i * ∏ j in s \ {i}, p j = 1) ↔ pairwise (is_coprime on λ i : s, p i) :=
sorry

lemma exists_sum_eq_one_iff_pairwise_coprime [fintype I] :
  (∃ μ : I → R, ∑ (i : I), μ i * ∏ j in {i}ᶜ, p j = 1) ↔ pairwise (is_coprime on p) := begin
convert exists_sum_eq_one_iff_pairwise_coprime' using 1, ext, split,
{ rintro hp ⟨i, _⟩ ⟨j, _⟩ h, apply hp, intro h', apply h, ext, exact h' },
{ intros hp i j h, apply hp ⟨i, finset.mem_univ i⟩ ⟨j, finset.mem_univ j⟩,
  rintro ⟨h'⟩, exact h rfl } end

lemma pairwise_coprime_iff_coprime_prod [fintype I] :
  pairwise (is_coprime on p) ↔ ∀ i, is_coprime (p i) (∏ j in {i}ᶜ, (p j)) :=
begin
  split; intro hp,
  { intro i, rw is_coprime.prod_right_iff, intros j hj,
    rw [finset.mem_compl, finset.mem_singleton] at hj, apply hp, symmetry, exact hj },
  { intros i j hj, specialize hp i, rw is_coprime.prod_right_iff at hp, apply hp,
    rw [finset.mem_compl, finset.mem_singleton], exact hj.symm }
end

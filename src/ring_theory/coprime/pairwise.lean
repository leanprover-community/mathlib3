import ring_theory.coprime.lemmas
open_locale big_operators

section subsingleton

variables {R : Type*} [comm_semiring R] [subsingleton R] {x y : R}

@[nontriviality, simp] lemma is_coprime_subsingleton : is_coprime = λ x y : R, true :=
by { funext, simp }

end subsingleton

section finset

lemma pairwise_insert {α} {s : finset α} {a : α} (h : a ∉ s) (r : α → α → Prop) :
  pairwise (r on λ a : s.cons a h, a) ↔ pairwise (r on λ a : s, a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
sorry

end finset

variables {R : Type*} {I : Type*} [comm_semiring R] {p : I → R} [decidable_eq I] {s : finset I}

lemma exists_sum_eq_one_iff_pairwise_coprime (h : s.nonempty) :
  (∃ μ : I → R, ∑ i in s, μ i * ∏ j in s \ {i}, p j = 1) ↔ pairwise (is_coprime on λ i : s, p i) :=
begin
  casesI subsingleton_or_nontrivial R,
  { simp only [eq_iff_true_of_subsingleton, exists_const, is_coprime_subsingleton, true_iff],
    tauto },
  refine h.cons_induction _ _; clear' s h,
  { simp only [pairwise, finset.sum_singleton, finset.sdiff_self, finset.prod_empty, mul_one,
               exists_apply_eq_apply, ne.def, true_iff],
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h,
    rw finset.mem_singleton at hi hj,
    simpa [hi, hj] using h },
  intros a s has h ih,
  have : ∀ s : finset I,
        (is_coprime on λ i : s, p i) = ((λ x y, is_coprime (p x) (p y)) on λ i : s, i),
  { simp [function.on_fun] },
  rw [this, pairwise_insert, ←this],
  split; intro h,
  { sorry },
  { sorry }
end

lemma exists_sum_eq_one_iff_pairwise_coprime' [fintype I] [nonempty I] :
  (∃ μ : I → R, ∑ (i : I), μ i * ∏ j in {i}ᶜ, p j = 1) ↔ pairwise (is_coprime on p) := begin
convert exists_sum_eq_one_iff_pairwise_coprime finset.univ_nonempty using 1, ext, split,
{ rintro hp ⟨i, _⟩ ⟨j, _⟩ h, apply hp, intro h', apply h, ext, exact h' },
{ intros hp i j h, apply hp ⟨i, finset.mem_univ i⟩ ⟨j, finset.mem_univ j⟩,
  rintro ⟨h'⟩, exact h rfl },
by apply_instance end

lemma pairwise_coprime_iff_coprime_prod :
  pairwise (is_coprime on λ i : s, p i) ↔ ∀ i ∈ s, is_coprime (p i) (∏ j in s \ {i}, (p j)) :=
begin
  split; intro hp,
  { intros i hi, rw is_coprime.prod_right_iff, intros j hj,
    rw [finset.mem_sdiff, finset.mem_singleton] at hj, obtain ⟨hj, ji⟩ := hj,
    apply hp ⟨i, hi⟩ ⟨j, hj⟩, rintro ⟨f⟩, exact ji rfl },
  { rintro ⟨i, hi⟩ ⟨j, hj⟩ h, specialize hp i hi, rw is_coprime.prod_right_iff at hp, apply hp,
    rw [finset.mem_sdiff, finset.mem_singleton],
    refine ⟨hj, λ f, h _⟩, ext, symmetry, exact f }
end

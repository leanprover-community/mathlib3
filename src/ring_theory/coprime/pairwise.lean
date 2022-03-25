import ring_theory.coprime.lemmas
import algebra.big_operators.ring
open_locale big_operators

namespace finset
variables {α : Type*} {s : finset α}

lemma pairwise_cons {a : α} (ha : a ∉ s) (r : α → α → Prop) :
  pairwise (r on λ a : s.cons a ha, a) ↔ pairwise (r on λ a : s, a) ∧ ∀ b ∈ s, r a b ∧ r b a :=
begin
  have : ∀ {s : finset α} {b c : α} {hb : b ∈ s} {hc : c ∈ s}, (⟨b, hb⟩ : s) = ⟨c, hc⟩ → b = c :=
    λ s b c hb hc eq, congr_arg coe eq,
  refine ⟨λ h, ⟨λ ⟨b, hb⟩ ⟨c, hc⟩ ne, h ⟨b, subset_cons ha hb⟩ ⟨c, subset_cons ha hc⟩
    (λ eq, ne $ subtype.ext $ this eq),
    λ b hb, ⟨h ⟨a, mem_cons_self _ _⟩ ⟨b, subset_cons ha hb⟩ (λ eq, ha $ (this eq).symm.cases_on hb),
      h ⟨b, subset_cons ha hb⟩ ⟨a, mem_cons_self _ _⟩ (λ eq, ha $ (this eq).cases_on hb)⟩⟩,
  λ h b c ne, _⟩,
  obtain ⟨b, hb⟩ := b, obtain ⟨c, hc⟩ := c, change r b c, rw mem_cons at hb hc,
  cases hb with hb hb; cases hc with hc hc,
  { exfalso, apply ne, ext, change b = c, rw [hb, hc] },
  { rw hb, exact (h.right c hc).left },
  { rw hc, exact (h.right b hb).right },
  { exact h.left ⟨b, hb⟩ ⟨c, hc⟩ (λ eq, ne $ subtype.ext $ this eq) }
end

end finset

variables {R : Type*} {I : Type*} [comm_semiring R] {p : I → R} [decidable_eq I] {s : finset I}
open finset

lemma exists_sum_eq_one_iff_pairwise_coprime (h : s.nonempty) :
  (∃ μ : I → R, ∑ i in s, μ i * ∏ j in s \ {i}, p j = 1) ↔ pairwise (is_coprime on λ i : s, p i) :=
begin
  refine h.cons_induction _ _; clear' s h,
  { simp only [pairwise, sum_singleton, finset.sdiff_self, prod_empty, mul_one,
      exists_apply_eq_apply, ne.def, true_iff],
    rintro a ⟨i, hi⟩ ⟨j, hj⟩ h,
    rw finset.mem_singleton at hi hj,
    simpa [hi, hj] using h },
  intros a s has h ih,
  have : ∀ s : finset I,
        (is_coprime on λ i : s, p i) = ((λ x y, is_coprime (p x) (p y)) on λ i : s, i),
  { simp [function.on_fun] },
  rw [this, pairwise_cons, ←this],
  have mem : ∀ x ∈ s, a ∈ insert a s \ {x} := λ x hx, by
    { rw [mem_sdiff, mem_singleton], exact ⟨mem_insert_self _ _, λ ha, has (ha.symm.cases_on hx)⟩ },
  split,
  { rintro ⟨μ, hμ⟩,
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert has] at hμ,
    refine ⟨ih.mp ⟨pi.single h.some (μ a * p h.some) + μ * λ _, p a, _⟩, λ b hb, _⟩,
    { rw [prod_eq_mul_prod_diff_singleton h.some_spec, ← mul_assoc,
        ← @if_pos _ _ h.some_spec R (_ * _) 0, ← sum_pi_single', ← sum_add_distrib] at hμ,
      rw [← hμ, sum_congr rfl], intros x hx, convert add_mul _ _ _ using 2,
      { by_cases hx : x = h.some,
        { rw [hx, pi.single_eq_same, pi.single_eq_same] },
        { rw [pi.single_eq_of_ne hx, pi.single_eq_of_ne hx, zero_mul] } },
      { convert (mul_assoc _ _ _).symm,
        convert prod_eq_mul_prod_diff_singleton (mem x hx) _ using 3,
        convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert has] } },
    { have : is_coprime (p b) (p a) :=
        ⟨μ a * ∏ i in s \ {b}, p i, ∑ i in s, μ i * ∏ j in s \ {i}, p j, _⟩,
      { exact ⟨this.symm, this⟩ },
      rw [mul_assoc, ← prod_eq_prod_diff_singleton_mul hb, sum_mul, ← hμ, sum_congr rfl],
      intros x hx, convert mul_assoc _ _ _,
      convert prod_eq_prod_diff_singleton_mul (mem x hx) _ using 3,
      convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert has] } },
  { rintro ⟨hp, Hb⟩, obtain ⟨μ, hμ⟩ := ih.mpr hp,
    obtain ⟨u, v, huv⟩ := is_coprime.prod_left (λ b hb, (Hb b hb).right),
    use λ i, if i = a then u else v * μ i,
    have hμ' : ∑ i in s, v * ((μ i * ∏ j in s \ {i}, p j) * p a) = v * p a := by
      rw [← mul_sum, ← sum_mul, hμ, one_mul],
    rw [sum_cons, cons_eq_insert, sdiff_singleton_eq_erase, erase_insert has, if_pos rfl,
      ← huv, ← hμ', sum_congr rfl], intros x hx,
    rw [mul_assoc, if_neg (λ ha : x = a, has (ha.cases_on hx))],
    convert mul_assoc _ _ _, convert (prod_eq_prod_diff_singleton_mul (mem x hx) _).symm using 3,
    convert sdiff_sdiff_comm, rw [sdiff_singleton_eq_erase, erase_insert has] }
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

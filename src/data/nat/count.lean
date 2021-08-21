import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard

/-!
-/

namespace nat
variables (p : ℕ → Prop) [decidable_pred p]

/-- Count the `i ≤ n` satisfying `p i`. -/
def count (n : ℕ) : ℕ :=
((list.range (n+1)).filter p).length

noncomputable instance count_set_fintype (p : ℕ → Prop) (n : ℕ) : fintype { i | i ≤ n ∧ p i } :=
fintype.of_injective (λ i, (⟨i.1, i.2.1⟩ : { i | i ≤ n })) (by tidy)

/-- `count p n` can be expressed as the cardinality of `{ i | i ≤ n ∧ p i }`. -/
lemma count_eq_card (n : ℕ) : count p n = fintype.card { i : ℕ | i ≤ n ∧ p i } :=
sorry

/--
Find the `n`-th natural number satisfying `p`
(indexed from `0`, so `nth p 0` is the first natural number satisfying `p`),
or `0` if there is no such.
-/
noncomputable def nth : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

lemma nth_def (n : ℕ) : nth p n = Inf { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
well_founded.fix_eq _ _ _

lemma count_monotone : monotone (count p) :=
begin
  intros n m h,
  rw [count_eq_card, count_eq_card],
  fapply fintype.card_le_of_injective,
  { exact λ i, ⟨i.1, i.2.1.trans h, i.2.2⟩, },
  { rintros ⟨n, _⟩ ⟨m, _⟩ h,
    simpa using h, },
end

-- Not sure how hard this is. Possibly not needed, anyway.
lemma nth_mem_of_le_card (n : ℕ) (w : (n : cardinal) ≤ cardinal.mk { i | p i }) :
  p (nth p n) :=
sorry

lemma nth_mem_of_infinite_aux (i : set.infinite p) (n : ℕ) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  -- This sorry should be relatively easy:
  -- it's the intersection of an infinite set with finitely many cofinite sets.
  have ne : set.nonempty { i : ℕ | p i ∧ ∀ k < n, nth p k < i } := sorry,
  rw nth_def,
  exact Inf_mem ne,
end

lemma nth_mem_of_infinite (i : set.infinite p) (n : ℕ) : p (nth p n) :=
(nth_mem_of_infinite_aux p i n).1

lemma nth_strict_mono_of_infinite (i : set.infinite p) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p i m).2 _ h

lemma count_nth_of_le_card (n : ℕ) (w : n ≤ nat.card { i | p i }) :
  count p (nth p n) = n + 1 :=
sorry

lemma count_nth_of_infinite (i : set.infinite p) (n : ℕ) : count p (nth p n) = n + 1 :=
sorry

lemma count_nth_gc (i : set.infinite p) : galois_connection (count p) (nth p) :=
begin
  rintro a b,
  rw [nth, count],
  rw le_cInf_iff (⟨0, λ _ _, zero_le _⟩ : bdd_below _),
  sorry,
  refine ⟨0, λ _ _, zero_le _⟩,
  rintro y,
end

lemma count_le_iff_le_nth {p} [decidable_pred p] (i : set.infinite p) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b :=
count_nth_gc p i _ _

lemma lt_nth_iff_count_lt {p} [decidable_pred p] (i : set.infinite p) {a b : ℕ} :
  a < count p b ↔ nth p a < b :=
lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth i

lemma nth_count_le (i : set.infinite p) (n : ℕ) : count p (nth p n) ≤ n :=
(count_nth_gc _ i).l_u_le _

lemma nth_le_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k ≤ n :=
sorry

-- todo: move
lemma le_succ_iff (x n : ℕ) : x ≤ n + 1 ↔ x ≤ n ∨ x = n + 1 :=
by rw [decidable.le_iff_lt_or_eq, lt_succ_iff]

lemma count_eq_count_add_one (n : ℕ) (h : p (n+1)) :
  count p (n + 1) = count p n + 1 :=
begin
  rw [count_eq_card, count_eq_card],
  suffices : {i : ℕ | i ≤ n + 1 ∧ p i} = {i : ℕ | i ≤ n ∧ p i} ∪ {n + 1},
  { simp [this] },
  ext,
  simp only [set.mem_insert_iff, set.mem_set_of_eq, set.union_singleton],
  rw [le_succ_iff, or_and_distrib_left],
  suffices : (x = n + 1 ∨ p x) ↔ p x,
  { rw this,
    tauto },
  simp [h] {contextual := tt},
end

-- TODO this is the difficult sorry
lemma nth_count (n : ℕ) (h : p n) : nth p (count p n - 1) = n :=
sorry

open_locale classical

noncomputable def set.infinite.order_iso_nat {s : set ℕ} (i : s.infinite) : s ≃o ℕ :=
(strict_mono.order_iso_of_surjective
  (λ n, (⟨nth s n, nth_mem_of_infinite s i n⟩ : s))
  (λ n m h, nth_strict_mono_of_infinite s i h)
  (λ ⟨n, w⟩, ⟨count s n - 1, by simpa using nth_count s n w⟩)).symm

end nat

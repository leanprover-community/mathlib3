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
((list.range n).filter p).length

noncomputable instance count_set_fintype (n : ℕ) (p : ℕ → Prop) : fintype { i | i ≤ n ∧ p i } :=
fintype.of_injective (λ i, (⟨i.1, i.2.1⟩ : { i | i ≤ n })) (by tidy)

/-- `count p n` can be expressed as the cardinality of `{ i | i ≤ n ∧ p i }`. -/
lemma count_eq_card (n : ℕ) : count p n = fintype.card { i : ℕ | i ≤ n ∧ p i } :=
sorry

/-- Find the `n`-th natural number satisfying `p`, or `0` if there is no such. -/
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

lemma nth_mem_of_infinite_aux (n : ℕ) (i : set.infinite p) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  -- This sorry should be relatively easy:
  -- it's the intersection of an infinite set with finitely many cofinite sets.
  have ne : set.nonempty { i : ℕ | p i ∧ ∀ k < n, nth p k < i } := sorry,
  rw nth_def,
  exact Inf_mem ne,
end

lemma nth_mem_of_infinite (n : ℕ) (i : set.infinite p) : p (nth p n) :=
(nth_mem_of_infinite_aux p n i).1

lemma nth_strict_mono_of_infinite (i : set.infinite p) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p m i).2 _ h

lemma count_nth_of_le_card (n : ℕ) (w : n ≤ nat.card { i | p i }) :
  count p (nth p n) = n :=
sorry

lemma count_nth_of_infinite (n : ℕ) (i : set.infinite p) : count p (nth p n) = n :=
sorry

lemma nth_le_of_le_count (n k : ℕ) (h : k ≤ count p n) : nth p k ≤ n :=
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
lemma nth_count (n : ℕ) (h : p n) : nth p (count p n) = n :=
sorry

open_locale classical

noncomputable def set.infinite.order_iso_nat {s : set ℕ} (i : s.infinite) : s ≃o ℕ :=
(strict_mono.order_iso_of_surjective
  (λ n, (⟨nth s n, nth_mem_of_infinite s n i⟩ : s))
  (λ n m h, nth_strict_mono_of_infinite s i h)
  (λ ⟨n, w⟩, ⟨count s n, by simpa using nth_count s n w⟩)).symm

end nat

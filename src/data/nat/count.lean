import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard

namespace nat

/-- Count the `i ≤ n` satisfying `p i`. -/
noncomputable def count (p : ℕ → Prop) (n : ℕ) : ℕ :=
nat.card { i : ℕ | i ≤ n ∧ p i }

/-- Find the `n`-th natural number satisfying `p`, or `0` if there is no such. -/
noncomputable def nth (p : ℕ → Prop) : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

lemma nth_def (p : ℕ → Prop) (n : ℕ) : nth p n = Inf { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
well_founded.fix_eq _ _ _

lemma count_monotone (p : ℕ → Prop) : monotone (count p) :=
begin
  intros n m h,
  dsimp [count],
  haveI : Π n, fintype { i | i ≤ n ∧ p i } :=
    λ n, fintype.of_injective (λ i, (⟨i.1, i.2.1⟩ : { i | i ≤ n })) (by tidy),
  rw [card_eq_fintype_card, card_eq_fintype_card],
  fapply fintype.card_le_of_injective,
  { exact λ i, ⟨i.1, i.2.1.trans h, i.2.2⟩, },
  { rintros ⟨n, _⟩ ⟨m, _⟩ h,
    simpa using h, },
end

lemma nth_mem_of_le_card (p : ℕ → Prop) (n : ℕ) (w : (n : cardinal) ≤ cardinal.mk { i | p i }) :
  p (nth p n) :=
sorry

lemma nth_mem_of_infinite_aux (p : ℕ → Prop) (n : ℕ) (i : set.infinite p) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  have ne : set.nonempty { i : ℕ | p i ∧ ∀ k < n, nth p k < i } := sorry,
  rw nth_def,
  exact Inf_mem ne,
end

lemma nth_mem_of_infinite (p : ℕ → Prop) (n : ℕ) (i : set.infinite p) : p (nth p n) :=
(nth_mem_of_infinite_aux p n i).1

lemma nth_strict_mono_of_infinite (p : ℕ → Prop) (i : set.infinite p) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p m i).2 _ h

lemma count_nth_of_le_card (p : ℕ → Prop) (n : ℕ) (w : n ≤ nat.card { i | p i }) :
  count p (nth p n) = n :=
sorry

lemma count_nth_of_infinite (p : ℕ → Prop) (n : ℕ) (i : set.infinite p) : count p (nth p n) = n :=
sorry

lemma nth_le_of_le_count (p : ℕ → Prop) (n k : ℕ) (h : k ≤ count p n) : nth p k ≤ n :=
sorry

lemma nth_count_le (p : ℕ → Prop) (n : ℕ) : nth p (count p n) ≤ n :=
nth_le_of_le_count p n (count p n) (le_refl _)

lemma count_eq_count_add_one (p : ℕ → Prop) (n : ℕ) (h : p (n+1)) :
  count p (n + 1) = count p n + 1 :=
sorry

-- TODO this is the difficult sorry
lemma nth_count (p : ℕ → Prop) (n : ℕ) (h : p n) : nth p (count p n) = n :=
sorry

end nat

noncomputable def set.infinite.order_iso_nat {s : set ℕ} (i : s.infinite) : s ≃o ℕ :=
(strict_mono.order_iso_of_surjective
  (λ n, (⟨nat.nth s n, nat.nth_mem_of_infinite s n i⟩ : s))
  (λ n m h, nat.nth_strict_mono_of_infinite s i h)
  (λ ⟨n, w⟩, ⟨nat.count s n, by simpa using nat.nth_count s n w⟩)).symm

import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard

/-!
-/

namespace nat

namespace computable
variables (p : ℕ → Prop) [decidable_pred p]

/-- Find the `n`-th natural number satisfying `p`, or `0` if there is no such. -/
noncomputable def nth  : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

/-- Count the `i ≤ n` satisfying `p i`. -/
def count (n : ℕ) : ℕ :=
((list.range n.succ).filter p).length

lemma nth_count_gc  : galois_connection (nth p) (count p) :=
begin
  rintro a b,
  rw nth,
  rw Inf_le_iff,
end

lemma nth_le_iff_le_count {p} [decidable_pred p] {a b : ℕ} : nth p a ≤ b ↔ a ≤ count p b :=
nth_count_gc p _ _

lemma lt_nth_iff_count_lt {p} [decidable_pred p] {a b : ℕ} : a < nth p b ↔ count p a < b :=
lt_iff_lt_of_le_iff_le nth_le_iff_le_count

lemma nth_count_le  (n : ℕ) : nth p (count p n) ≤ n :=
(nth_count_gc _).l_u_le _

lemma count_succ_eq_succ_count {n : ℕ} (h : p (n + 1)) :
  count p (n + 1) = count p n + 1 :=
begin
  suffices : (list.range (n+2)).filter p = ((list.range n.succ).filter p) ++ [n+1],
  { simp [count, this] },
  rw list.range_succ,
  simp [h]
end

lemma nth_count  (n : ℕ) (h : p n) : nth p (count p n) = n :=
begin
  refine (nth_count_le _ _).antisymm _,
  cases n,
  { exact zero_le _ },
  rw [count_succ_eq_succ_count _ h, succ_le_iff, lt_nth_iff_count_lt],
  exact lt_succ_self _,
end


end computable

namespace noncomp
variables (p : ℕ → Prop)

/-- Count the `i ≤ n` satisfying `p i`. -/
noncomputable def count (p : ℕ → Prop) (n : ℕ) : ℕ :=
nat.card { i : ℕ | i ≤ n ∧ p i }

/-- Find the `n`-th natural number satisfying `p`, or `0` if there is no such. -/
noncomputable def nth  : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

lemma nth_def  (n : ℕ) : nth p n = Inf { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
well_founded.fix_eq _ _ _

lemma count_monotone  : monotone (count p) :=
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

lemma nth_mem_of_le_card  (n : ℕ) (w : (n : cardinal) ≤ cardinal.mk { i | p i }) :
  p (nth p n) :=
sorry

lemma nth_mem_of_infinite_aux  (n : ℕ) (i : set.infinite p) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  have ne : set.nonempty { i : ℕ | p i ∧ ∀ k < n, nth p k < i } := sorry,
  rw nth_def,
  exact Inf_mem ne,
end

lemma nth_mem_of_infinite  (n : ℕ) (i : set.infinite p) : p (nth p n) :=
(nth_mem_of_infinite_aux p n i).1

lemma nth_strict_mono_of_infinite  (i : set.infinite p) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p m i).2 _ h

lemma count_nth_of_le_card  (n : ℕ) (w : n ≤ nat.card { i | p i }) :
  count p (nth p n) = n :=
sorry

lemma count_nth_of_infinite  (n : ℕ) (i : set.infinite p) : count p (nth p n) = n :=
sorry

lemma nth_le_of_le_count  (n k : ℕ) (h : k ≤ count p n) : nth p k ≤ n :=
sorry

lemma nth_count_gc  : galois_connection (nth p) (count p) :=
begin
  rintro a b,
  rw nth,
end

lemma nth_le_iff_le_count {p} [decidable_pred p] {a b : ℕ} : nth p a ≤ b ↔ a ≤ count p b :=
nth_count_gc p _ _

lemma lt_nth_iff_count_lt {p} [decidable_pred p] {a b : ℕ} : a < nth p b ↔ count p a < b :=
lt_iff_lt_of_le_iff_le nth_le_iff_le_count

lemma nth_count_le  (n : ℕ) : nth p (count p n) ≤ n :=
(nth_count_gc _).l_u_le _

lemma count_eq_count_add_one  (n : ℕ) (h : p (n+1)) :
  count p (n + 1) = count p n + 1 :=
sorry

-- TODO this is the difficult sorry
lemma nth_count  (n : ℕ) (h : p n) : nth p (count p n) = n :=
begin
  refine (nth_count_le _ _).antisymm _,
end

noncomputable def set.infinite.order_iso_nat {s : set ℕ} (i : s.infinite) : s ≃o ℕ :=
(strict_mono.order_iso_of_surjective
  (λ n, (⟨nat.nth s n, nat.nth_mem_of_infinite s n i⟩ : s))
  (λ n m h, nat.nth_strict_mono_of_infinite s i h)
  (λ ⟨n, w⟩, ⟨nat.count s n, by simpa using nat.nth_count s n w⟩)).symm

end noncomp

end nat

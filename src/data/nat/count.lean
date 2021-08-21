import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard
import data.nat.lattice

/-!
-/

namespace nat
variables (p : ℕ → Prop) [decidable_pred p]

/-- Count the `i < n` satisfying `p i`. -/
def count (n : ℕ) : ℕ :=
((list.range n).filter p).length

noncomputable instance count_set_fintype (p : ℕ → Prop) (n : ℕ) : fintype { i | i < n ∧ p i } :=
fintype.of_injective (λ i, (⟨i.1, i.2.1⟩ : { i | i < n })) (by tidy)

/-- `count p n` can be expressed as the cardinality of `{ i | i ≤ n ∧ p i }`. -/
lemma count_eq_card (n : ℕ) : count p n = fintype.card { i : ℕ | i < n ∧ p i } :=
begin
  have h : list.nodup ((list.range n).filter p) :=
    list.nodup_filter _ (list.nodup_range n),
  rw ←multiset.coe_nodup at h,
  rw [count, ←multiset.coe_card],
  change (finset.mk _ h).card = _,
  rw [←set.to_finset_card],
  congr' 1,
  ext i,
  simp [lt_succ_iff],
end

lemma count_succ_eq_succ_count_iff {p : ℕ → Prop} [decidable_pred p] {n : ℕ} :
  count p (n + 1) = count p n + 1 ↔ p n :=
begin
  sorry
end

lemma count_succ_eq_succ_count {n : ℕ} (h : p n) :
  count p (n + 1) = count p n + 1 :=
begin
  rw [count_eq_card, count_eq_card],
  suffices : {i : ℕ | i < n + 1 ∧ p i} = {i : ℕ | i < n ∧ p i} ∪ {n},
  { simp [this] },
  ext,
  simp only [set.mem_insert_iff, set.mem_set_of_eq, set.union_singleton],
  rw [lt_succ_iff, decidable.le_iff_lt_or_eq, or_comm, or_and_distrib_left],
  exact and_congr_right (λ _, (or_iff_right_of_imp $ λ h : x = n, h.symm.subst hn).symm),
end

lemma count_succ_eq_count_iff {p : ℕ → Prop} [decidable_pred p] {n : ℕ} :
  count p (n + 1) = count p n ↔ ¬p n :=
begin
  sorry
end

lemma count_succ_eq_count {n : ℕ} (h : ¬p n) :
  count p (n + 1) = count p n :=
begin
  rw [count_eq_card, count_eq_card],
  suffices : {i : ℕ | i < n + 1 ∧ p i} = {i : ℕ | i < n ∧ p i} ∪ {n},
  { simp [this] },
  ext,
  simp only [set.mem_insert_iff, set.mem_set_of_eq, set.union_singleton],
  rw [lt_succ_iff, decidable.le_iff_lt_or_eq, or_comm, or_and_distrib_left],
  exact and_congr_right (λ _, (or_iff_right_of_imp $ λ h : x = n, h.symm.subst hn).symm),
end

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
  { exact λ i, ⟨i.1, i.2.1.trans_le h, i.2.2⟩ },
  { rintros ⟨n, _⟩ ⟨m, _⟩ h,
    simpa using h },
end

-- Not sure how hard this is. Possibly not needed, anyway.
lemma nth_mem_of_le_card (n : ℕ) (w : (n : cardinal) ≤ cardinal.mk { i | p i }) :
  p (nth p n) :=
sorry

-- TODO move to `data.set.finite`.
lemma exists_gt_of_infinite (i : set.infinite p) (n : ℕ) : ∃ m, p m ∧ n < m := sorry

-- TODO move to `data.set.finite`.
lemma infinite_of_infinite_sdiff_finite {α : Type*} {s t : set α}
  (hs : s.infinite) (ht : t.finite) : (s \ t).infinite :=
begin
  intro hd,
  have := set.finite.union hd (set.finite.inter_of_right ht s),
  rw set.diff_union_inter at this,
  exact hs this,
end

lemma nth_mem_of_infinite_aux (n : ℕ) (i : set.infinite (set_of p)) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  have ne : set.nonempty { i : ℕ | p i ∧ ∀ k < n, nth p k < i },
  { let s : set ℕ := ⋃ (k < n), { i : ℕ | nth p k ≥ i },
    convert_to ((set_of p) \ s).nonempty,
    { ext i, simp, },
    have : s.finite,
    { apply set.finite.bUnion,
      apply set.finite_lt_nat,
      intros k h,
      apply set.finite_le_nat, },
    apply set.infinite.nonempty,
    apply infinite_of_infinite_sdiff_finite i this, },
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
  sorry,
end

lemma count_le_iff_le_nth {p} [decidable_pred p] (i : set.infinite p) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b :=
count_nth_gc p i _ _

lemma lt_nth_iff_count_lt {p} [decidable_pred p] (i : set.infinite p) {a b : ℕ} :
  a < count p b ↔ nth p a < b :=
lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth i

lemma nth_count_le (i : set.infinite p) (n : ℕ) : count p (nth p n) ≤ n :=
(count_nth_gc _ i).l_u_le _

lemma nth_le_of_le_count (a b : ℕ) (h : a < nth p b) : count p a < b :=
begin

end

lemma nth_le_of_le_count (a b : ℕ) (h : a ≤ count p b) : nth p a ≤ b :=
begin
  rw lt_of_lt_
  rw nth,
  refine cInf_le_of_le _ _ _,

end

lemma nth_le_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k ≤ n :=
sorry

-- todo: move
lemma le_succ_iff (x n : ℕ) : x ≤ n + 1 ↔ x ≤ n ∨ x = n + 1 :=
by rw [decidable.le_iff_lt_or_eq, lt_succ_iff]

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

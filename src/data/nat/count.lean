import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard
import data.nat.lattice
import data.finset.intervals

/-!

# Counting on ℕ

This files defines ways to get basic properties of a predicate on ℕ, such as "how many numbers
under `k` satisfy the predicate" and "what is the `n`th number that satisifies this predicate".
We define these as two functions, `count` and `nth`, that answer these questions, and prove
the expected theorems about them.

## Main definitions:

* `count`: `count p n` returns the number of `k < n` such that `p k`.
* `nth`: `nth p n` returns the `n`-th `k` (zero-indexed) number such that `p k`. If there is no
  such number (that is, `p` is true for at most `n` numbers), `nth p n = 0`.
-/

open list

section to_move

namespace nat

lemma le_succ_iff (x n : ℕ) : x ≤ n + 1 ↔ x ≤ n ∨ x = n + 1 :=
by rw [decidable.le_iff_lt_or_eq, nat.lt_succ_iff]

end nat

namespace set

variables {α : Type*} {s t : set α}

lemma sdiff_eq_empty_iff_subset : s \ t = ∅ ↔ s ⊆ t :=
sdiff_eq_bot_iff

-- TODO: move to `data.set.finite`.
lemma infinite_of_infinite_sdiff_finite {α : Type*} {s t : set α}
  (hs : s.infinite) (ht : t.finite) : (s \ t).infinite :=
begin
  intro hd,
  have := set.finite.union hd (set.finite.inter_of_right ht s),
  rw set.diff_union_inter at this,
  exact hs this,
end

-- TODO: move to `data.set.finite`.
lemma exists_gt_of_infinite (s : set ℕ) (i : infinite s) (n : ℕ) : ∃ m, m ∈ s ∧ n < m :=
begin
  obtain ⟨m, hm⟩ := set.infinite.nonempty (infinite_of_infinite_sdiff_finite i (set.finite_le_nat n)),
  use m,
  simpa using hm,
end

lemma infinite.exists_not_mem_finset (i : s.infinite) (f : finset α) :
  ∃ a ∈ s, a ∉ f :=
begin
  suffices : (s \ f).nonempty,
  { use this.some,
    have := this.some_spec,
    tauto },
  by_contra h,
  apply i,
  apply finite.subset f.finite_to_set,
  exact (sdiff_eq_empty_iff_subset.mp $ or.resolve_right (eq_empty_or_nonempty _) h),
end

end set

end to_move

namespace nat

variables (p : ℕ → Prop) [decidable_pred p]

/-- Count the `i < n` satisfying `p i`. -/
def count (n : ℕ) : ℕ :=
((list.range n).filter p).length

@[simp] lemma count_zero : count p 0 = 0 :=
by rw [count, range_zero, filter_nil, length]

lemma list.range_one : range 1 = [0] := rfl

lemma list.filter_singleton {α : Type*} (a : α) (p : α → Prop) [decidable_pred p] :
  [a].filter p = if p a then [a] else [] :=
by split_ifs; simp [h]

@[simp] lemma count_one : count p 1 = if p 0 then 1 else 0 :=
begin
  rw [count, list.range_one, list.filter_singleton, apply_ite list.length],
  refl,
end

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

@[simp] lemma count_succ {n : ℕ} : count p (n + 1) = count p n + (if p n then 1 else 0) :=
begin
  suffices : (list.range (n+1)).filter p = ((list.range n).filter p) ++ if p n then [n] else [],
  { split_ifs; simp [h, count, this] },
  rw list.range_succ,
  split_ifs; simp [h]
end

lemma count_succ' : ∀ {n : ℕ}, count p (n + 1) = count (λ k, p (k + 1)) n + (if p 0 then 1 else 0)
| 0     := by simp
| (n+1) := by simpa [@count_succ' n] using add_right_comm _ _ _

lemma count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n :=
by by_cases h : p n; simp [h]

lemma count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n :=
by by_cases h : p n; simp [h]

lemma count_succ_eq_succ_count {n : ℕ} (h : p n) : count p (n + 1) = count p n + 1 :=
by simp [h]

lemma count_succ_eq_count {n : ℕ} (h : ¬p n) : count p (n + 1) = count p n :=
by simp [h]

lemma count_le_card (n : ℕ) : (count p n : cardinal) ≤ cardinal.mk (set_of p) :=
begin
  obtain h | h := lt_or_ge (cardinal.mk (set_of p)) cardinal.omega,
  { haveI := (cardinal.lt_omega_iff_fintype.mp h).some,
    rw [cardinal.fintype_card, cardinal.nat_cast_le, count_eq_card],
    fapply fintype.card_le_of_injective,
    exact λ ⟨i, _, hi⟩, ⟨i, hi⟩,
    tidy },
  { rw le_antisymm ((cardinal.countable_iff _).mp ((set_of p).countable_encodable)) h,
    exact (cardinal.nat_lt_omega _).le },
end

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. -/
noncomputable def nth : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

lemma nth_def (n : ℕ) : nth p n = Inf { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
well_founded.fix_eq _ _ _

lemma nth_zero : nth p 0 = Inf { i : ℕ | p i } :=
by { rw [nth_def], simp, }

@[simp]
lemma nth_zero_of_zero (h : p 0) : nth p 0 = 0 :=
begin
  apply nat.eq_zero_of_le_zero,
  rw nth_def,
  apply nat.Inf_le,
  simp [h],
end

lemma nth_succ_of_zero (h : p 0) (n : ℕ) (w : (n + 2 : cardinal) ≤ cardinal.mk (set_of p)) :
  nth p (n+1) = nth (λ i, p (i+1)) n + 1 :=
begin
  revert w,
  apply nat.strong_induction_on n,
  intros n' ih w,
  replace ih : ∀ m, m < n' → nth (λ i, p (i + 1)) m = nth p (m + 1) - 1 := sorry, -- easy: the extra condition is vacuous + some arithmetic
  rw [nth_def, nth_def],
  simp [ih] {contextual:=tt},
  sorry,
  -- I think this is doable from here!
end

lemma nth_zero_of_exists (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h, }

lemma count_monotone : monotone (count p) :=
begin
  intros n m h,
  rw [count_eq_card, count_eq_card],
  fapply fintype.card_le_of_injective,
  { exact λ i, ⟨i.1, i.2.1.trans_le h, i.2.2⟩ },
  { rintros ⟨n, _⟩ ⟨m, _⟩ h,
    simpa using h },
end

lemma nth_mem_of_infinite_aux (i : set.infinite (set_of p)) (n : ℕ) :
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
    apply set.infinite_of_infinite_sdiff_finite i this, },
  rw nth_def,
  exact Inf_mem ne,
end

lemma nth_mem_of_infinite (i : set.infinite (set_of p)) (n : ℕ) : p (nth p n) :=
(nth_mem_of_infinite_aux p i n).1

lemma nth_strict_mono_of_infinite (i : set.infinite (set_of p)) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p i m).2 _ h

-- eric: i think this needs a cardinal.mk (set_of p) restriction too sadly
lemma nth_of_not_zero (h : ¬ p 0) (k : ℕ) : nth p k = nth (λ i, p (i+1)) k + 1 :=
begin
  apply nat.strong_induction_on k,
  intro k,
  intro w,
  rw [nth_def, nth_def],
  have w' : ∀ m, m < k → nth (λ i, p (i+1)) m = nth p m - 1 := sorry,
  simp [w'] {contextual := tt},
  clear w w',
  sorry --- easy from here.
end

lemma nth_count (n : ℕ) (h : p n) : nth p (count p n) = n :=
begin
  unfreezingI { induction n with n ih generalizing p },
  { simp [h], },
  rw count_succ',
  split_ifs with h',
  { rw nth_succ_of_zero _ h',
    rw ih _ h,
    have := count_le_card p (n+2),
    rw [count_succ', count_succ] at this,
    simp only [h, h', cast_one, if_true, cast_add] at this,
    assumption_mod_cast },
  { simp,
    rw nth_of_not_zero _ h',
    rw ih,
    exact h, },
end

open_locale classical

noncomputable def set.infinite.order_iso_nat {s : set ℕ} (i : s.infinite) : s ≃o ℕ :=
(strict_mono.order_iso_of_surjective
  (λ n, (⟨nth s n, nth_mem_of_infinite s i n⟩ : s))
  (λ n m h, nth_strict_mono_of_infinite s i h)
  (λ ⟨n, w⟩, ⟨count s n, by simpa using nth_count s n w⟩)).symm

-- Other development, which does not appear necessary for `set.infinite.order_iso_nat`,
-- but may be useful for building the Galois connection:

-- eric: I just realised this isn't true; it's more like `nat.card (set_of p) ≤ n` or some similar
-- condition. Probably just worth removing this lemma.
lemma nth_eq_zero_iff (n : ℕ) : nth p n = 0 ↔ n = 0 ∧ p 0 ∨ set_of p = ∅ :=
begin
  rw nth,
  split,
  { simp only [nat.not_lt_zero, set.mem_set_of_eq, Inf_eq_zero],
    rintro (⟨hp0, hn⟩ | rhs),
    { rw eq_bot_of_minimal hn,
      exact or.inl ⟨rfl, hp0⟩ },
    { sorry }, },
  { rintro (⟨rfl, hp0⟩ | hnone),
    { simp [hp0] },
    { rw nat.Inf_eq_zero,
      right,
      rw set.set_of_and,
      convert set.empty_inter _ } }
end

lemma count_nth_of_lt_card (n : ℕ) (w : (n : cardinal) < cardinal.mk { i | p i }) :
  count p (nth p n) = n :=
begin
  casesI fintype_or_infinite {i | p i},
  { sorry },
  { sorry }
end

lemma nth_mem_of_lt_card (n : ℕ) (w : (n : cardinal) < cardinal.mk { i | p i }) :
  p (nth p n) :=
begin
  casesI fintype_or_infinite {i | p i},
  { rw [cardinal.fintype_card, cardinal.nat_cast_lt, ←nat.card_eq_fintype_card] at w,
    sorry, },
  { apply nth_mem_of_infinite,
    rwa ←set.infinite_coe_iff, },
end

lemma count_nth_of_infinite (i : set.infinite p) (n : ℕ) : count p (nth p n) = n :=
sorry

lemma count_nth_gc (i : set.infinite p) : galois_connection (count p) (nth p) :=
begin
  rintro x y,
  rw [nth, le_cInf_iff (⟨0, λ _ _, zero_le _⟩ : bdd_below _)],
  dsimp,
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

lemma nth_le_of_le_count (a b : ℕ) (h : a ≤ count p b) : nth p a ≤ b :=
begin
  sorry
end

lemma nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n :=
sorry


end nat

import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard
import data.nat.lattice
import data.finset.intervals
import order.order_iso_nat

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

## Main results:

* `set.infinite.order_iso_nat`: An infinite set of natural numbers is order-isomorphic to the
  natural numbers.
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
  obtain ⟨m, hm⟩ := (infinite_of_infinite_sdiff_finite i $ set.finite_le_nat n).nonempty,
  exact ⟨m, by simpa using hm⟩
end

lemma infinite.exists_not_mem_finset (i : s.infinite) (f : finset α) : ∃ a ∈ s, a ∉ f :=
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

variable (p : ℕ → Prop)

section count

variable [decidable_pred p]

/-- Count the `i < n` satisfying `p i`. -/
def count (n : ℕ) : ℕ :=
((list.range n).filter p).length

@[simp] lemma count_zero : count p 0 = 0 :=
by rw [count, range_zero, filter_nil, length]

lemma list.range_one : range 1 = [0] := rfl

lemma list.filter_singleton {α : Type*} (a : α) (p : α → Prop) [decidable_pred p] :
  [a].filter p = if p a then [a] else [] :=
by split_ifs; simp [h]

noncomputable instance count_set_fintype (p : ℕ → Prop) (n : ℕ) : fintype { i | i < n ∧ p i } :=
fintype.of_injective (λ i, (⟨i.1, i.2.1⟩ : { i | i < n })) (by tidy)

lemma count_eq_card_finset (n : ℕ) : count p n = finset.card (finset.filter p (finset.range n)) :=
rfl

/-- `count p n` can be expressed as the cardinality of `{ i | i ≤ n ∧ p i }`. -/
lemma count_eq_card (n : ℕ) : count p n = fintype.card { i : ℕ | i < n ∧ p i } :=
begin
  rw [←set.to_finset_card, count_eq_card_finset],
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

lemma count_one : count p 1 = if p 0 then 1 else 0 := by simp

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

lemma count_monotone : monotone (count p) :=
λ x y h, length_le_of_sublist $ filter_sublist_filter p $ range_sublist.mpr h

lemma count_lt_of_lt (x y : ℕ) (hc : count p x < count p y) : x < y :=
(count_monotone p).reflect_lt hc

end count

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. -/
noncomputable def nth : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

lemma nth_def (n : ℕ) : nth p n = Inf { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
well_founded.fix_eq _ _ _

instance decidable_pred_mem_set_of [decidable_pred p] : decidable_pred (∈ set_of p) :=
by assumption

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

-- This should probably be moved to data.nat.lattice
lemma Inf_plus {n: ℕ} {p: set ℕ} (h: 0 < Inf {m : ℕ | p m}) :
  Inf {m : ℕ | p m} + n = Inf {m : ℕ | p (m - n)} :=
begin
  have hp: ¬ p 0 := not_mem_of_lt_Inf h,
  have hne: p.nonempty := nonempty_of_pos_Inf h,
  apply eq.symm,
  rw Inf_def,
  { erw nat.find_eq_iff,
    simp,
    split,
    { rw set_of,
      apply Inf_mem hne, },
    { intros k hk hpk,
      have hkle: n ≤ k,
      { apply le_of_lt,
        rw ← sub_pos_iff_lt,
        rw pos_iff_ne_zero,
        intro hkn,
        rw hkn at hpk,
        apply hp,
        exact hpk, },
      have hkI: k - n < Inf (set_of p) := (sub_lt_iff_right hkle).mpr hk,
      rw set_of at hkI,
      exact not_mem_of_lt_Inf hkI hpk, }, },
  { cases hne with t ht,
    use t + n,
    simp,
    exact ht,},
end

lemma nth_succ_of_zero (h : p 0) (n : ℕ) (w : (n + 2 : cardinal) ≤ cardinal.mk (set_of p)) :
  nth p (n + 1) = nth (λ i, p (i + 1)) n + 1 :=
begin
  revert w,
  apply nat.strong_induction_on n,
  intros n' ih w,
  replace ih : ∀ m, m < n' → nth (λ i, p (i + 1)) m = nth p (m + 1) - 1,
  { intros m hm,
    specialize ih m hm (le_trans _ w),
    { norm_cast,
      exact le_of_lt (add_lt_add_right hm 2), },
    simp [ih], },
  rw [nth_def, nth_def],
  simp [ih] {contextual:=tt},
  obtain h0 | hlt := nat.eq_zero_or_pos (Inf {i | p (i + 1) ∧ ∀ k, k < n' → nth p (k + 1) - 1 < i}),
  { rw [h0, zero_add],
    simp at h0,
    obtain ⟨hp, h0⟩ | h0 := h0,
    { rw nonpos_iff_eq_zero.mp (not_lt.mp $ h0 0),
      simp only [lt_one_iff, forall_eq, nth_zero_of_zero _ h],
      rw Inf_def,
      { erw nat.find_eq_iff,
        refine ⟨by simpa, λ m hm, _⟩,
        rw nat.lt_one_iff at hm,
        simp [hm] },
      { exact ⟨1, by simpa⟩ } },
    { sorry } },
  { rw Inf_plus hlt,
    { sorry } }
end

lemma nth_zero_of_exists [decidable_pred p] (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h, }

/--
When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`.
-/
lemma nth_eq_order_iso_of_nat [decidable_pred p] (i : infinite (set_of p)) (n : ℕ) :
  nth p n = nat.subtype.order_iso_of_nat (set_of p) n :=
sorry

lemma nth_set_card_aux {n: ℕ} (hf: set.finite p)
  (hf' :{ i : ℕ | p i ∧ ∀ k < n, nth p k < i }.finite)
  (hle: n ≤ (set.finite.to_finset hf).card):
    (set.finite.to_finset hf').card =
    (set.finite.to_finset hf).card - n :=
begin
  tactic.unfreeze_local_instances,
  induction n with k,
  { have heq: hf.to_finset = hf'.to_finset,
    { ext a,
      simp,
      split,
      { intros hp,
        exact hp, },
      { intros hp,
        exact hp, },},
    rw heq,
    refl, },
  { have hf'': {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k → nth p k_1 < i}.finite,
    { have hsub: {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k → nth p k_1 < i} ⊆ p,
      { intros x hx,
        simp at hx,
        cases hx,
        exact hx_left, },
      exact set.finite.subset hf hsub, },
    specialize n_ih hf'',
    have hk: k ≤ hf.to_finset.card,
    { apply le_trans,
      swap,
      exact hle,
      exact le_succ k, },
    specialize n_ih hk,
    have hm1: hf.to_finset.card - k.succ = (hf.to_finset.card - k) - 1 := rfl,
    rw hm1,
    rw ← n_ih,
    have her: hf'.to_finset = finset.erase hf''.to_finset (nth p k),
    { ext a,
      simp,
      split,
      { intro h,
        cases h with hp hlt,
        split,
        { apply ne_of_gt,
          apply hlt,
          exact lt_add_one k, },
        { split,
          { exact hp, },
            intros n hn,
            apply hlt,
            apply lt_trans,
            { exact hn, },
            { exact lt_add_one k, }, }, },
      { intro h,
        cases h with hak hlt,
        cases hlt with hp hlt,
        split,
        { exact hp,},
        { intros n hn,
          by_cases hnk: n = k,
          { rw hnk,
            apply lt_of_le_of_ne,
            { rw nth,
              apply nat.Inf_le,
              simp,
              split,
              { exact hp, },
              { exact hlt,}, },
            { by_contra,
              simp at h,
              apply hak,
              apply eq.symm,
              apply h, }, },
          { apply hlt,
            apply lt_of_le_of_ne,
            { exact lt_succ_iff.mp hn,},
            { exact hnk,}, }, }, }, },
    rw her,
    apply finset.card_erase_of_mem,
    have hn: {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k → nth p k_1 < i}.nonempty,
    { have hfn: (hf''.to_finset).nonempty,
      { rw ← finset.card_pos,
        rw n_ih,
        apply nat.sub_pos_of_lt,
        exact hle, },
      exact (set.finite.to_finset.nonempty hf'').mp hfn, },
    have hI: nth p k ∈ {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k → nth p k_1 < i},
    { rw nth,
      apply Inf_mem,
      exact hn, },
    simp at hI,
    simp,
    exact hI, },
end

lemma nth_set_card {n: ℕ} (hf: set.finite p)
  (hf' :{ i : ℕ | p i ∧ ∀ k < n, nth p k < i }.finite):
    (set.finite.to_finset hf').card =
    (set.finite.to_finset hf).card - n :=
begin
  by_cases hle: n ≤ (set.finite.to_finset hf).card,
  { apply nth_set_card_aux,
    exact hle, },
  { simp at hle,
    have hf'': {i : ℕ | p i ∧ ∀ (k : ℕ),
      k < (set.finite.to_finset hf).card → nth p k < i}.finite,
    { apply set.finite.subset,
      exact hf,
      intro x,
      simp,
      intros hp h,
      exact hp, },
    have h0: hf''.to_finset.card = hf.to_finset.card - hf.to_finset.card,
    { apply nth_set_card_aux,
      refl, },
    simp at h0,
    have hn0: hf.to_finset.card - n = 0,
    { apply nat.sub_eq_zero_of_le,
      exact le_of_lt hle },
    rw hn0,
    simp,
    have hsub: {i : ℕ | p i ∧ ∀ (k : ℕ), k < n → nth p k < i} ⊆ ∅,
    { rw ← h0,
      intro x,
      simp,
      intros hp h,
      split,
      { exact hp,},
      { intros m hm,
        apply h,
        apply lt_trans,
        { exact hm, },
        { exact hle, }, }, },
    exact eq_bot_iff.mpr hsub,
  }
end

lemma nth_mem_of_infinite_aux (i : (set_of p).infinite) (n : ℕ) :
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

lemma nth_mem_of_infinite (i : (set_of p).infinite) (n : ℕ) : p (nth p n) :=
(nth_mem_of_infinite_aux p i n).1

lemma nth_strict_mono_of_infinite (i : (set_of p).infinite) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p i m).2 _ h

lemma nth_monotone_of_infinite (i : (set_of p).infinite) : monotone (nth p) :=
(nth_strict_mono_of_infinite p i).monotone

lemma nth_nonzero_of_ge_nonzero (h : ¬p 0) (k : ℕ) (h : nth p k ≠ 0) : ∀ a ≤ k, nth p a ≠ 0 :=
sorry

lemma nth_of_not_zero (h : ¬ p 0) (k : ℕ) (h : nth p k ≠ 0) : nth p k = nth (λ i, p (i+1)) k + 1 :=
begin
  revert h,
  apply nat.strong_induction_on k,
  clear k,
  intros a b ha,
  rw [nth_def, nth_def],
  have w' : ∀ m, m < a → nth (λ i, p (i+1)) m = nth p m - 1,
  { intros m hm,
    specialize b m hm (nth_nonzero_of_ge_nonzero _ h a ha m hm.le),
    rw b,
    simp },
  simp [w'] {contextual := tt},
  sorry --- easy from here.
end

lemma nth_count_le [decidable_pred p] (i: set.infinite p) (n : ℕ): n ≤ nth p (count p n) :=
sorry

lemma nth_count [decidable_pred p] (n : ℕ) (h : p n) : nth p (count p n) = n :=
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
  { obtain hcz | hcz := eq_or_ne (nth p (count (λ k, p (k + 1)) n + if p 0 then 1 else 0)) 0,
    { exfalso,
      rw ←count_succ' at hcz,
      have hcz' := hcz,
      rw [nth_def, Inf_eq_zero] at hcz,
      dsimp at hcz,
      obtain _ | hcz := hcz,
      { tauto },
      rw set.eq_empty_iff_forall_not_mem at hcz,
      specialize hcz n.succ,
      refine hcz ⟨h, _⟩,
      /- ⊢ ∀ (k : ℕ), k < count p (n + 1) → nth p k < n.succ,
      but we have hcz' : nth p (count p (n + 1)) = 0 -/
      sorry },
    { simp [h'] at ⊢ hcz,
      rw nth_of_not_zero _ h' _ hcz,
      rw ih,
      exact h } },
end

open_locale classical

variable [decidable_pred p]

lemma count_nth_of_infinite (i : set.infinite p) (n : ℕ) : count p (nth p n) = n :=
begin
  induction n with k,
  { rw count_eq_card_finset,
    simp,
    ext,
    simp,
    intros ha,
    rw nth at ha,
    have hn: a ∉ {i : ℕ | p i ∧ ∀ (k : ℕ), k < 0 → nth p k < i} := not_mem_of_lt_Inf ha,
    simp at hn,
    exact hn, },
  { rw count_eq_card_finset,
    have ih: finset.filter p (finset.range (nth p k.succ)) =
      insert (nth p k) (finset.filter p (finset.range (nth p k))),
    { ext,
      simp,
      split,
      { intro h,
        cases h with ha hp,
        have hle: a ≤ nth p k,
        { rw nth at ha,
          by_contra,
          simp at h,
          have haI: Inf {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k.succ → nth p k_1 < i} ≤ a,
          { apply nat.Inf_le,
            { simp,
              split,
              { exact hp, },
              { intros m hm,
                apply lt_of_le_of_lt,
                { apply nth_monotone_of_infinite,
                  { exact i, },
                  rw ← lt_succ_iff,
                  exact hm, },
                  exact h, }, }, },
          exact lt_le_antisymm ha haI, },
        by_cases a = nth p k,
        { left,
          exact h, },
        { right,
          split,
          { exact (ne.le_iff_lt h).mp hle},
          { exact hp, }, }, },
      { intro h,
        cases h,
        { rw h,
          split,
          { apply nth_strict_mono_of_infinite,
            exact i,
            exact lt_add_one k},
          { apply nth_mem_of_infinite,
            apply i, }, },
          { cases h with ha hp,
            split,
            { apply lt_trans ha,
              apply nth_strict_mono_of_infinite,
              exact i,
              exact lt_add_one k },
            { exact hp, }, }, }, },
    rw ih,
    rw finset.card_insert_of_not_mem,
    { rw ← count_eq_card_finset,
      rw n_ih, },
    { simp, },
  },
end

lemma count_nth_gc (i : set.infinite p) : galois_connection (count p) (nth p) :=
begin
  rintro x y,
  rw [nth, le_cInf_iff (⟨0, λ _ _, zero_le _⟩ : bdd_below _)],
  { dsimp,
    refine ⟨_, λ h, _⟩,
    { rintro hxy n ⟨hn, h⟩,
      obtain rfl | hne := eq_or_ne y (count p x),
      { specialize h (count p n),
        replace hn : nth p (count p n) = n := nth_count _ _ hn,
        replace h : count p x ≤ count p n := by rwa [hn, lt_self_iff_false, imp_false, not_lt] at h,
        apply le_trans,
        { apply nth_count_le p,
          exact i},
        rw ← hn,
        exact nth_monotone_of_infinite p i h },
      { have hlt : count p x < y := (ne.le_iff_lt hne.symm).mp hxy,
        specialize h (count p x) hlt,
        apply le_trans,
        { apply nth_count_le p,
          exact i},
        { apply le_of_lt h} } },
    { specialize h (nth p y),
      have hp : p (nth p y) := nth_mem_of_infinite p i _,
      have hs : (∀ (k : ℕ), k < y → nth p k < nth p y) → x ≤ nth p y := by tauto,
      specialize hs (λ k h, nth_strict_mono_of_infinite p i h),
      have hy : count p (nth p y) = y := count_nth_of_infinite p i _,
      rw ← hy,
      exact count_monotone _ hs } },
  use nth p y,
  apply nth_mem_of_infinite_aux p i,
end

lemma count_le_iff_le_nth {p} (i : set.infinite p) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b :=
count_nth_gc p i _ _

lemma lt_nth_iff_count_lt {p} (i : set.infinite p) {a b : ℕ} :
  a < count p b ↔ nth p a < b :=
lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth i


lemma nth_le_of_le_count (a b : ℕ) (h : a ≤ count p b) : nth p a ≤ b :=
begin
  sorry
end

lemma nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n :=
sorry

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

end nat

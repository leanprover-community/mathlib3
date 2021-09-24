/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import data.list.basic
import data.nat.prime
import order.order_iso_nat
import set_theory.fincard

/-!

# Counting on ℕ

This files defines ways to get basic properties of a predicate on ℕ, such as "how many numbers
under `k` satisfy the predicate" and "what is the `n`th number that satisifies this predicate".
We define these as two functions, `count` and `nth`, that answer these questions, and prove
the expected theorems about them.

## Main definitions

* `count p n`: The number of naturals `k < n` such that `p k`.
* `nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nth p n = 0`.

## Main results

* `set.infinite.order_iso_nat`: An infinite set of natural numbers is order-isomorphic to the
  natural numbers.
-/

open finset

namespace nat
variable (p : ℕ → Prop)

section count
variable [decidable_pred p]

/-- Count the number of naturals `k < n` satisfying `p k`. -/
def count (n : ℕ) : ℕ := ((list.range n).filter p).length

@[simp] lemma count_zero : count p 0 = 0 :=
by rw [count, list.range_zero, list.filter_nil, list.length]

instance count_set_fintype (n : ℕ) : fintype {i | i < n ∧ p i} :=
fintype.of_finset ((finset.range n).filter p) (by simp)

lemma count_eq_card_finset (n : ℕ) : count p n = ((range n).filter p).card := rfl

/-- `count p n` can be expressed as the cardinality of `{ i | i ≤ n ∧ p i }`. -/
lemma count_eq_card_fintype (n : ℕ) : count p n = fintype.card { i : ℕ | i < n ∧ p i } :=
begin
  rw [←set.to_finset_card, count_eq_card_finset],
  congr' 1,
  ext i,
  simp [lt_succ_iff],
end

@[simp] lemma count_succ {n : ℕ} : count p (n + 1) = count p n + (if p n then 1 else 0) :=
by split_ifs; simp [count, list.range_succ, h]

lemma count_succ' : ∀ {n : ℕ}, count p (n + 1) = count (λ k, p (k + 1)) n + (if p 0 then 1 else 0)
| 0     := by simp
| (n+1) := by simpa [@count_succ' n] using add_right_comm _ _ _

lemma count_succ_eq_succ_count_iff {n : ℕ} : count p (n + 1) = count p n + 1 ↔ p n :=
by by_cases h : p n; simp [h]

lemma count_succ_eq_count_iff {n : ℕ} : count p (n + 1) = count p n ↔ ¬p n :=
by by_cases h : p n; simp [h]

lemma count_succ_eq_succ_count {n : ℕ} (h : p n) : count p (n + 1) = count p n + 1 :=
(count_succ_eq_succ_count_iff p).mpr h

lemma count_succ_eq_count {n : ℕ} (h : ¬p n) : count p (n + 1) = count p n :=
(count_succ_eq_count_iff p).mpr h

lemma count_one : count p 1 = if p 0 then 1 else 0 := by simp

lemma count_le_card (n : ℕ) : (count p n : cardinal) ≤ cardinal.mk (set_of p) :=
begin
  obtain h | h := lt_or_ge (cardinal.mk (set_of p)) cardinal.omega,
  { haveI := (cardinal.lt_omega_iff_fintype.mp h).some,
    rw [cardinal.fintype_card, cardinal.nat_cast_le, count_eq_card_fintype],
    fapply fintype.card_le_of_injective,
    exact λ ⟨i, _, hi⟩, ⟨i, hi⟩,
    tidy },
  { rw le_antisymm ((cardinal.countable_iff _).mp ((set_of p).countable_encodable)) h,
    exact (cardinal.nat_lt_omega _).le },
end

lemma count_monotone : monotone (count p) :=
λ x y h, list.length_le_of_sublist $ (list.range_sublist.mpr h).filter p

lemma count_lt_of_lt (x y : ℕ) (hc : count p x < count p y) : x < y :=
(count_monotone p).reflect_lt hc

end count

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. -/
noncomputable def nth : ℕ → ℕ
| n := Inf { i : ℕ | p i ∧ ∀ k < n, nth k < i }

instance decidable_pred_mem_set_of [h : decidable_pred p] : decidable_pred (∈ set_of p) := h

lemma nth_zero : nth p 0 = Inf { i : ℕ | p i } := by { rw nth, simp }

@[simp]
lemma nth_zero_of_zero (h : p 0) : nth p 0 = 0 :=
begin
  apply nat.eq_zero_of_le_zero,
  rw nth,
  apply nat.Inf_le,
  simp [h],
end

lemma nth_zero_of_exists [decidable_pred p] (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h }

lemma nth_set_card_aux {n : ℕ} (hf : (set_of p).finite)
  (hf' : {i : ℕ | p i ∧ ∀ t < n, nth p t < i}.finite) (hle : n ≤ hf.to_finset.card) :
  hf'.to_finset.card = hf.to_finset.card - n :=
begin
  unfreezingI { induction n with k hk },
  { congr,
    simp only [forall_false_left, nat.not_lt_zero, forall_const, and_true] },
  have hf'': {i : ℕ | p i ∧ ∀ t, t < k → nth p t < i}.finite,
  { refine hf.subset (λ x hx, _),
    rw set.mem_set_of_eq at hx,
    exact hx.left, },
  have hle' := nat.sub_pos_of_lt hle,
  specialize hk hf'' (k.le_succ.trans hle),
  rw [nat.sub_succ', ←hk],
  convert_to (finset.erase hf''.to_finset (nth p k)).card = _,
  { congr,
    ext a,
    simp only [set.finite.mem_to_finset, ne.def, set.mem_set_of_eq, finset.mem_erase],
    refine ⟨λ ⟨hp, hlt⟩,
              ⟨(hlt _ (lt_add_one k)).ne', ⟨hp, λ n hn, hlt n (hn.trans_le k.le_succ)⟩⟩, _⟩,
    rintro ⟨hak, hp, hlt⟩,
    refine ⟨hp, λ n hn, _⟩,
    obtain rfl | hnk := eq_or_ne n k,
    { refine lt_of_le_of_ne _ (ne.symm hak),
      rw nth,
      apply nat.Inf_le,
      simpa [hp] using hlt, },
    { apply hlt,
      exact (le_of_lt_succ hn).lt_of_ne hnk } },
  apply finset.card_erase_of_mem,
  rw [nth, set.finite.mem_to_finset],
  apply Inf_mem,
  rwa [←set.finite.to_finset.nonempty hf'', ←finset.card_pos, hk]
end

lemma nth_set_card {n : ℕ} (hf : (set_of p).finite)
  (hf' : {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.finite) :
  hf'.to_finset.card = hf.to_finset.card - n :=
begin
  obtain hle | hle := le_or_lt n hf.to_finset.card,
  { exact nth_set_card_aux p hf _ hle, },
  { rw (nat.sub_eq_zero_of_le hle.le),
    simp only [finset.card_eq_zero, set.finite_to_finset_eq_empty_iff, ←set.subset_empty_iff],
    convert_to _ ⊆ {i : ℕ | p i ∧ ∀ (k : ℕ), k < hf.to_finset.card → nth p k < i},
    { symmetry,
      rw [←set.finite_to_finset_eq_empty_iff, ←finset.card_eq_zero,
          ←nat.sub_self hf.to_finset.card],
      { apply nth_set_card_aux p hf _ le_rfl, },
      { apply hf.subset,
        simp {contextual := tt}, } },
    intro x,
    simp only [true_and, and_imp, set.mem_set_of_eq] { contextual := tt },
    intros hp h m hm,
    apply h,
    exact hm.trans hle, },
end

lemma nth_set_nonempty_of_lt_card {n : ℕ} (hf : (set_of p).finite)
  (hlt: n < hf.to_finset.card) :
  {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.nonempty :=
begin
  have hf': {i : ℕ | p i ∧ ∀ (k : ℕ), k < n → nth p k < i}.finite,
  { apply hf.subset,
    simp { contextual := tt }, },
  rw [←set.finite.to_finset.nonempty hf', ←finset.card_pos, nth_set_card p hf],
  exact nat.sub_pos_of_lt hlt,
end

lemma nth_mem_of_lt_card_finite_aux (n : ℕ) (hf : (set_of p).finite) (hlt : n < hf.to_finset.card) :
  nth p n ∈ {i : ℕ | p i ∧ ∀ k < n, nth p k < i} :=
begin
  rw nth,
  apply Inf_mem,
  apply nth_set_nonempty_of_lt_card _ _ hlt,
end

lemma nth_mem_of_lt_card_finite {n : ℕ} (hf : (set_of p).finite) (hlt : n < hf.to_finset.card) :
  p (nth p n) := (nth_mem_of_lt_card_finite_aux p n hf hlt).1

lemma nth_strict_mono_finite {m n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) (hmn : m < n) : nth p m < nth p n :=
(nth_mem_of_lt_card_finite_aux p _ hf hlt).2 _ hmn

lemma nth_mem_of_infinite_aux (i : (set_of p).infinite) (n : ℕ) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  rw nth,
  apply Inf_mem,
  let s : set ℕ := ⋃ (k < n), { i : ℕ | nth p k ≥ i },
  convert_to ((set_of p) \ s).nonempty,
  { ext i,
    simp, },
  apply set.infinite.nonempty,
  apply i.diff,
  apply set.finite.bUnion (set.finite_lt_nat _),
  intros k h,
  apply set.finite_le_nat,
end

lemma nth_mem_of_infinite (i : (set_of p).infinite) (n : ℕ) : p (nth p n) :=
(nth_mem_of_infinite_aux p i n).1

lemma nth_strict_mono_of_infinite (i : (set_of p).infinite) : strict_mono (nth p) :=
λ n m h, (nth_mem_of_infinite_aux p i m).2 _ h

lemma nth_monotone_of_infinite (i : (set_of p).infinite) : monotone (nth p) :=
(nth_strict_mono_of_infinite p i).monotone

lemma nth_monotone_finite {m n : ℕ} (hf : (set_of p).finite) (hlt : n < hf.to_finset.card)
  (hmn: m ≤ n) : nth p m ≤ nth p n :=
begin
  apply le_of_lt_or_eq,
  obtain rfl | h := eq_or_ne m n,
  { exact or.inr rfl },
  { exact or.inl (nth_strict_mono_finite p hf hlt ((ne.le_iff_lt h).mp hmn)) }
end

lemma le_nth_of_lt_nth_succ_finite {k a : ℕ} (hf : (set_of p).finite)
  (hlt : k.succ < hf.to_finset.card) (h : a < nth p k.succ) (hp : p a) :
  a ≤ (nth p) k :=
begin
  by_contra hak,
  push_neg at hak,
  refine lt_le_antisymm h _,
  rw nth,
  apply nat.Inf_le,
  refine ⟨hp, λ n hn, lt_of_le_of_lt _ hak⟩,
  exact nth_monotone_finite p hf ((k.le_succ).trans_lt hlt) (lt_succ_iff.mp hn),
end

lemma le_nth_of_lt_nth_succ_infinite {k a : ℕ} (i : (set_of p).infinite)
  (h : a < nth p k.succ) (hp : p a) :
  a ≤ (nth p) k :=
begin
  by_contra hak,
  push_neg at hak,
  refine lt_le_antisymm h _,
  rw nth,
  apply nat.Inf_le,
  refine ⟨hp, λ n hn, lt_of_le_of_lt _ hak⟩,
  apply nth_monotone_of_infinite p i,
  exact lt_succ_iff.mp hn,
end

section count
variables [decidable_pred p]

@[simp] lemma count_nth_of_zero : count p (nth p 0) = 0 :=
begin
  rw [count_eq_card_finset, finset.card_eq_zero, nth_zero],
  ext a,
  simp only [finset.not_mem_empty, not_and, finset.mem_filter, finset.mem_range, iff_false],
  intros ha hp,
  exact lt_le_antisymm ha (nat.Inf_le hp),
end

lemma filter_range_nth_eq_insert_of_finite (hf : (set_of p).finite) {k : ℕ}
  (hlt : k.succ < hf.to_finset.card) :
  finset.filter p (finset.range (nth p k.succ)) =
    insert (nth p k) (finset.filter p (finset.range (nth p k))) :=
begin
  ext a,
  simp only [finset.mem_insert, finset.mem_filter, finset.mem_range],
  split,
  { rintro ⟨ha, hp⟩,
    refine or_iff_not_imp_left.mpr (λ h, ⟨lt_of_le_of_ne _ h, hp⟩),
    exact le_nth_of_lt_nth_succ_finite p hf hlt ha hp, },
  { rintro (ha | ⟨ha, hp⟩),
    { rw ha,
      refine ⟨nth_strict_mono_finite p hf hlt (lt_add_one _), _⟩,
      apply nth_mem_of_lt_card_finite p hf,
      exact (k.le_succ).trans_lt hlt },
    refine ⟨ha.trans _, hp⟩,
    exact nth_strict_mono_finite p hf hlt (lt_add_one _), },
end

lemma count_nth_of_lt_card_finite {n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) : count p (nth p n) = n :=
begin
  induction n with k hk,
  { apply count_nth_of_zero },
  rw [count_eq_card_finset, filter_range_nth_eq_insert_of_finite p hf hlt,
      finset.card_insert_of_not_mem],
  { rw [←count_eq_card_finset, hk],
    exact lt_of_succ_lt hlt, },
  { simp }
end

lemma filter_range_nth_eq_insert_of_infinite (i : (set_of p).infinite) (k : ℕ) :
  (finset.range (nth p k.succ)).filter p = insert (nth p k) ((finset.range (nth p k)).filter p) :=
begin
  ext a,
  simp only [finset.mem_insert, finset.mem_filter, finset.mem_range],
  split,
  { rintro ⟨ha, hp⟩,
    refine or_iff_not_imp_left.mpr (λ hne, ⟨_, hp⟩),
    rw ←ne.le_iff_lt hne,
    by_contra h,
    push_neg at h,
    rw nth at ha,
    refine lt_le_antisymm ha (nat.Inf_le _),
    simp only [hp, true_and, set.mem_set_of_eq],
    refine λ m hm, lt_of_le_of_lt _ h,
    apply nth_monotone_of_infinite p i,
    exact lt_succ_iff.mp hm, },
  { rintro (rfl | ⟨ha, hp⟩),
    { refine ⟨_, nth_mem_of_infinite p i _⟩,
      exact nth_strict_mono_of_infinite p i (lt_add_one k) },
    { refine ⟨ha.trans _, hp⟩,
      apply nth_strict_mono_of_infinite p i (lt_add_one k) } }
end

lemma count_nth_of_infinite (i : (set_of p).infinite) (n : ℕ) : count p (nth p n) = n :=
begin
  induction n with k hk,
  { apply count_nth_of_zero },
  rw [count_eq_card_finset, filter_range_nth_eq_insert_of_infinite p i,
      finset.card_insert_of_not_mem],
  { rw [←count_eq_card_finset, hk] },
  { simp }
end

lemma count_strict_mono {m n : ℕ} (hm : p m) (hmn : m < n) : count p m < count p n :=
begin
  rw [count_eq_card_finset, count_eq_card_finset],
  apply finset.card_lt_card,
  refine ⟨λ a, _, _⟩,
  { simp only [and_imp, mem_filter, mem_range],
    exact λ ha hp, ⟨ha.trans hmn, hp⟩ },
  { rw finset.not_subset,
    exact ⟨m, by simp [hm, hmn]⟩ },
end

lemma count_injective {m n : ℕ} (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n :=
begin
  by_contra,
  wlog hmn : m < n,
  { exact ne.lt_or_lt h },
  { simpa [heq] using count_strict_mono _ hm hmn, },
end

lemma nth_count_of_infinite {n : ℕ} (i : (set_of p).infinite) (hp : p n) :
  nth p (count p n) = n :=
begin
  apply count_injective p (nth_mem_of_infinite _ i _) hp,
  apply count_nth_of_infinite p i,
end

lemma count_lt_card {n : ℕ} (hf : (set_of p).finite) (hp : p n) :
  count p n < hf.to_finset.card :=
begin
  rw count_eq_card_finset,
  refine finset.card_lt_card ⟨λ _, by simp {contextual := tt}, _⟩,
  rw finset.not_subset,
  exact ⟨n, by simp [hp]⟩
end

lemma nth_count_of_finite {n : ℕ} (hf : (set_of p).finite) (hp : p n) :
  nth p (count p n) = n :=
begin
  refine count_injective p _ hp _,
  { apply nth_mem_of_lt_card_finite p hf,
    exact count_lt_card p hf hp, },
  { exact count_nth_of_lt_card_finite _ _ (count_lt_card _ hf hp), },
end

lemma nth_count {n : ℕ} (hp : p n) : nth p (count p n) = n :=
begin
  obtain hfi | hinf := em (set.finite p),
  { exact nth_count_of_finite p hfi hp, },
  { exact nth_count_of_infinite p hinf hp, },
end

lemma nth_count_eq_Inf {n : ℕ} : nth p (count p n) = Inf {i : ℕ | p i ∧ n ≤ i} :=
begin
  rw nth,
  congr,
  ext a,
  simp only [set.mem_set_of_eq, and.congr_right_iff],
  intro hp,
  refine ⟨λ h, _, λ hn k hk, lt_of_lt_of_le _ hn⟩,
  { by_contra ha,
    simp only [not_le] at ha,
    have hn : nth p (count p a) < a := h _ (count_strict_mono p hp ha),
    rwa [nth_count p hp, lt_self_iff_false] at hn },
  { apply count_lt_of_lt p,
    convert hk,
    obtain hfi | hfi : set.finite p ∨ set.infinite p := em (set.finite p),
    { rw count_nth_of_lt_card_finite _ hfi,
      exact hk.trans ((count_monotone _ hn).trans_lt (count_lt_card _ hfi hp)) },
    { apply count_nth_of_infinite p hfi } },
end

lemma nth_count_le (i : (set_of p).infinite) (n : ℕ) : n ≤ nth p (count p n) :=
begin
  rw nth_count_eq_Inf,
  suffices h : Inf {i : ℕ | p i ∧ n ≤ i} ∈ {i : ℕ | p i ∧ n ≤ i},
  { exact h.2 },
  apply Inf_mem,
  obtain ⟨m, hp, hn⟩ := i.exists_nat_lt n,
  exact ⟨m, hp, hn.le⟩
end

lemma count_nth_gc (i : (set_of p).infinite) : galois_connection (count p) (nth p) :=
begin
  rintro x y,
  rw [nth, le_cInf_iff (⟨0, λ _ _, zero_le _⟩ : bdd_below _)],
  { dsimp,
    refine ⟨_, λ h, _⟩,
    { rintro hxy n ⟨hn, h⟩,
      obtain rfl | hne := eq_or_ne y (count p x),
      { specialize h (count p n),
        replace hn : nth p (count p n) = n := nth_count _ hn,
        replace h : count p x ≤ count p n := by rwa [hn, lt_self_iff_false, imp_false, not_lt] at h,
        refine (nth_count_le p i x).trans _,
        rw ← hn,
        exact nth_monotone_of_infinite p i h },
      { have hlt : count p x < y := (ne.le_iff_lt hne.symm).mp hxy,
        exact (nth_count_le p i x).trans (h (count p x) hlt).le } },
    { specialize h (nth p y),
      have hp := nth_mem_of_infinite p i y,
      have hs : (∀ (k : ℕ), k < y → nth p k < nth p y) → x ≤ nth p y := by tauto,
      rw ←count_nth_of_infinite p i y,
      exact count_monotone _ (hs (λ k h, nth_strict_mono_of_infinite p i h)) } },
  exact ⟨nth p y, nth_mem_of_infinite_aux p i y⟩
end

lemma count_le_iff_le_nth (i : (set_of p).infinite) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b := count_nth_gc p i _ _

lemma lt_nth_iff_count_lt (i : (set_of p).infinite) {a b : ℕ} :
  a < count p b ↔ nth p a < b := lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth p i

lemma lt_of_count_lt {a b : ℕ} (h: count p a < count p b): a < b :=
begin
  simp only [count_eq_card_finset] at h,
  by_contra hab,
  push_neg at hab,
  apply (lt_iff_not_ge _ _).mp h,
  apply finset.card_le_of_subset,
  simp only [finset.subset_iff, and_imp, finset.mem_filter, finset.mem_range],
  refine λ x hx hp, ⟨hx.trans_le hab, hp⟩
end

lemma nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n :=
begin
  obtain hfi | hinf := em (set.finite p),
  { have hio : count p (nth p k) < count p n,
    { rwa count_nth_of_lt_card_finite,
      { refine h.trans_le _,
        { exact hfi }, -- rogue goal
        simp [count_eq_card_finset, finset.card_le_of_subset, finset.subset_iff] } },
    apply lt_of_count_lt p hio },
  { rwa ← lt_nth_iff_count_lt,
    exact hinf }
end

lemma le_nth_of_count_le (n k : ℕ) (h: n ≤ nth p k) : count p n ≤ k :=
begin
  by_contra hc,
  apply not_lt.mpr h,
  apply nth_lt_of_lt_count,
  simpa using hc
end

lemma count_nth_of_lt_card (n : ℕ) (w : (n : cardinal) < cardinal.mk (set_of p)) :
  count p (nth p n) = n :=
begin
  casesI fintype_or_infinite (set_of p) with hf hi,
  { apply count_nth_of_lt_card_finite _ (⟨hf⟩ : set.finite _),
    rw set.finite.card_to_finset,
    rw cardinal.fintype_card at w,
    assumption_mod_cast },
  { apply count_nth_of_infinite,
    rwa set.infinite_coe_iff at hi }
end

end count

lemma nth_mem_of_lt_card (n : ℕ) (w : (n : cardinal) < cardinal.mk (set_of p)) : p (nth p n) :=
begin
  casesI fintype_or_infinite (set_of p) with hf hi,
  { apply nth_mem_of_lt_card_finite _ (⟨hf⟩ : set.finite _),
    rw set.finite.card_to_finset,
    rw cardinal.fintype_card at w,
    assumption_mod_cast },
  { apply nth_mem_of_infinite,
    rwa set.infinite_coe_iff at hi }
end

lemma nth_nonzero_of_ge_nonzero (h : ¬p 0) (a k : ℕ) (ha: a ≤ k) (h : nth p k ≠ 0) :
  nth p a ≠ 0 :=
begin
  refine λ h0, h _,
  rw [nth, Inf_eq_zero] at ⊢ h0,
  right,
  cases h0,
  { simp only [nat.not_lt_zero, set.mem_set_of_eq] at h0,
    tauto },
  { apply set.eq_empty_of_subset_empty,
    rw ← h0,
    intro x,
    simp only [and_imp, set.mem_set_of_eq],
    exact λ hp hk, ⟨hp, λ m hm, hk _ $ hm.trans_le ha⟩ }
end

/--
When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`.
-/
lemma nth_eq_order_iso_of_nat [decidable_pred p] (i : infinite (set_of p)) (n : ℕ) :
  nth p n = nat.subtype.order_iso_of_nat (set_of p) n :=
begin
  have hi := set.infinite_coe_iff.mp i,
  induction n with k hk;
  simp only [subtype.order_iso_of_nat_apply, subtype.of_nat, nat_zero_eq_zero],
  { rw [subtype.semilattice_sup_bot_bot_apply, nth_zero_of_exists] },
  { simp only [nat.subtype.succ, set.mem_set_of_eq, subtype.coe_mk, subtype.val_eq_coe],
    rw [subtype.order_iso_of_nat_apply] at hk,
    set b := nth p k.succ - nth p k - 1 with hb,
    replace hb : p (↑(subtype.of_nat (set_of p) k) + b + 1),
    { rw [hb, ←hk, sub_right_comm'],
      have hn11: nth p k.succ - 1 + 1 = nth p k.succ,
      { rw sub_add_cancel_iff_le,
        apply succ_le_of_lt,
        apply pos_of_gt,
        apply nth_strict_mono_of_infinite p hi,
        exact lt_add_one k },
      rw add_sub_cancel_of_le,
      { rw hn11,
        apply nth_mem_of_infinite p hi },
      { rw [← lt_succ_iff, ← nat.add_one, hn11],
        apply nth_strict_mono_of_infinite p hi,
        exact lt_add_one k } },
    have H : (∃ n: ℕ , p (↑(subtype.of_nat (set_of p) k) + n + 1)) := ⟨b, hb⟩,
    set t := nat.find H with ht,
    obtain ⟨hp, hmin⟩ := (nat.find_eq_iff _).mp ht,
    rw [←ht, ←hk] at hp hmin ⊢,
    rw [nth, Inf_def ⟨_, nth_mem_of_infinite_aux p hi k.succ⟩, nat.find_eq_iff],
    refine ⟨⟨by convert hp, λ r hr, _⟩, λ n hn, _⟩,
    { rw lt_succ_iff at ⊢ hr,
      exact (nth_monotone_of_infinite p hi hr).trans (by simp) },
    simp only [exists_prop, not_and, not_lt, set.mem_set_of_eq, not_forall],
    refine λ hpn, ⟨k, lt_add_one k, _⟩,
    by_contra hlt,
    push_neg at hlt,
    replace hn : n - nth p k - 1 < t,
    { rw sub_lt_iff_left,
      { rw sub_lt_iff_left hlt.le,
        convert hn using 1,
        ac_refl },
      exact le_sub_of_add_le_left' (succ_le_of_lt hlt) },
    apply hmin,
    apply hn,
    convert hpn,
    have hn11 : n - 1 + 1 = n := nat.sub_add_cancel (pos_of_gt hlt),
    rwa [sub_right_comm', add_sub_cancel_of_le],
    rwa [←hn11, lt_succ_iff] at hlt }
end

end nat

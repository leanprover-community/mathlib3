import order.rel_iso
import data.set.finite
import order.conditionally_complete_lattice
import set_theory.fincard
import data.nat.lattice
import data.finset.intervals
import order.order_iso_nat
import data.nat.prime

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
  have := hd.union (ht.inter_of_right s),
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

lemma nat.subtype.semilattice_sup_bot_bot_apply {s : set ℕ} [decidable_pred (∈ s)] [h : nonempty s] :
((⊥ : s) : ℕ) = nat.find (nonempty_subtype.1 h) := rfl

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
lemma Inf_plus {n : ℕ} {p : ℕ → Prop} (h : 0 < Inf {m : ℕ | p m}) :
  Inf {m : ℕ | p m} + n = Inf {m : ℕ | p (m - n)} :=
begin
  symmetry,
  rw Inf_def,
  { erw nat.find_eq_iff,
    simp only [nat.add_sub_cancel, set.mem_set_of_eq],
    split,
    { apply Inf_mem (nonempty_of_pos_Inf h), },
    { intros k hk hpk,
      refine not_mem_of_lt_Inf _ hpk,
      rw sub_lt_iff_right,
      { exact hk, },
      { apply le_of_lt,
        rw [←sub_pos_iff_lt, pos_iff_ne_zero],
        intro hkn,
        rw hkn at hpk,
        exact not_mem_of_lt_Inf h hpk, }, }, },
  { obtain ⟨t, ht⟩ := nonempty_of_pos_Inf h,
    use t + n,
    simpa using ht, },
end

lemma nth_zero_of_exists [decidable_pred p] (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h, }

lemma nth_set_card_aux {n : ℕ}
  (hf : (set_of p).finite)
  (hf' : {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.finite)
  (hle : n ≤ hf.to_finset.card) :
  hf'.to_finset.card = hf.to_finset.card - n :=
begin
  tactic.unfreeze_local_instances,
  induction n with k,
  { rw nat.sub_zero,
    congr' 1,
    ext a,
    simp only [forall_false_left, nat.not_lt_zero, forall_const, and_true], },
  { change _ = hf.to_finset.card - k - 1,
    have hf'': {i : ℕ | p i ∧ ∀ (k_1 : ℕ), k_1 < k → nth p k_1 < i}.finite,
    { apply hf.subset,
      intros x hx,
      rw set.mem_set_of_eq at hx,
      exact hx.left, },
    have hle' := nat.sub_pos_of_lt hle,
    specialize n_ih hf'' (le_trans (le_succ k) hle),
    rw ←n_ih at ⊢ hle',
    convert_to finset.card (finset.erase hf''.to_finset (nth p k)) = _,
    { congr' 1,
      ext a,
      simp only [set.finite.mem_to_finset, ne.def, set.mem_set_of_eq, finset.mem_erase],
      split,
      { rintro ⟨hp, hlt⟩,
        split,
        { exact ne_of_gt (hlt _ (lt_add_one k)), },
        { refine ⟨hp, _⟩,
          intros n hn,
          apply hlt,
          apply lt_trans hn (lt_add_one k), }, },
      { rintro ⟨hak, hp, hlt⟩,
        refine ⟨hp, _⟩,
        intros n hn,
        by_cases hnk : n = k,
        { subst n,
          refine lt_of_le_of_ne _ (ne.symm hak),
          rw nth,
          apply nat.Inf_le,
          simpa [hp] using hlt, },
        { apply hlt,
          exact lt_of_le_of_ne (lt_succ_iff.mp hn) hnk, }, }, },
    apply finset.card_erase_of_mem,
    rw [nth, set.finite.mem_to_finset],
    apply Inf_mem,
    rw [←set.finite.to_finset.nonempty hf'', ←finset.card_pos],
    exact hle', },
end

lemma nth_set_card {n : ℕ} (hf : (set_of p).finite)
  (hf' : {i : ℕ | p i ∧ ∀ k < n, nth p k < i}.finite) :
  hf'.to_finset.card =  hf.to_finset.card - n :=
begin
  by_cases hle : n ≤ hf.to_finset.card,
  { exact nth_set_card_aux p hf _ hle, },
  { push_neg at hle,
    convert_to _ = 0,
    { apply nat.sub_eq_zero_of_le,
      exact le_of_lt hle },
    simp only [finset.card_eq_zero, set.finite_to_finset_eq_empty_iff, ←set.subset_empty_iff],
    convert_to _ ⊆ {i : ℕ | p i ∧ ∀ (k : ℕ), k < hf.to_finset.card → nth p k < i},
    { symmetry,
      rw [←set.finite_to_finset_eq_empty_iff, ←finset.card_eq_zero],
      rw ←nat.sub_self hf.to_finset.card,
      { apply nth_set_card_aux p hf _ (le_refl _), },
      { apply hf.subset,
        simp {contextual := tt}, }, },
    intro x,
    simp only [true_and, and_imp, set.mem_set_of_eq] { contextual := tt },
    intros hp h m hm,
    apply h,
    exact lt_trans hm hle, },
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

lemma nth_mem_of_lt_card_finite_aux (n : ℕ) (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) :
  nth p n ∈ {i : ℕ | p i ∧ ∀ k < n, nth p k < i} :=
begin
  rw nth,
  apply Inf_mem,
  apply nth_set_nonempty_of_lt_card _ _ hlt,
end

lemma nth_mem_of_lt_card_finite {n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) :
  p (nth p n) :=
begin
  have h := nth_mem_of_lt_card_finite_aux p n hf hlt,
  rw set.mem_set_of_eq at h,
  exact h.left,
end

lemma nth_mem_of_infinite_aux (i : (set_of p).infinite) (n : ℕ) :
  nth p n ∈ { i : ℕ | p i ∧ ∀ k < n, nth p k < i } :=
begin
  rw nth_def,
  apply Inf_mem,
  let s : set ℕ := ⋃ (k < n), { i : ℕ | nth p k ≥ i },
  convert_to ((set_of p) \ s).nonempty,
  { ext i,
    simp, },
  apply set.infinite.nonempty,
  apply set.infinite_of_infinite_sdiff_finite i,
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

lemma nth_strict_mono_finite {m n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) (hmn : m < n) :
  nth p m < nth p n :=
begin
  have h := nth_mem_of_lt_card_finite_aux p _ hf hlt,
  rw set.mem_set_of_eq at h,
  exact h.right _ hmn,
end

lemma nth_monotone_finite {m n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) (hmn: m ≤ n) :
  nth p m ≤ nth p n :=
begin
  apply le_of_lt_or_eq,
  by_cases m = n,
  { subst h,
    exact or.inr rfl, },
  { left,
    have := (ne.le_iff_lt h).mp hmn,
    apply nth_strict_mono_finite p hf hlt this, },
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
  rw set.mem_set_of_eq,
  refine ⟨hp, _⟩,
  intros n hn,
  refine lt_of_le_of_lt _ hak,
  refine nth_monotone_finite p hf _ (lt_succ_iff.mp hn),
  exact lt_trans (lt_add_one _) hlt,
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
    apply or_iff_not_imp_left.mpr,
    intro h,
    refine ⟨_, hp⟩,
    refine lt_of_le_of_ne _ h,
    exact le_nth_of_lt_nth_succ_finite p hf hlt ha hp, },
  { rintro (ha | ha),
    { rw ha,
      split,
      { exact nth_strict_mono_finite p hf hlt (lt_add_one _), },
      { apply nth_mem_of_lt_card_finite p hf,
        refine lt_trans _ hlt,
        exact lt_add_one k, }, },
    obtain ⟨ha, hp⟩ := ha,
    refine ⟨_, hp⟩,
    refine lt_trans ha _,
    exact nth_strict_mono_finite p hf hlt (lt_add_one _), },
end

lemma count_nth_of_lt_card_finite {n : ℕ} (hf : (set_of p).finite)
  (hlt : n < hf.to_finset.card) : count p (nth p n) = n :=
begin
  induction n with k,
  { apply count_nth_of_zero, },
  { rw count_eq_card_finset,
    rw filter_range_nth_eq_insert_of_finite p hf hlt,
    rw finset.card_insert_of_not_mem,
    { rw [←count_eq_card_finset, n_ih],
      exact lt_of_succ_lt hlt, },
    { simp, }, },
end

lemma filter_range_nth_eq_insert_of_infinite (i : (set_of p).infinite) (k : ℕ) :
  finset.filter p (finset.range (nth p k.succ)) =
    insert (nth p k) (finset.filter p (finset.range (nth p k))) :=
begin
  ext a,
  simp only [finset.mem_insert, finset.mem_filter, finset.mem_range],
  split,
  { rintro ⟨ha, hp⟩,
    apply or_iff_not_imp_left.mpr,
    intro hne,
    refine ⟨_, hp⟩,
    rw ←ne.le_iff_lt hne,
    by_contra h,
    push_neg at h,
    rw nth at ha,
    refine lt_le_antisymm ha (nat.Inf_le _),
    simp only [hp, true_and, set.mem_set_of_eq],
    intros m hm,
    refine lt_of_le_of_lt _ h,
    apply nth_monotone_of_infinite p i,
    exact lt_succ_iff.mp hm, },
  { rintro (h | h),
    { subst a,
      split,
      { exact nth_strict_mono_of_infinite p i (lt_add_one k), },
      { exact nth_mem_of_infinite p i _, }, },
    { obtain ⟨ha, hp⟩ := h,
      refine ⟨_, hp⟩,
      apply lt_trans ha,
      apply nth_strict_mono_of_infinite p i (lt_add_one k) }, },
end

lemma count_nth_of_infinite (i : (set_of p).infinite) (n : ℕ) : count p (nth p n) = n :=
begin
  induction n with k,
  { apply count_nth_of_zero, },
  { rw count_eq_card_finset,
    rw filter_range_nth_eq_insert_of_infinite p i,
    rw finset.card_insert_of_not_mem,
    { rw ←count_eq_card_finset,
      rw n_ih, },
    { simp, }, },
end

lemma count_strict_mono {m n : ℕ}
  (hm : p m) (hmn : m < n) : count p m < count p n :=
begin
  rw [count_eq_card_finset, count_eq_card_finset],
  apply finset.card_lt_card,
  split,
  { intro a,
    simp only [and_imp, and_true, finset.mem_filter, finset.mem_range] {contextual := tt},
    intros ha hp,
    exact lt_trans ha hmn, },
  { rw finset.subset_iff,
    push_neg,
    use m,
    simp [hm, hmn], },
end

lemma count_injective {m n : ℕ}
  (hm : p m) (hn : p n) (heq : count p m = count p n) : m = n :=
begin
  by_contra,
  wlog hmn : m < n,
  { exact ne.lt_or_lt h },
  { have hlt : count p m < count p n := count_strict_mono _ hm hmn,
    rw heq at hlt,
    simpa using hlt, },
end

lemma nth_count_of_infinite {n : ℕ} (i : (set_of p).infinite) (hp : p n) :
  nth p (count p n) = n :=
begin
  apply count_injective p (nth_mem_of_infinite _ i _) hp,
  exact count_nth_of_infinite p i _,
end

lemma count_lt_card {n : ℕ} (hf : (set_of p).finite) (hp : p n) :
  count p n < hf.to_finset.card :=
begin
  rw count_eq_card_finset,
  apply finset.card_lt_card,
  split,
  { intro a,
    simp {contextual := tt}, },
  { rw finset.subset_iff,
    push_neg,
    use n,
    simp [hp], },
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
  congr' 1,
  ext a,
  simp only [set.mem_set_of_eq, and.congr_right_iff],
  intro hp,
  split,
  { intro h,
    by_contra ha,
    simp only [not_le] at ha,
    have hn: nth p (count p a) < a := h _ (count_strict_mono p hp ha),
    rwa [nth_count p hp, lt_self_iff_false] at hn, },
  { intros hn k hk,
    refine lt_of_lt_of_le _ hn,
    { apply (count_monotone p).reflect_lt,
      convert hk,
      have hfi: set.finite p ∨ set.infinite p := em (set.finite p),
      cases hfi,
      { rw count_nth_of_lt_card_finite,
        refine lt_trans hk _,
        { exact hfi, },
        { apply lt_of_le_of_lt (count_monotone _ hn) (count_lt_card _ hfi hp) }, },
        { apply count_nth_of_infinite p hfi, }, }, },
end

lemma nth_count_le [decidable_pred p] (i : (set_of p).infinite) (n : ℕ) : n ≤ nth p (count p n) :=
begin
  rw nth_count_eq_Inf,
  suffices h: Inf {i : ℕ | p i ∧ n ≤ i} ∈ {i : ℕ | p i ∧ n ≤ i},
  { rw set.mem_set_of_eq at h,
    cases h with hp hle,
    exact hle, },
  apply Inf_mem,
  have hg := set.exists_gt_of_infinite,
  specialize hg p i n,
  cases hg with m hm,
  use m,
  rw set.mem_set_of_eq,
  cases hm with hp hn,
  split,
  { exact hp, },
  { apply le_of_lt hn, },
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

lemma count_le_iff_le_nth (i : (set_of p).infinite) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b :=
count_nth_gc p i _ _

lemma lt_nth_iff_count_lt (i : (set_of p).infinite) {a b : ℕ} :
  a < count p b ↔ nth p a < b :=
lt_iff_lt_of_le_iff_le $ count_le_iff_le_nth p i

lemma lt_of_count_lt {a b : ℕ} (h: count p a < count p b): a < b :=
begin
  rw count_eq_card_finset at h,
  rw count_eq_card_finset at h,
  by_contra hab,
  rw lt_iff_not_ge at h,
  apply h,
  rw ge_iff_le,
  simp at hab,
  apply finset.card_le_of_subset,
  rw finset.subset_iff,
  simp only [and_imp, finset.mem_filter, finset.mem_range],
  intros x hx hp,
  split,
  { refine lt_of_lt_of_le hx hab, },
  { exact hp, },
end

lemma nth_lt_of_lt_count (n k : ℕ) (h : k < count p n) : nth p k < n :=
begin
  obtain hfi | hinf := em (set.finite p),
  { have hio: count p (nth p k) < count p n,
    { rw count_nth_of_lt_card_finite,
      { exact h, },
      { apply lt_of_lt_of_le,
        { exact h, },
        { rw count_eq_card_finset,
          apply finset.card_le_of_subset,
          rw finset.subset_iff,
          simp only [and_imp, imp_self, set.finite.mem_to_finset,
            implies_true_iff, finset.mem_filter, set.mem_set_of_eq], }, },
      exact hfi, },
      apply lt_of_count_lt p hio, },
  { rw ← lt_nth_iff_count_lt,
    exact h,
    rw set.infinite,
    exact hinf, },
end

lemma le_nth_of_count_le (n k : ℕ) (h: n ≤ nth p k) : count p n ≤ k :=
begin
  by_contra hc,
  have hn: ¬ nth p k < n := not_lt.mpr h,
  apply hn,
  apply nth_lt_of_lt_count,
  simp only [not_le] at hc,
  exact hc,
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

lemma nth_mem_of_lt_card (n : ℕ) (w : (n : cardinal) < cardinal.mk (set_of p)) :
  p (nth p n) :=
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
  intro h0,
  apply h,
  rw nth,
  rw Inf_eq_zero,
  right,
  rw nth at h0,
  rw Inf_eq_zero at h0,
  cases h0,
  { simp only [nat.not_lt_zero, set.mem_set_of_eq] at h0,
    cases h0,
    tauto, },
  { apply set.eq_empty_of_subset_empty,
    rw ← h0,
    intro x,
    simp only [and_imp, set.mem_set_of_eq],
    intros hp hk,
    split,
    { exact hp, },
    { intros m hm,
      apply hk,
      exact lt_of_lt_of_le hm ha, }, },
end

/--
When `p` is true infinitely often, `nth` agrees with `nat.subtype.order_iso_of_nat`.
-/
lemma nth_eq_order_iso_of_nat [decidable_pred p] (i : infinite (set_of p)) (n : ℕ) :
  nth p n = nat.subtype.order_iso_of_nat (set_of p) n :=
begin
  cases n; simp [subtype.order_iso_of_nat_apply, subtype.of_nat],
  { rw [subtype.semilattice_sup_bot_bot_apply, nth_zero_of_exists] },
  sorry
end

end count

end nat

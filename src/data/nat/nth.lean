/-
Copyright (c) 2021 Vladimir Goryachev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Goryachev, Kyle Miller, Scott Morrison, Eric Rodriguez
-/
import data.nat.count
import data.set.intervals.monotone
import order.order_iso_nat

/-!
# The `n`th Number Satisfying a Predicate

This file defines a function for "what is the `n`th number that satisifies a given predicate `p`",
and provides lemmas that deal with this function and its connection to `nat.count`.

## Main definitions

* `nat.nth p n`: The `n`-th natural `k` (zero-indexed) such that `p k`. If there is no
  such natural (that is, `p` is true for at most `n` naturals), then `nat.nth p n = 0`.

## Main results

* `nat.nth_set_card`: For a fintely-often true `p`, gives the cardinality of the set of numbers
  satisfying `p` above particular values of `nth p`
* `nat.count_nth_gc`: Establishes a Galois connection between `nat.nth p` and `nat.count p`.
* `nat.nth_eq_order_iso_of_nat`: For an infinitely-ofter true predicate, `nth` agrees with the
  order-isomorphism of the subtype to the natural numbers.

There has been some discussion on the subject of whether both of `nth` and
`nat.subtype.order_iso_of_nat` should exist. See discussion
[here](https://github.com/leanprover-community/mathlib/pull/9457#pullrequestreview-767221180).
Future work should address how lemmas that use these should be written.

-/

open finset

namespace nat
variable (p : ℕ → Prop)

/-- Find the `n`-th natural number satisfying `p` (indexed from `0`, so `nth p 0` is the first
natural number satisfying `p`), or `0` if there is no such number. See also
`subtype.order_iso_of_nat` for the order isomorphism with ℕ when `p` is infinitely often true. -/
noncomputable def nth (p : ℕ → Prop) (n : ℕ) : ℕ :=
by classical; exact
  if h : set.finite (set_of p) then (h.to_finset.sort (≤)).nthd n 0
  else @nat.subtype.order_iso_of_nat (set_of p) (set.infinite.to_subtype h) n

variable {p}

/-!
### Lemmas about `nat.nth` on a finite set
-/

theorem nth_of_card_le (hf : (set_of p).finite) {n : ℕ} (hn : hf.to_finset.card ≤ n) :
  nth p n = 0 :=
by { rw [nth, dif_pos hf, list.nthd_eq_default], rwa [finset.length_sort] }

theorem nth_eq_nthd_sort (h : (set_of p).finite) (n : ℕ) :
  nth p n = (h.to_finset.sort (≤)).nthd n 0 :=
dif_pos h

theorem nth_eq_order_emb_of_fin (hf : (set_of p).finite) {n : ℕ} (hn : n < hf.to_finset.card) :
  nth p n = hf.to_finset.order_emb_of_fin rfl ⟨n, hn⟩ :=
by { rw [nth_eq_nthd_sort hf, finset.order_emb_of_fin_apply, list.nthd_eq_nth_le], refl }

theorem nth_strict_mono_on (hf : (set_of p).finite) :
  strict_mono_on (nth p) (set.Iio hf.to_finset.card) :=
begin
  rintro m (hm : m < _) n (hn : n < _) h,
  simp only [nth_eq_order_emb_of_fin, *],
  exact order_embedding.strict_mono _ h
end

theorem nth_lt_nth_of_lt_card (hf : (set_of p).finite) {m n : ℕ} (h : m < n)
  (hn : n < hf.to_finset.card) : nth p m < nth p n :=
nth_strict_mono_on hf (h.trans hn) hn h

theorem nth_le_nth_of_lt_card (hf : (set_of p).finite) {m n : ℕ} (h : m ≤ n)
  (hn : n < hf.to_finset.card) : nth p m ≤ nth p n :=
(nth_strict_mono_on hf).monotone_on (h.trans_lt hn) hn h

theorem lt_of_nth_lt_nth_of_lt_card (hf : (set_of p).finite) {m n : ℕ} (h : nth p m < nth p n)
  (hm : m < hf.to_finset.card) : m < n :=
not_le.1 $ λ hle, h.not_le $ nth_le_nth_of_lt_card hf hle hm

theorem le_of_nth_le_nth_of_lt_card (hf : (set_of p).finite) {m n : ℕ} (h : nth p m ≤ nth p n)
  (hm : m < hf.to_finset.card) : m ≤ n :=
not_lt.1 $ λ hlt, h.not_lt $ nth_lt_nth_of_lt_card hf hlt hm

theorem nth_inj_on (hf : (set_of p).finite) : (set.Iio hf.to_finset.card).inj_on (nth p) :=
(nth_strict_mono_on hf).inj_on

theorem range_nth_of_finite (hf : (set_of p).finite) : set.range (nth p) = insert 0 (set_of p) :=
by simpa only [← nth_eq_nthd_sort hf, mem_sort, set.finite.mem_to_finset]
  using set.range_list_nthd (hf.to_finset.sort (≤)) 0

@[simp] theorem image_nth_Iio_card (hf : (set_of p).finite) :
  nth p '' set.Iio hf.to_finset.card = set_of p :=
calc nth p '' set.Iio hf.to_finset.card = set.range (hf.to_finset.order_emb_of_fin rfl) :
  by ext x; simp only [set.mem_image, set.mem_range, fin.exists_iff,
    ← nth_eq_order_emb_of_fin hf, set.mem_Iio, exists_prop]
... = set_of p : by rw [range_order_emb_of_fin, set.finite.coe_to_finset]

lemma nth_mem_of_lt_card {n : ℕ} (hf : (set_of p).finite) (hlt : n < hf.to_finset.card) :
  p (nth p n) :=
(image_nth_Iio_card hf).subset $ set.mem_image_of_mem _ hlt

theorem exists_lt_card_finite_nth_eq (hf : (set_of p).finite) {x} (h : p x) :
  ∃ n, n < hf.to_finset.card ∧ nth p n = x :=
by rwa [← @set.mem_set_of_eq _ _ p, ← image_nth_Iio_card hf] at h

/-!
### Lemmas about `nat.nth` on an infinite set
-/

/-- When `s` is an infinite set, `nth` agrees with `nat.subtype.order_iso_of_nat`. -/
theorem nth_apply_eq_order_iso_of_nat (hf : (set_of p).infinite) (n : ℕ) :
  nth p n = @nat.subtype.order_iso_of_nat (set_of p) hf.to_subtype n :=
by rw [nth, dif_neg hf]

/-- When `s` is an infinite set, `nth` agrees with `nat.subtype.order_iso_of_nat`. -/
theorem nth_eq_order_iso_of_nat (hf : (set_of p).infinite) :
  nth p = coe ∘ @nat.subtype.order_iso_of_nat (set_of p) hf.to_subtype :=
funext $ nth_apply_eq_order_iso_of_nat hf

lemma nth_strict_mono (hf : (set_of p).infinite) : strict_mono (nth p) :=
begin
  rw [nth_eq_order_iso_of_nat hf],
  exact (subtype.strict_mono_coe _).comp (order_iso.strict_mono _)
end

lemma nth_injective (hf : (set_of p).infinite) : function.injective (nth p) :=
(nth_strict_mono hf).injective

lemma nth_monotone (hf : (set_of p).infinite) : monotone (nth p) :=
(nth_strict_mono hf).monotone

lemma nth_lt_nth (hf : (set_of p).infinite) {k n} : nth p k < nth p n ↔ k < n :=
(nth_strict_mono hf).lt_iff_lt

lemma nth_le_nth (hf : (set_of p).infinite) {k n} : nth p k ≤ nth p n ↔ k ≤ n :=
(nth_strict_mono hf).le_iff_le

lemma range_nth_of_infinite (hf : (set_of p).infinite) : set.range (nth p) = set_of p :=
begin
  rw [nth_eq_order_iso_of_nat hf],
  haveI := hf.to_subtype,
  exact nat.subtype.coe_comp_of_nat_range
end

theorem nth_mem_of_infinite (hf : (set_of p).infinite) (n : ℕ) : p (nth p n) :=
set.range_subset_iff.1 (range_nth_of_infinite hf).le n

/-!
### Lemmas that work for finite and infinite sets
-/

theorem exists_lt_card_nth_eq {x} (h : p x) :
  ∃ n, (∀ hf : (set_of p).finite, n < hf.to_finset.card) ∧ nth p n = x :=
begin
  refine (set_of p).finite_or_infinite.elim (λ hf, _) (λ hf, _),
  { rcases exists_lt_card_finite_nth_eq hf h with ⟨n, hn, hx⟩,
    exact ⟨n, λ hf', hn, hx⟩ },
  { rw [← @set.mem_set_of_eq _ _ p, ← range_nth_of_infinite hf] at h,
    rcases h with ⟨n, hx⟩,
    exact ⟨n, λ hf', absurd hf' hf, hx⟩ }
end

theorem subset_range_nth : set_of p ⊆ set.range (nth p) :=
λ x (hx : p x), let ⟨n, _, hn⟩ := exists_lt_card_nth_eq hx in ⟨n, hn⟩

theorem range_nth_subset : set.range (nth p) ⊆ insert 0 (set_of p) :=
(set_of p).finite_or_infinite.elim (λ h, (range_nth_of_finite h).subset)
  (λ h, (range_nth_of_infinite h).trans_subset (set.subset_insert _ _))

theorem nth_mem (n : ℕ) (h : ∀ hf : (set_of p).finite, n < hf.to_finset.card) : p (nth p n) :=
(set_of p).finite_or_infinite.elim (λ hf, nth_mem_of_lt_card hf (h hf))
  (λ h, nth_mem_of_infinite h n)

theorem nth_lt_nth' {m n : ℕ} (hlt : m < n) (h : ∀ hf : (set_of p).finite, n < hf.to_finset.card) :
  nth p m < nth p n :=
(set_of p).finite_or_infinite.elim (λ hf, nth_lt_nth_of_lt_card hf hlt (h _))
  (λ hf, (nth_lt_nth hf).2 hlt)

theorem nth_le_nth' {m n : ℕ} (hle : m ≤ n) (h : ∀ hf : (set_of p).finite, n < hf.to_finset.card) :
  nth p m ≤ nth p n :=
(set_of p).finite_or_infinite.elim (λ hf, nth_le_nth_of_lt_card hf hle (h _))
  (λ hf, (nth_le_nth hf).2 hle)

theorem le_nth {n : ℕ} (h : ∀ hf : (set_of p).finite, n < hf.to_finset.card) : n ≤ nth p n :=
(set_of p).finite_or_infinite.elim
  (λ hf, ((nth_strict_mono_on hf).mono $ set.Iic_subset_Iio.2 (h _)).Iic_id_le _ le_rfl)
  (λ hf, (nth_strict_mono hf).id_le _)

theorem is_least_nth {n} (h : ∀ hf : (set_of p).finite, n < hf.to_finset.card) :
  is_least { i | p i ∧ ∀ k < n, nth p k < i } (nth p n) :=
⟨⟨nth_mem n h, λ k hk, nth_lt_nth' hk h⟩, λ x hx, let ⟨k, hk, hkx⟩ := exists_lt_card_nth_eq hx.1
  in (lt_or_le k n).elim (λ hlt, absurd hkx (hx.2 _ hlt).ne) (λ hle, hkx ▸ nth_le_nth' hle hk)⟩

theorem is_least_nth_of_lt_card {n : ℕ} (hf : (set_of p).finite) (hn : n < hf.to_finset.card) :
  is_least { i | p i ∧ ∀ k < n, nth p k < i } (nth p n) :=
is_least_nth $ λ _, hn

theorem is_least_nth_of_infinite (hf : (set_of p).infinite) (n : ℕ) :
  is_least { i | p i ∧ ∀ k < n, nth p k < i } (nth p n) :=
is_least_nth $ λ h, absurd h hf

/-- An alternative recursive definition of `nat.nth`: `nat.nth s n` is the infimum of `x ∈ s` such
that `nat.nth s k < x` for all `k < n`, if this set is nonempty. We do not assume that the set is
nonempty because we use the same "garbage value" `0` both for `Inf` on `ℕ` and for `nat.nth s n` for
`n ≥ card s`. -/
lemma nth_eq_Inf (p : ℕ → Prop) (n : ℕ) : nth p n = Inf {x | p x ∧ ∀ k < n, nth p k < x} :=
begin
  by_cases hn : ∀ hf : (set_of p).finite, n < hf.to_finset.card,
  { exact (is_least_nth hn).cInf_eq.symm },
  { push_neg at hn,
    rcases hn with ⟨hf, hn⟩,
    rw [nth_of_card_le _ hn],
    refine ((congr_arg Inf $ set.eq_empty_of_forall_not_mem $ λ k hk, _).trans Inf_empty).symm,
    rcases exists_lt_card_nth_eq hk.1 with ⟨k, hlt, rfl⟩,
    exact (hk.2 _ ((hlt hf).trans_le hn)).false }
end

lemma nth_zero : nth p 0 = Inf (set_of p) := by { rw nth_eq_Inf, simp }

@[simp] lemma nth_zero_of_zero (h : p 0) : nth p 0 = 0 := by simp [nth_zero, h]

lemma nth_zero_of_exists [decidable_pred p] (h : ∃ n, p n) : nth p 0 = nat.find h :=
by { rw [nth_zero], convert nat.Inf_def h }

lemma nth_eq_zero {n} :
  nth p n = 0 ↔ p 0 ∧ n = 0 ∨ ∃ hf : (set_of p).finite, hf.to_finset.card ≤ n :=
begin
  refine ⟨λ h, _, _⟩,
  { simp only [or_iff_not_imp_right, not_exists, not_le],
    exact λ hn, ⟨h ▸ nth_mem _ hn, nonpos_iff_eq_zero.1 $ h ▸ le_nth hn⟩ },
  { rintro (⟨h₀, rfl⟩ | ⟨hf, hle⟩),
    exacts [nth_zero_of_zero h₀, nth_of_card_le hf hle] }
end

lemma nth_eq_zero_mono (h₀ : ¬p 0) {a b : ℕ} (hab : a ≤ b) (ha : nth p a = 0) :
  nth p b = 0 :=
begin
  simp only [nth_eq_zero, h₀, false_and, false_or] at ha ⊢,
  exact ha.imp (λ hf hle, hle.trans hab)
end

lemma le_nth_of_lt_nth_succ {k a : ℕ} (h : a < nth p (k + 1)) (ha : p a) :
  a ≤ nth p k :=
begin
  cases (set_of p).finite_or_infinite with hf hf,
  { rcases exists_lt_card_finite_nth_eq hf ha with ⟨n, hn, rfl⟩,
    cases lt_or_le (k + 1) hf.to_finset.card with hk hk,
    { rwa [(nth_strict_mono_on hf).lt_iff_lt hn hk, lt_succ_iff,
        ← (nth_strict_mono_on hf).le_iff_le hn (k.lt_succ_self.trans hk)] at h },
    { rw [nth_of_card_le _ hk] at h,
      exact absurd h (zero_le _).not_lt } },
  { rcases subset_range_nth ha with ⟨n, rfl⟩,
    rwa [nth_lt_nth hf, lt_succ_iff, ← nth_le_nth hf] at h }
end

section count
variables (p) [decidable_pred p]

@[simp] lemma count_nth_zero : count p (nth p 0) = 0 :=
begin
  rw [count_eq_card_filter_range, card_eq_zero, filter_eq_empty_iff, nth_zero],
  exact λ n h₁ h₂, (mem_range.1 h₁).not_le (nat.Inf_le h₂)
end

lemma filter_range_nth_subset_insert (k : ℕ) :
  (range (nth p (k + 1))).filter p ⊆ insert (nth p k) ((range (nth p k)).filter p) :=
begin
  intros a ha,
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢,
  exact (le_nth_of_lt_nth_succ ha.1 ha.2).eq_or_lt.imp_right (λ h, ⟨h, ha.2⟩)
end

variable {p}

lemma filter_range_nth_eq_insert {k : ℕ}
  (hlt : ∀ hf : (set_of p).finite, k + 1 < hf.to_finset.card) :
  (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) :=
begin
  refine (filter_range_nth_subset_insert p k).antisymm (λ a ha, _),
  simp only [mem_insert, mem_filter, mem_range] at ha ⊢,
  have : nth p k < nth p (k + 1) := nth_lt_nth' k.lt_succ_self hlt,
  rcases ha with (rfl | ⟨hlt, hpa⟩),
  { exact ⟨this, nth_mem _ (λ hf, k.lt_succ_self.trans (hlt hf))⟩ },
  { exact ⟨hlt.trans this, hpa⟩ },
end

lemma filter_range_nth_eq_insert_of_finite (hf : (set_of p).finite) {k : ℕ}
  (hlt : k + 1 < hf.to_finset.card) :
  (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) :=
filter_range_nth_eq_insert $ λ _, hlt

lemma filter_range_nth_eq_insert_of_infinite (hp : (set_of p).infinite) (k : ℕ) :
  (range (nth p (k + 1))).filter p = insert (nth p k) ((range (nth p k)).filter p) :=
filter_range_nth_eq_insert $ λ hf, absurd hf hp

lemma count_nth {n : ℕ} (hn : ∀ hf : (set_of p).finite, n < hf.to_finset.card) :
  count p (nth p n) = n :=
begin
  induction n with k ihk,
  { exact count_nth_zero _ },
  { rw [count_eq_card_filter_range, filter_range_nth_eq_insert hn, card_insert_of_not_mem,
      ←count_eq_card_filter_range, ihk (λ hf, lt_of_succ_lt (hn hf))],
    simp }
end

lemma count_nth_of_lt_card_finite {n : ℕ} (hp : (set_of p).finite)
  (hlt : n < hp.to_finset.card) : count p (nth p n) = n :=
count_nth $ λ _, hlt

lemma count_nth_of_infinite (hp : (set_of p).infinite) (n : ℕ) : count p (nth p n) = n :=
count_nth $ λ hf, absurd hf hp

lemma count_nth_succ {n : ℕ} (hn : ∀ hf : (set_of p).finite, n < hf.to_finset.card) :
  count p (nth p n + 1) = n + 1 :=
by rw [count_succ, count_nth hn, if_pos (nth_mem _ hn)]

@[simp] lemma nth_count {n : ℕ} (hpn : p n) : nth p (count p n) = n :=
have ∀ hf : (set_of p).finite, count p n < hf.to_finset.card,
  from λ hf, count_lt_card hf hpn,
count_injective (nth_mem _ this) hpn (count_nth this)

lemma nth_lt_of_lt_count {n k : ℕ} (h : k < count p n) : nth p k < n :=
begin
  refine (count_monotone p).reflect_lt _,
  rwa [count_nth],
  exact λ hf, h.trans_le (count_le_card hf n)
end

lemma le_nth_of_count_le {n k : ℕ} (h : n ≤ nth p k) : count p n ≤ k :=
not_lt.1 $ λ hlt, h.not_lt $ nth_lt_of_lt_count hlt

variable (p)

lemma nth_count_eq_Inf (n : ℕ) : nth p (count p n) = Inf {i : ℕ | p i ∧ n ≤ i} :=
begin
  refine (nth_eq_Inf _ _).trans (congr_arg Inf _),
  refine set.ext (λ a, and_congr_right $ λ hpa, _),
  refine ⟨λ h, not_lt.1 (λ ha, _), λ hn k hk, lt_of_lt_of_le (nth_lt_of_lt_count hk) hn⟩,
  have hn : nth p (count p a) < a := h _ (count_strict_mono hpa ha),
  rwa [nth_count hpa, lt_self_iff_false] at hn
end

variable {p}

lemma le_nth_count' {n : ℕ} (hpn : ∃ k, p k ∧ n ≤ k) : n ≤ nth p (count p n) :=
(le_cInf hpn $ λ k, and.right).trans (nth_count_eq_Inf p n).ge

lemma le_nth_count (hp : (set_of p).infinite) (n : ℕ) : n ≤ nth p (count p n) :=
let ⟨m, hp, hn⟩ := hp.exists_nat_lt n in le_nth_count' ⟨m, hp, hn.le⟩

/-- If a predicate `p : ℕ → Prop` is true for infinitely many numbers, then `nat.count p` and
`nat.nth p` form a Galois insertion. -/
noncomputable def gi_count_nth (hp : (set_of p).infinite) : galois_insertion (count p) (nth p) :=
galois_insertion.monotone_intro (nth_monotone hp) (count_monotone p)
  (le_nth_count hp) (count_nth_of_infinite hp)

lemma gc_count_nth (hp : (set_of p).infinite) : galois_connection (count p) (nth p) :=
(gi_count_nth hp).gc

lemma count_le_iff_le_nth (hp : (set_of p).infinite) {a b : ℕ} :
  count p a ≤ b ↔ a ≤ nth p b := gc_count_nth hp _ _

lemma lt_nth_iff_count_lt (hp : (set_of p).infinite) {a b : ℕ} :
  a < count p b ↔ nth p a < b := (gc_count_nth hp).lt_iff_lt

end count

end nat

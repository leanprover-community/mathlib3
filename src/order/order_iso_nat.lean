/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.nat.lattice
import logic.denumerable
import logic.function.iterate
import order.hom.basic
import tactic.congrm

/-!
# Relation embeddings from the naturals

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows translation from monotone functions `ℕ → α` to order embeddings `ℕ ↪ α` and
defines the limit value of an eventually-constant sequence.

## Main declarations

* `nat_lt`/`nat_gt`: Make an order embedding `ℕ ↪ α` from an increasing/decreasing function `ℕ → α`.
* `monotonic_sequence_limit`: The limit of an eventually-constant monotone sequence `ℕ →o α`.
* `monotonic_sequence_limit_index`: The index of the first occurence of `monotonic_sequence_limit`
  in the sequence.
-/

variable {α : Type*}

namespace rel_embedding

variables {r : α → α → Prop} [is_strict_order α r]

/-- If `f` is a strictly `r`-increasing sequence, then this returns `f` as an order embedding. -/
def nat_lt (f : ℕ → α) (H : ∀ n : ℕ, r (f n) (f (n + 1))) : ((<) : ℕ → ℕ → Prop) ↪r r :=
of_monotone f $ nat.rel_of_forall_rel_succ_of_lt r H

@[simp] lemma coe_nat_lt {f : ℕ → α} {H : ∀ n : ℕ, r (f n) (f (n + 1))} : ⇑(nat_lt f H) = f := rfl

/-- If `f` is a strictly `r`-decreasing sequence, then this returns `f` as an order embedding. -/
def nat_gt (f : ℕ → α) (H : ∀ n : ℕ, r (f (n + 1)) (f n)) : ((>) : ℕ → ℕ → Prop) ↪r r :=
by { haveI := is_strict_order.swap r, exact rel_embedding.swap (nat_lt f H) }

@[simp] lemma coe_nat_gt {f : ℕ → α} {H : ∀ n : ℕ, r (f (n + 1)) (f n)} : ⇑(nat_gt f H) = f := rfl

theorem exists_not_acc_lt_of_not_acc {a : α} {r} (h : ¬ acc r a) : ∃ b, ¬ acc r b ∧ r b a :=
begin
  contrapose! h,
  refine ⟨_, λ b hr, _⟩,
  by_contra hb,
  exact h b hb hr
end

/-- A value is accessible iff it isn't contained in any infinite decreasing sequence. -/
theorem acc_iff_no_decreasing_seq {x} :
  acc r x ↔ is_empty {f : ((>) : ℕ → ℕ → Prop) ↪r r // x ∈ set.range f} :=
begin
  split,
  { refine λ h, h.rec_on (λ x h IH, _),
    split,
    rintro ⟨f, k, hf⟩,
    exact is_empty.elim' (IH (f (k + 1)) (hf ▸ f.map_rel_iff.2 (lt_add_one k))) ⟨f, _, rfl⟩ },
  { have : ∀ x : {a // ¬ acc r a}, ∃ y : {a // ¬ acc r a}, r y.1 x.1,
    { rintro ⟨x, hx⟩,
      cases exists_not_acc_lt_of_not_acc hx,
      exact ⟨⟨w, h.1⟩, h.2⟩ },
    obtain ⟨f, h⟩ := classical.axiom_of_choice this,
    refine λ E, classical.by_contradiction (λ hx, E.elim'
      ⟨(nat_gt (λ n, (f^[n] ⟨x, hx⟩).1) (λ n, _)), 0, rfl⟩),
    rw function.iterate_succ',
    apply h }
end

theorem not_acc_of_decreasing_seq (f : ((>) : ℕ → ℕ → Prop) ↪r r) (k : ℕ) : ¬ acc r (f k) :=
by { rw [acc_iff_no_decreasing_seq, not_is_empty_iff], exact ⟨⟨f, k, rfl⟩⟩ }

/-- A relation is well-founded iff it doesn't have any infinite decreasing sequence. -/
theorem well_founded_iff_no_descending_seq :
  well_founded r ↔ is_empty (((>) : ℕ → ℕ → Prop) ↪r r) :=
begin
  split,
  { rintro ⟨h⟩,
    exact ⟨λ f, not_acc_of_decreasing_seq f 0 (h _)⟩ },
  { introI h,
    exact ⟨λ x, acc_iff_no_decreasing_seq.2 infer_instance⟩ }
end

theorem not_well_founded_of_decreasing_seq (f : ((>) : ℕ → ℕ → Prop) ↪r r) : ¬ well_founded r :=
by { rw [well_founded_iff_no_descending_seq, not_is_empty_iff], exact ⟨f⟩ }

end rel_embedding

namespace nat
variables (s : set ℕ) [infinite s]

/-- An order embedding from `ℕ` to itself with a specified range -/
def order_embedding_of_set [decidable_pred (∈ s)] : ℕ ↪o ℕ :=
(rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _))).trans
  (order_embedding.subtype s)

/-- `nat.subtype.of_nat` as an order isomorphism between `ℕ` and an infinite subset. See also
`nat.nth` for a version where the subset may be finite. -/
noncomputable def subtype.order_iso_of_nat : ℕ ≃o s :=
by { classical, exact rel_iso.of_surjective (rel_embedding.order_embedding_of_lt_embedding
  (rel_embedding.nat_lt (nat.subtype.of_nat s) (λ n, nat.subtype.lt_succ_self _)))
  nat.subtype.of_nat_surjective }

variable {s}

@[simp]
lemma coe_order_embedding_of_set [decidable_pred (∈ s)] :
  ⇑(order_embedding_of_set s) = coe ∘ subtype.of_nat s := rfl

lemma order_embedding_of_set_apply [decidable_pred (∈ s)] {n : ℕ} :
  order_embedding_of_set s n = subtype.of_nat s n := rfl

@[simp]
lemma subtype.order_iso_of_nat_apply [decidable_pred (∈ s)] {n : ℕ} :
  subtype.order_iso_of_nat s n = subtype.of_nat s n :=
by { simp [subtype.order_iso_of_nat], congr }

variable (s)

lemma order_embedding_of_set_range [decidable_pred (∈ s)] :
  set.range (nat.order_embedding_of_set s) = s :=
subtype.coe_comp_of_nat_range

theorem exists_subseq_of_forall_mem_union {s t : set α} (e : ℕ → α) (he : ∀ n, e n ∈ s ∪ t) :
  ∃ g : ℕ ↪o ℕ, (∀ n, e (g n) ∈ s) ∨ (∀ n, e (g n) ∈ t) :=
begin
  classical,
  have : infinite (e ⁻¹' s) ∨ infinite (e ⁻¹' t),
    by simp only [set.infinite_coe_iff, ← set.infinite_union, ← set.preimage_union,
      set.eq_univ_of_forall (λ n, set.mem_preimage.2 (he n)), set.infinite_univ],
  casesI this,
  exacts [⟨nat.order_embedding_of_set (e ⁻¹' s), or.inl $ λ n, (nat.subtype.of_nat (e ⁻¹' s) _).2⟩,
    ⟨nat.order_embedding_of_set (e ⁻¹' t), or.inr $ λ n, (nat.subtype.of_nat (e ⁻¹' t) _).2⟩]
end

end nat

theorem exists_increasing_or_nonincreasing_subseq' (r : α → α → Prop) (f : ℕ → α) :
  ∃ (g : ℕ ↪o ℕ), (∀ n : ℕ, r (f (g n)) (f (g (n + 1)))) ∨
    (∀ m n : ℕ, m < n → ¬ r (f (g m)) (f (g n))) :=
begin
  classical,
  let bad : set ℕ := { m | ∀ n, m < n → ¬ r (f m) (f n) },
  by_cases hbad : infinite bad,
  { haveI := hbad,
    refine ⟨nat.order_embedding_of_set bad, or.intro_right _ (λ m n mn, _)⟩,
    have h := set.mem_range_self m,
    rw nat.order_embedding_of_set_range bad at h,
    exact h _ ((order_embedding.lt_iff_lt _).2 mn) },
  { rw [set.infinite_coe_iff, set.infinite, not_not] at hbad,
    obtain ⟨m, hm⟩ : ∃ m, ∀ n, m ≤ n → ¬ n ∈ bad,
    { by_cases he : hbad.to_finset.nonempty,
      { refine ⟨(hbad.to_finset.max' he).succ, λ n hn nbad, nat.not_succ_le_self _
        (hn.trans (hbad.to_finset.le_max' n (hbad.mem_to_finset.2 nbad)))⟩ },
      { exact ⟨0, λ n hn nbad, he ⟨n, hbad.mem_to_finset.2 nbad⟩⟩ } },
    have h : ∀ (n : ℕ), ∃ (n' : ℕ), n < n' ∧ r (f (n + m)) (f (n' + m)),
    { intro n,
      have h := hm _ (le_add_of_nonneg_left n.zero_le),
      simp only [exists_prop, not_not, set.mem_set_of_eq, not_forall] at h,
      obtain ⟨n', hn1, hn2⟩ := h,
      obtain ⟨x, hpos, rfl⟩ := exists_pos_add_of_lt hn1,
      refine ⟨n + x, add_lt_add_left hpos n, _⟩,
      rw [add_assoc, add_comm x m, ← add_assoc],
      exact hn2 },
    let g' : ℕ → ℕ := @nat.rec (λ _, ℕ) m (λ n gn, nat.find (h gn)),
    exact ⟨(rel_embedding.nat_lt (λ n, g' n + m)
      (λ n, nat.add_lt_add_right (nat.find_spec (h (g' n))).1 m)).order_embedding_of_lt_embedding,
      or.intro_left _ (λ n, (nat.find_spec (h (g' n))).2)⟩ }
end

/-- This is the infinitary Erdős–Szekeres theorem, and an important lemma in the usual proof of
    Bolzano-Weierstrass for `ℝ`. -/
theorem exists_increasing_or_nonincreasing_subseq (r : α → α → Prop) [is_trans α r] (f : ℕ → α) :
  ∃ (g : ℕ ↪o ℕ), (∀ m n : ℕ, m < n → r (f (g m)) (f (g n))) ∨
    (∀ m n : ℕ, m < n → ¬ r (f (g m)) (f (g n))) :=
begin
  obtain ⟨g, hr | hnr⟩ := exists_increasing_or_nonincreasing_subseq' r f,
  { refine ⟨g, or.intro_left _ (λ m n mn, _)⟩,
    obtain ⟨x, rfl⟩ := exists_add_of_le (nat.succ_le_iff.2 mn),
    induction x with x ih,
    { apply hr },
    { apply is_trans.trans _ _ _ _ (hr _),
      exact ih (lt_of_lt_of_le m.lt_succ_self (nat.le_add_right _ _)) } },
  { exact ⟨g, or.intro_right _ hnr⟩ }
end

lemma well_founded.monotone_chain_condition' [preorder α] :
  well_founded ((>) : α → α → Prop) ↔ ∀ (a : ℕ →o α), ∃ n, ∀ m, n ≤ m → ¬ a n < a m :=
begin
  refine ⟨λ h a, _, λ h, _⟩,
  { have hne : (set.range a).nonempty := ⟨a 0, by simp⟩,
    obtain ⟨x, ⟨n, rfl⟩, H⟩ := h.has_min _ hne,
    exact ⟨n, λ m hm, H _ (set.mem_range_self _)⟩ },
  { refine rel_embedding.well_founded_iff_no_descending_seq.2 ⟨λ a, _⟩,
    obtain ⟨n, hn⟩ := h (a.swap : ((<) : ℕ → ℕ → Prop) →r ((<) : α → α → Prop)).to_order_hom,
    exact hn n.succ n.lt_succ_self.le ((rel_embedding.map_rel_iff _).2 n.lt_succ_self) },
end

/-- The "monotone chain condition" below is sometimes a convenient form of well foundedness. -/
lemma well_founded.monotone_chain_condition [partial_order α] :
  well_founded ((>) : α → α → Prop) ↔ ∀ (a : ℕ →o α), ∃ n, ∀ m, n ≤ m → a n = a m :=
well_founded.monotone_chain_condition'.trans $ begin
  congrm ∀ a, ∃ n, ∀ m (h : n ≤ m), (_ : Prop),
  rw lt_iff_le_and_ne,
  simp [a.mono h]
end

/-- Given an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a partially-ordered
type, `monotonic_sequence_limit_index a` is the least natural number `n` for which `aₙ` reaches the
constant value. For sequences that are not eventually constant, `monotonic_sequence_limit_index a`
is defined, but is a junk value. -/
noncomputable def monotonic_sequence_limit_index [preorder α] (a : ℕ →o α) : ℕ :=
Inf {n | ∀ m, n ≤ m → a n = a m}

/-- The constant value of an eventually-constant monotone sequence `a₀ ≤ a₁ ≤ a₂ ≤ ...` in a
partially-ordered type. -/
noncomputable def monotonic_sequence_limit [preorder α] (a : ℕ →o α) :=
a (monotonic_sequence_limit_index a)

lemma well_founded.supr_eq_monotonic_sequence_limit [complete_lattice α]
  (h : well_founded ((>) : α → α → Prop)) (a : ℕ →o α) : supr a = monotonic_sequence_limit a :=
begin
  suffices : (⨆ (m : ℕ), a m) ≤ monotonic_sequence_limit a,
  { exact le_antisymm this (le_supr a _), },
  apply supr_le,
  intros m,
  by_cases hm : m ≤ monotonic_sequence_limit_index a,
  { exact a.monotone hm, },
  { replace hm := le_of_not_le hm,
    let S := { n | ∀ m, n ≤ m → a n = a m },
    have hInf : Inf S ∈ S,
    { refine nat.Inf_mem _, rw well_founded.monotone_chain_condition at h, exact h a, },
    change Inf S ≤ m at hm,
    change a m ≤ a (Inf S),
    rw hInf m hm, },
end

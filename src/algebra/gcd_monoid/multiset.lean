/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.gcd_monoid.basic
import data.multiset.finset_ops
import data.multiset.fold

/-!
# GCD and LCM operations on multisets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Main definitions

- `multiset.gcd` - the greatest common denominator of a `multiset` of elements of a `gcd_monoid`
- `multiset.lcm` - the least common multiple of a `multiset` of elements of a `gcd_monoid`

## Implementation notes

TODO: simplify with a tactic and `data.multiset.lattice`

## Tags

multiset, gcd
-/

namespace multiset
variables {α : Type*} [cancel_comm_monoid_with_zero α] [normalized_gcd_monoid α]

/-! ### lcm -/
section lcm

/-- Least common multiple of a multiset -/
def lcm (s : multiset α) : α := s.fold gcd_monoid.lcm 1

@[simp] lemma lcm_zero : (0 : multiset α).lcm = 1 :=
fold_zero _ _

@[simp] lemma lcm_cons (a : α) (s : multiset α) :
  (a ::ₘ s).lcm = gcd_monoid.lcm a s.lcm :=
fold_cons_left _ _ _ _

@[simp] lemma lcm_singleton {a : α} : ({a} : multiset α).lcm = normalize a :=
(fold_singleton _ _ _).trans $ lcm_one_right _

@[simp] lemma lcm_add (s₁ s₂ : multiset α) : (s₁ + s₂).lcm = gcd_monoid.lcm s₁.lcm s₂.lcm :=
eq.trans (by simp [lcm]) (fold_add _ _ _ _ _)

lemma lcm_dvd {s : multiset α} {a : α} : s.lcm ∣ a ↔ (∀ b ∈ s, b ∣ a) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib, lcm_dvd_iff] {contextual := tt})

lemma dvd_lcm {s : multiset α} {a : α} (h : a ∈ s) : a ∣ s.lcm :=
lcm_dvd.1 dvd_rfl _ h

lemma lcm_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
lcm_dvd.2 $ assume b hb, dvd_lcm (h hb)

@[simp] lemma normalize_lcm (s : multiset α) : normalize (s.lcm) = s.lcm :=
multiset.induction_on s (by simp) $ λ a s IH, by simp

@[simp] theorem lcm_eq_zero_iff [nontrivial α] (s : multiset α) : s.lcm = 0 ↔ (0 : α) ∈ s :=
begin
  induction s using multiset.induction_on with a s ihs,
  { simp only [lcm_zero, one_ne_zero, not_mem_zero] },
  { simp only [mem_cons, lcm_cons, lcm_eq_zero_iff, ihs, @eq_comm _ a] },
end

variables [decidable_eq α]

@[simp] lemma lcm_dedup (s : multiset α) : (dedup s).lcm = s.lcm :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  unfold lcm,
  rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same],
  apply lcm_eq_of_associated_left (associated_normalize _),
end

@[simp] lemma lcm_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).lcm = gcd_monoid.lcm s₁.lcm s₂.lcm :=
by { rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add], simp }

@[simp] lemma lcm_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).lcm = gcd_monoid.lcm s₁.lcm s₂.lcm :=
by { rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_add], simp }

@[simp] lemma lcm_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).lcm = gcd_monoid.lcm a s.lcm :=
by { rw [← lcm_dedup, dedup_ext.2, lcm_dedup, lcm_cons], simp }

end lcm

/-! ### gcd -/
section gcd

/-- Greatest common divisor of a multiset -/
def gcd (s : multiset α) : α := s.fold gcd_monoid.gcd 0

@[simp] lemma gcd_zero : (0 : multiset α).gcd = 0 :=
fold_zero _ _

@[simp] lemma gcd_cons (a : α) (s : multiset α) :
  (a ::ₘ s).gcd = gcd_monoid.gcd a s.gcd :=
fold_cons_left _ _ _ _

@[simp] lemma gcd_singleton {a : α} : ({a} : multiset α).gcd = normalize a :=
(fold_singleton _ _ _).trans $ gcd_zero_right _

@[simp] lemma gcd_add (s₁ s₂ : multiset α) : (s₁ + s₂).gcd = gcd_monoid.gcd s₁.gcd s₂.gcd :=
eq.trans (by simp [gcd]) (fold_add _ _ _ _ _)

lemma dvd_gcd {s : multiset α} {a : α} : a ∣ s.gcd ↔ (∀ b ∈ s, a ∣ b) :=
multiset.induction_on s (by simp)
  (by simp [or_imp_distrib, forall_and_distrib, dvd_gcd_iff] {contextual := tt})

lemma gcd_dvd {s : multiset α} {a : α} (h : a ∈ s) : s.gcd ∣ a :=
dvd_gcd.1 dvd_rfl _ h

lemma gcd_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₂.gcd ∣ s₁.gcd :=
dvd_gcd.2 $ assume b hb, gcd_dvd (h hb)

@[simp] lemma normalize_gcd (s : multiset α) : normalize (s.gcd) = s.gcd :=
multiset.induction_on s (by simp) $ λ a s IH, by simp

theorem gcd_eq_zero_iff (s : multiset α) : s.gcd = 0 ↔ ∀ (x : α), x ∈ s → x = 0 :=
begin
  split,
  { intros h x hx,
    apply eq_zero_of_zero_dvd,
    rw ← h,
    apply gcd_dvd hx },
  { apply s.induction_on,
    { simp },
    intros a s sgcd h,
    simp [h a (mem_cons_self a s), sgcd (λ x hx, h x (mem_cons_of_mem hx))] }
end

lemma gcd_map_mul (a : α) (s : multiset α) :
  (s.map ((*) a)).gcd = normalize a * s.gcd :=
begin
  refine s.induction_on _ (λ b s ih, _),
  { simp_rw [map_zero, gcd_zero, mul_zero] },
  { simp_rw [map_cons, gcd_cons, ← gcd_mul_left], rw ih,
    apply ((normalize_associated a).mul_right _).gcd_eq_right },
end

section

variables [decidable_eq α]

@[simp] lemma gcd_dedup (s : multiset α) : (dedup s).gcd = s.gcd :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  unfold gcd,
  rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same],
  apply (associated_normalize _).gcd_eq_left,
end

@[simp] lemma gcd_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).gcd = gcd_monoid.gcd s₁.gcd s₂.gcd :=
by { rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add], simp }

@[simp] lemma gcd_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).gcd = gcd_monoid.gcd s₁.gcd s₂.gcd :=
by { rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_add], simp }

@[simp] lemma gcd_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).gcd = gcd_monoid.gcd a s.gcd :=
by { rw [← gcd_dedup, dedup_ext.2, gcd_dedup, gcd_cons], simp }

end

lemma extract_gcd' (s t : multiset α) (hs : ∃ x, x ∈ s ∧ x ≠ (0 : α))
  (ht : s = t.map ((*) s.gcd)) : t.gcd = 1 :=
((@mul_right_eq_self₀ _ _ s.gcd _).1 $ by conv_lhs { rw [← normalize_gcd, ← gcd_map_mul, ← ht] })
  .resolve_right $ by { contrapose! hs, exact s.gcd_eq_zero_iff.1 hs }

lemma extract_gcd (s : multiset α) (hs : s ≠ 0) :
  ∃ t : multiset α, s = t.map ((*) s.gcd) ∧ t.gcd = 1 :=
begin
  classical,
  by_cases h : ∀ x ∈ s, x = (0 : α),
  { use replicate s.card 1,
    rw [map_replicate, eq_replicate, mul_one, s.gcd_eq_zero_iff.2 h, ←nsmul_singleton, ←gcd_dedup],
    rw [dedup_nsmul (card_pos.2 hs).ne', dedup_singleton, gcd_singleton],
    exact ⟨⟨rfl, h⟩, normalize_one⟩ },
  { choose f hf using @gcd_dvd _ _ _ s,
    have := _, push_neg at h,
    refine ⟨s.pmap @f (λ _, id), this, extract_gcd' s _ h this⟩,
    rw map_pmap, conv_lhs { rw [← s.map_id, ← s.pmap_eq_map _ _ (λ _, id)] },
    congr' with x hx, rw [id, ← hf hx] },
end

end gcd

end multiset

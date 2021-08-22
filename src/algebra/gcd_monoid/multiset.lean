/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import algebra.gcd_monoid.basic
import data.multiset.lattice

/-!
# GCD and LCM operations on multisets

## Main definitions

- `multiset.gcd` - the greatest common denominator of a `multiset` of elements of a `gcd_monoid`
- `multiset.lcm` - the least common multiple of a `multiset` of elements of a `gcd_monoid`

## Implementation notes

TODO: simplify with a tactic and `data.multiset.lattice`

## Tags

multiset, gcd
-/

namespace multiset
variables {α : Type*} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]

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
lcm_dvd.1 (dvd_refl _) _ h

lemma lcm_mono {s₁ s₂ : multiset α} (h : s₁ ⊆ s₂) : s₁.lcm ∣ s₂.lcm :=
lcm_dvd.2 $ assume b hb, dvd_lcm (h hb)

@[simp] lemma normalize_lcm (s : multiset α) : normalize (s.lcm) = s.lcm :=
multiset.induction_on s (by simp) $ λ a s IH, by simp

variables [decidable_eq α]

@[simp] lemma lcm_erase_dup (s : multiset α) : (erase_dup s).lcm = s.lcm :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  unfold lcm,
  rw [← cons_erase h, fold_cons_left, ← lcm_assoc, lcm_same],
  apply lcm_eq_of_associated_left (associated_normalize _),
end

@[simp] lemma lcm_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).lcm = gcd_monoid.lcm s₁.lcm s₂.lcm :=
by { rw [← lcm_erase_dup, erase_dup_ext.2, lcm_erase_dup, lcm_add], simp }

@[simp] lemma lcm_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).lcm = gcd_monoid.lcm s₁.lcm s₂.lcm :=
by { rw [← lcm_erase_dup, erase_dup_ext.2, lcm_erase_dup, lcm_add], simp }

@[simp] lemma lcm_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).lcm = gcd_monoid.lcm a s.lcm :=
by { rw [← lcm_erase_dup, erase_dup_ext.2, lcm_erase_dup, lcm_cons], simp }

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
dvd_gcd.1 (dvd_refl _) _ h

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

variables [decidable_eq α]

@[simp] lemma gcd_erase_dup (s : multiset α) : (erase_dup s).gcd = s.gcd :=
multiset.induction_on s (by simp) $ λ a s IH, begin
  by_cases a ∈ s; simp [IH, h],
  unfold gcd,
  rw [← cons_erase h, fold_cons_left, ← gcd_assoc, gcd_same],
  apply (associated_normalize _).gcd_eq_left,
end

@[simp] lemma gcd_ndunion (s₁ s₂ : multiset α) :
  (ndunion s₁ s₂).gcd = gcd_monoid.gcd s₁.gcd s₂.gcd :=
by { rw [← gcd_erase_dup, erase_dup_ext.2, gcd_erase_dup, gcd_add], simp }

@[simp] lemma gcd_union (s₁ s₂ : multiset α) :
  (s₁ ∪ s₂).gcd = gcd_monoid.gcd s₁.gcd s₂.gcd :=
by { rw [← gcd_erase_dup, erase_dup_ext.2, gcd_erase_dup, gcd_add], simp }

@[simp] lemma gcd_ndinsert (a : α) (s : multiset α) :
  (ndinsert a s).gcd = gcd_monoid.gcd a s.gcd :=
by { rw [← gcd_erase_dup, erase_dup_ext.2, gcd_erase_dup, gcd_cons], simp }

end gcd

end multiset

/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Aaron Anderson
-/
import data.finset.fold
import data.multiset.gcd

/-!
# GCD and LCM operations on finsets

## Main definitions

- `finset.gcd` - the greatest common denominator of a `finset` of elements of a `gcd_monoid`
- `finset.lcm` - the least common multiple of a `finset` of elements of a `gcd_monoid`

## Implementation notes

Many of the proofs use the lemmas `gcd.def` and `lcm.def`, which relate `finset.gcd`
and `finset.lcm` to `multiset.gcd` and `multiset.lcm`.

TODO: simplify with a tactic and `data.finset.lattice`

## Tags

finset, gcd
-/

variables {α β γ : Type*} [comm_cancel_monoid_with_zero α] [nontrivial α] [gcd_monoid α]

namespace finset
open multiset

/-! ### lcm -/
section lcm

/-- Least common multiple of a finite set -/
def lcm (s : finset β) (f : β → α) : α := s.fold gcd_monoid.lcm 1 f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma lcm_def : s.lcm f = (s.1.map f).lcm := rfl

@[simp] lemma lcm_empty : (∅ : finset β).lcm f = 1 :=
fold_empty

@[simp] lemma lcm_dvd_iff {a : α} : s.lcm f ∣ a ↔ (∀b ∈ s, f b ∣ a) :=
begin
  apply iff.trans multiset.lcm_dvd,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

lemma lcm_dvd {a : α} : (∀b ∈ s, f b ∣ a) → s.lcm f ∣ a :=
lcm_dvd_iff.2

lemma dvd_lcm {b : β} (hb : b ∈ s) : f b ∣ s.lcm f :=
lcm_dvd_iff.1 (dvd_refl _) _ hb

@[simp] lemma lcm_insert [decidable_eq β] {b : β} :
  (insert b s : finset β).lcm f = gcd_monoid.lcm (f b) (s.lcm f) :=
begin
  by_cases h : b ∈ s,
  { rw [insert_eq_of_mem h,
        (lcm_eq_right_iff (f b) (s.lcm f) (multiset.normalize_lcm (s.1.map f))).2 (dvd_lcm h)] },
  apply fold_insert h,
end

@[simp] lemma lcm_singleton {b : β} : ({b} : finset β).lcm f = normalize (f b) :=
multiset.lcm_singleton

@[simp] lemma normalize_lcm : normalize (s.lcm f) = s.lcm f := by simp [lcm_def]

lemma lcm_union [decidable_eq β] : (s₁ ∪ s₂).lcm f = gcd_monoid.lcm (s₁.lcm f) (s₂.lcm f) :=
finset.induction_on s₁ (by rw [empty_union, lcm_empty, lcm_one_left, normalize_lcm]) $ λ a s has ih,
  by rw [insert_union, lcm_insert, lcm_insert, ih, lcm_assoc]

theorem lcm_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a ∈ s₂, f a = g a) :
  s₁.lcm f = s₂.lcm g :=
by { subst hs, exact finset.fold_congr hfg }

lemma lcm_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.lcm f ∣ s.lcm g :=
lcm_dvd (λ b hb, dvd_trans (h b hb) (dvd_lcm hb))

lemma lcm_mono (h : s₁ ⊆ s₂) : s₁.lcm f ∣ s₂.lcm f :=
lcm_dvd $ assume b hb, dvd_lcm (h hb)

end lcm

/-! ### gcd -/
section gcd

/-- Greatest common divisor of a finite set -/
def gcd (s : finset β) (f : β → α) : α := s.fold gcd_monoid.gcd 0 f

variables {s s₁ s₂ : finset β} {f : β → α}

lemma gcd_def : s.gcd f = (s.1.map f).gcd := rfl

@[simp] lemma gcd_empty : (∅ : finset β).gcd f = 0 :=
fold_empty

lemma dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ ∀b ∈ s, a ∣ f b :=
begin
  apply iff.trans multiset.dvd_gcd,
  simp only [multiset.mem_map, and_imp, exists_imp_distrib],
  exact ⟨λ k b hb, k _ _ hb rfl, λ k a' b hb h, h ▸ k _ hb⟩,
end

lemma gcd_dvd {b : β} (hb : b ∈ s) : s.gcd f ∣ f b :=
dvd_gcd_iff.1 (dvd_refl _) _ hb

lemma dvd_gcd {a : α} : (∀b ∈ s, a ∣ f b) → a ∣ s.gcd f :=
dvd_gcd_iff.2

@[simp] lemma gcd_insert [decidable_eq β] {b : β} :
  (insert b s : finset β).gcd f = gcd_monoid.gcd (f b) (s.gcd f) :=
begin
  by_cases h : b ∈ s,
  { rw [insert_eq_of_mem h,
    (gcd_eq_right_iff (f b) (s.gcd f) (multiset.normalize_gcd (s.1.map f))).2 (gcd_dvd h)] ,},
  apply fold_insert h,
end

@[simp] lemma gcd_singleton {b : β} : ({b} : finset β).gcd f = normalize (f b) :=
multiset.gcd_singleton

@[simp] lemma normalize_gcd : normalize (s.gcd f) = s.gcd f := by simp [gcd_def]

lemma gcd_union [decidable_eq β] : (s₁ ∪ s₂).gcd f = gcd_monoid.gcd (s₁.gcd f) (s₂.gcd f) :=
finset.induction_on s₁ (by rw [empty_union, gcd_empty, gcd_zero_left, normalize_gcd]) $ λ a s has ih,
  by rw [insert_union, gcd_insert, gcd_insert, ih, gcd_assoc]

theorem gcd_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀a ∈ s₂, f a = g a) :
  s₁.gcd f = s₂.gcd g :=
by { subst hs, exact finset.fold_congr hfg }

lemma gcd_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ∣ g b) : s.gcd f ∣ s.gcd g :=
dvd_gcd (λ b hb, dvd_trans (gcd_dvd hb) (h b hb))

lemma gcd_mono (h : s₁ ⊆ s₂) : s₂.gcd f ∣ s₁.gcd f :=
dvd_gcd $ assume b hb, gcd_dvd (h hb)

end gcd
end finset

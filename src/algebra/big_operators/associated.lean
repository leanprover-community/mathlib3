/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/

import algebra.associated
import algebra.big_operators.basic

/-!
# Products of associated, prime, and irreducible elements.

This file contains some theorems relating definitions in `algebra.associated`
and products of multisets and finsets.

-/

variables {α β γ δ : Type*}

-- the same local notation used in `algebra.associated`
local infix ` ~ᵤ ` : 50 := associated
open_locale big_operators

namespace prime

variables [comm_monoid_with_zero α] {p : α} (hp : prime p)

lemma exists_mem_multiset_dvd {s : multiset α} :
  p ∣ s.prod → ∃ a ∈ s, p ∣ a :=
multiset.induction_on s (λ h, (hp.not_dvd_one h).elim) $
λ a s ih h,
  have p ∣ a * s.prod, by simpa using h,
  match hp.dvd_or_dvd this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

include hp

lemma exists_mem_multiset_map_dvd {s : multiset β} {f : β → α} :
  p ∣ (s.map f).prod → ∃ a ∈ s, p ∣ f a :=
λ h, by simpa only [exists_prop, multiset.mem_map, exists_exists_and_eq_and]
  using hp.exists_mem_multiset_dvd h

lemma exists_mem_finset_dvd {s : finset β} {f : β → α} :
  p ∣ s.prod f → ∃ i ∈ s, p ∣ f i :=
hp.exists_mem_multiset_map_dvd

end prime

lemma exists_associated_mem_of_dvd_prod [cancel_comm_monoid_with_zero α] {p : α}
  (hp : prime p) {s : multiset α} : (∀ r ∈ s, prime r) → p ∣ s.prod → ∃ q ∈ s, p ~ᵤ q :=
multiset.induction_on s (by simp [mt is_unit_iff_dvd_one.2 hp.not_unit])
  (λ a s ih hs hps, begin
    rw [multiset.prod_cons] at hps,
    cases hp.dvd_or_dvd hps with h h,
    { use [a, by simp],
      cases h with u hu,
      cases (((hs a (multiset.mem_cons.2 (or.inl rfl))).irreducible)
        .is_unit_or_is_unit hu).resolve_left hp.not_unit with v hv,
      exact ⟨v, by simp [hu, hv]⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

namespace associates

section comm_monoid

variables [comm_monoid α]

theorem prod_mk {p : multiset α} : (p.map associates.mk).prod = associates.mk p.prod :=
multiset.induction_on p (by simp; refl) $ assume a s ih, by simp [ih]; refl

theorem rel_associated_iff_map_eq_map {p q : multiset α} :
  multiset.rel associated p q ↔ p.map associates.mk = q.map associates.mk :=
by { rw [← multiset.rel_eq, multiset.rel_map], simp only [mk_eq_mk_iff_associated] }

theorem prod_eq_one_iff {p : multiset (associates α)} :
  p.prod = 1 ↔ (∀a ∈ p, (a:associates α) = 1) :=
multiset.induction_on p
  (by simp)
  (by simp [mul_eq_one_iff, or_imp_distrib, forall_and_distrib] {contextual := tt})

theorem prod_le_prod {p q : multiset (associates α)} (h : p ≤ q) : p.prod ≤ q.prod :=
begin
  haveI := classical.dec_eq (associates α),
  haveI := classical.dec_eq α,
  suffices : p.prod ≤ (p + (q - p)).prod, { rwa [add_tsub_cancel_of_le h] at this },
  suffices : p.prod * 1 ≤ p.prod * (q - p).prod, { simpa },
  exact mul_mono (le_refl p.prod) one_le
end

end comm_monoid

section cancel_comm_monoid_with_zero

variables [cancel_comm_monoid_with_zero α]

lemma exists_mem_multiset_le_of_prime {s : multiset (associates α)} {p : associates α}
  (hp : prime p) :
  p ≤ s.prod → ∃a∈s, p ≤ a :=
multiset.induction_on s (assume ⟨d, eq⟩, (hp.ne_one (mul_eq_one_iff.1 eq.symm).1).elim) $
assume a s ih h,
  have p ≤ a * s.prod, by simpa using h,
  match prime.le_or_le hp this with
  | or.inl h := ⟨a, multiset.mem_cons_self a s, h⟩
  | or.inr h := let ⟨a, has, h⟩ := ih h in ⟨a, multiset.mem_cons_of_mem has, h⟩
  end

end cancel_comm_monoid_with_zero

end associates

namespace multiset

lemma prod_ne_zero_of_prime [cancel_comm_monoid_with_zero α] [nontrivial α]
 (s : multiset α) (h : ∀ x ∈ s, prime x) : s.prod ≠ 0 :=
multiset.prod_ne_zero (λ h0, prime.ne_zero (h 0 h0) rfl)

end multiset

/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
lemma prime.dvd_prod_iff {M : Type*} [comm_monoid_with_zero M] {p : M} {L : list M} (pp : prime p) :
p ∣ L.prod ↔ ∃ a ∈ L, p ∣ a :=
begin
  split,
  { intros h,
    induction L,
    { simp only [list.prod_nil] at h, exact absurd h (prime.not_dvd_one pp) },
    { rw list.prod_cons at h,
      cases (prime.dvd_or_dvd pp) h, { use L_hd, simp [h_1] },
      { rcases L_ih h_1 with ⟨x, hx1, hx2⟩, use x, simp [list.mem_cons_iff, hx1, hx2] } } },
  { exact λ ⟨a, ha1, ha2⟩, dvd_trans ha2 (list.dvd_prod ha1) },
end

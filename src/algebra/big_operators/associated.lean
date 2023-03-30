/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/

import algebra.associated
import algebra.big_operators.finsupp

/-!
# Products of associated, prime, and irreducible elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some theorems relating definitions in `algebra.associated`
and products of multisets, finsets, and finsupps.

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
    { have hap := hs a (multiset.mem_cons.2 (or.inl rfl)),
      exact ⟨a, multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩ },
    { rcases ih (λ r hr, hs _ (multiset.mem_cons.2 (or.inr hr))) h with ⟨q, hq₁, hq₂⟩,
      exact ⟨q, multiset.mem_cons.2 (or.inr hq₁), hq₂⟩ }
  end)

lemma multiset.prod_primes_dvd
  [cancel_comm_monoid_with_zero α] [Π a : α, decidable_pred (associated a)]
  {s : multiset α} (n : α) (h : ∀ a ∈ s, prime a) (div : ∀ a ∈ s, a ∣ n)
  (uniq : ∀ a, s.countp (associated a) ≤ 1) :
  s.prod ∣ n :=
begin
  induction s using multiset.induction_on with a s induct n primes divs generalizing n,
  { simp only [multiset.prod_zero, one_dvd] },
  { rw multiset.prod_cons,
    obtain ⟨k, rfl⟩ : a ∣ n := div a (multiset.mem_cons_self a s),
    apply mul_dvd_mul_left a,
    refine induct
      (λ a ha, h a (multiset.mem_cons_of_mem ha))
      (λ a, (multiset.countp_le_of_le _ (multiset.le_cons_self _ _)).trans (uniq a))
      k (λ b b_in_s, _),
    { have b_div_n := div b (multiset.mem_cons_of_mem b_in_s),
      have a_prime := h a (multiset.mem_cons_self a s),
      have b_prime := h b (multiset.mem_cons_of_mem b_in_s),
      refine (b_prime.dvd_or_dvd b_div_n).resolve_left (λ b_div_a, _),
      have assoc := b_prime.associated_of_dvd a_prime b_div_a,
      have := uniq a,
      rw [multiset.countp_cons_of_pos _ (associated.refl _), nat.succ_le_succ_iff, ←not_lt,
        multiset.countp_pos] at this,
      exact this ⟨b, b_in_s, assoc.symm⟩ } }
end

lemma finset.prod_primes_dvd
  [cancel_comm_monoid_with_zero α] [unique αˣ]
  {s : finset α} (n : α) (h : ∀ a ∈ s, prime a) (div : ∀ a ∈ s, a ∣ n) :
  (∏ p in s, p) ∣ n :=
begin
  classical,
  exact multiset.prod_primes_dvd n
    (by simpa only [multiset.map_id', finset.mem_def] using h)
    (by simpa only [multiset.map_id', finset.mem_def] using div)
    (by simp only [multiset.map_id', associated_eq_eq, multiset.countp_eq_card_filter,
        ←multiset.count_eq_card_filter_eq, ←multiset.nodup_iff_count_le_one, s.nodup]),
end

namespace associates

section comm_monoid

variables [comm_monoid α]

theorem prod_mk {p : multiset α} : (p.map associates.mk).prod = associates.mk p.prod :=
multiset.induction_on p (by simp) $ λ a s ih, by simp [ih, associates.mk_mul_mk]

theorem finset_prod_mk {p : finset β} {f : β → α} :
  ∏ i in p, associates.mk (f i) = associates.mk (∏ i in p, f i) :=
by rw [finset.prod_eq_multiset_prod, ← multiset.map_map, prod_mk, ← finset.prod_eq_multiset_prod]

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

open finset finsupp

section comm_monoid_with_zero

variables {M : Type*} [comm_monoid_with_zero M]

lemma prime.dvd_finset_prod_iff {S : finset α} {p : M} (pp : prime p) (g : α → M) :
  p ∣ S.prod g ↔ ∃ a ∈ S, p ∣ g a :=
⟨pp.exists_mem_finset_dvd, λ ⟨a, ha1, ha2⟩, dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩

lemma prime.dvd_finsupp_prod_iff  {f: α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : prime p) :
  p ∣ f.prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
prime.dvd_finset_prod_iff pp _

end comm_monoid_with_zero

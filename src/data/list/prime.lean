/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/

import algebra.associated
import data.list.big_operators
import data.list.perm

/-!
# Products of lists of prime elements.

This file contains some theorems relating `prime` and products of `list`s.

-/

open list

section comm_monoid_with_zero

variables {M : Type*} [comm_monoid_with_zero M]

/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
lemma prime.dvd_prod_iff {p : M} {L : list M} (pp : prime p) :
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

lemma prime.not_dvd_prod {p : M} {L : list M} (pp : prime p) (hL : ∀ a ∈ L, ¬ p ∣ a) :
  ¬ p ∣ L.prod :=
mt (prime.dvd_prod_iff pp).mp (not_bex.mpr hL)

end comm_monoid_with_zero

section cancel_comm_monoid_with_zero

variables {M : Type*} [cancel_comm_monoid_with_zero M] [unique (units M)]

lemma prime_dvd_prime_iff_eq
  {p q : M} (pp : prime p) (qp : prime q) : p ∣ q ↔ p = q :=
by rw [pp.dvd_prime_iff_associated qp, ←associated_eq_eq]

lemma mem_list_primes_of_dvd_prod {p : M} (hp : prime p) :
  ∀ {l : list M}, (∀ p ∈ l, prime p) → p ∣ l.prod → p ∈ l :=
begin
  intros L hL hpL,
  rcases hp.dvd_prod_iff.mp hpL with ⟨x, hx1, hx2⟩,
  rwa (prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2
end

lemma perm_of_prod_eq_prod : ∀ {l₁ l₂ : list M}, l₁.prod = l₂.prod →
  (∀ p ∈ l₁, prime p) → (∀ p ∈ l₂, prime p) → list.perm l₁ l₂
| []        []        _  _  _  := perm.nil
| []        (a :: l)  h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil M _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
| (a :: l)  []        h₁ h₂ h₃ :=
  have ha : a ∣ 1 := @prod_nil M _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _,
  absurd ha (prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
| (a :: l₁) (b :: l₂) h hl₁ hl₂ :=
  begin
    classical,
    have hl₁' : ∀ p ∈ l₁, prime p := λ p hp, hl₁ p (mem_cons_of_mem _ hp),
    have hl₂' : ∀ p ∈ (b :: l₂).erase a, prime p := λ p hp, hl₂ p (mem_of_mem_erase hp),
    have ha : a ∈ (b :: l₂) := mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
      (h ▸ by rw prod_cons; exact dvd_mul_right _ _),
    have hb : b :: l₂ ~ a :: (b :: l₂).erase a := perm_cons_erase ha,
    have hl : prod l₁ = prod ((b :: l₂).erase a) :=
      ((mul_right_inj' (hl₁ a (mem_cons_self _ _)).ne_zero).1 $
        by rwa [← prod_cons, ← prod_cons, ← hb.prod_eq]),
    exact perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm
  end

end cancel_comm_monoid_with_zero

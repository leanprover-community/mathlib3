/-
Copyright (c) 2021 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/

import algebra.squarefree
import ring_theory.unique_factorization_domain

/-!

# Chains of divisors

The results in this file show that in the monoid `associates M` of a unique_factorization_monoid
`M`, an element `a` is an n-th prime power iff its set of divisors is a strictly increasing chain
of length `n + 1`, aka we can find strictly increasing bijection bewteen `fin (n + 1)` and
the set of factors of `a`

We can then use this to show that given `a b : M`, if there is an monotone bijection
between the sets of factors of `associates.mk a` and `associates.mk b` then the prime
factorisations of `a` and `b` have the same shape.


## Main results
- `prime_pow_has_chain` : existence of chain for prime powers
- `eq_prime_pow_of_has_chain` : elements that have a chain are prime powers
- `multiplicity_le_of_monotone` : if there is a monotone bijection `d` between the set
  of factors of `a : associates M` and the set of factors of `b : associates N` then
  for any prime `p ∣ a`, `multiplicity p a ≤ multiplicity (d p) b`.

## Todo
- show that under the assumptions of `multiplicity_le_of_monotone`, `d p` is prime. Applying
  `multiplicity_le_of_monotone` on `d.symm` then gives us `multiplicity p a = multiplicity (d p) b`

-/


section factorisations_same_shape

noncomputable theory
open_locale classical

open unique_factorization_monoid multiplicity irreducible

variables {M : Type*} [cancel_comm_monoid_with_zero M]

lemma pow_prime_has_chain {p : associates M} (n : ℕ) (hn : n ≠ 0) (hp : prime p) :
  ∃ c : fin (n + 1) → associates M,
    c 1 = p ∧ strict_mono c ∧
    ∀ {r : associates M}, r ≤ p^n ↔ ∃ i, r = c i :=
begin
  refine ⟨λ i, p^(i : ℕ), _, λ n m h, _, λ y, ⟨λ h, _, _⟩⟩,
  { rw [fin.coe_one', nat.mod_eq_of_lt, pow_one],
    exact nat.lt_succ_of_le (nat.one_le_iff_ne_zero.mpr hn) },
  { exact associates.dvd_not_unit_iff_lt.mp ⟨pow_ne_zero n hp.ne_zero, p^(m - n : ℕ),
      not_is_unit_of_not_is_unit_dvd hp.not_unit (dvd_pow (dvd_refl _) (nat.sub_pos_of_lt h).ne'),
      (pow_mul_pow_sub p h.le).symm⟩ },
  { obtain ⟨i, i_le, hi⟩ := (dvd_prime_pow hp n).1 h,
    rw associated_iff_eq at hi,
    exact ⟨⟨i, nat.lt_succ_of_le i_le⟩, hi⟩ },
  { rintro ⟨i, rfl⟩,
    exact ⟨p^(n - i : ℕ), (pow_mul_pow_sub p (nat.succ_le_succ_iff.mp i.2)).symm⟩ }
end

lemma second_of_chain_not_is_unit (n : ℕ) (i : fin (n + 1)) (i_pos : i ≠ 0)
  (c : fin (n + 1) → associates M) (h₁ : strict_mono c) :
  ¬ is_unit (c i) :=
dvd_not_unit.not_unit (associates.dvd_not_unit_iff_lt.2
  (h₁ $ show (0 : fin (n + 1)) < i, from i.pos_iff_ne_zero.mpr i_pos))

lemma first_of_chain_is_unit {q : associates M} (n : ℕ) (c : fin (n + 1) → associates M)
  (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i, r = c i):
  is_unit (c 0) :=
begin
  obtain ⟨i, hr⟩ := h₂.mp associates.one_le,
  rw [associates.is_unit_iff_eq_one, ← associates.le_one_iff, hr],
  exact h₁.monotone (fin.zero_le i)
end

lemma second_of_chain_is_irreducible {q : associates M} (n : ℕ) (hn : n ≠ 0)
  (c : fin (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i)
  (hq : q ≠ 0) : irreducible (c 1) :=
begin
  cases n, { contradiction },
  refine (associates.is_atom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, rfl⟩))).mp ⟨_, λ b hb, _⟩,
  { exact ne_bot_of_gt (h₁ (show (0 : fin (n + 2)) < 1, from fin.one_pos)) },
  obtain ⟨⟨i, hi⟩, rfl⟩ := h₂.1 (hb.le.trans (h₂.2 ⟨1, rfl⟩)),
  cases i,
  { exact (associates.is_unit_iff_eq_one _).mp (first_of_chain_is_unit _ c h₁ @h₂) },
  { simpa [fin.lt_iff_coe_lt_coe] using h₁.lt_iff_lt.mp hb },
end

lemma prime_dvd_eq_second_of_chain {p q r : associates M} (n : ℕ) (hn : n ≠ 0)
  (c : fin (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i, r = c i)
  (hp : prime p) (hr : r ∣ q) (hp' : p ∣ r) :
  p = c 1 :=
begin
  obtain ⟨i, rfl⟩ := h₂.1 (dvd_trans hp' hr),
  suffices h : i = 1,
  { subst h },
  refine le_antisymm _ _, swap,
  { cases n, { contradiction },
    rw [fin.le_iff_coe_le_coe, fin.coe_one, nat.succ_le_iff, ← fin.coe_zero,
        ← fin.lt_iff_coe_lt_coe, fin.pos_iff_ne_zero],
    rintro rfl,
    exact prime.not_unit hp (first_of_chain_is_unit _ c h₁ @h₂) },
  { refine le_of_not_lt (λ hi, _),
    have hp' := hp.irreducible,
    contrapose hp',
    obtain (rfl | ⟨j, rfl⟩) := i.eq_zero_or_eq_succ,
    { cases hi },
    refine (not_irreducible_of_not_unit_dvd_not_unit
      (dvd_not_unit.not_unit (associates.dvd_not_unit_iff_lt.2
      (h₁ (show (0 : fin (n + 1)) < j, from _)) )) _),
    { cases n, { contradiction },
      simpa [← fin.succ_zero_eq_one, fin.succ_lt_succ_iff] using hi },
    rw associates.dvd_not_unit_iff_lt,
    apply h₁,
    simpa using fin.lt_succ },
end

lemma card_subset_divisors_le_length_of_chain {q : associates M} (n : ℕ)
  (c : fin (n + 1) → associates M)
  (h₂ : ∀ (r : associates M), r ≤ q ↔ ∃ i, r = c i)
  (m : finset (associates M)) (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 :=
begin
  have mem_image : ∀ (r : associates M), r ≤ q → r ∈ finset.univ.image c,
  { intros r hr,
    rw finset.mem_image,
    obtain ⟨i, hi⟩ := (h₂ r).1 hr,
    exact ⟨i, finset.mem_univ _, hi.symm⟩ },
  have subset_image : m ⊆ finset.univ.image c := λ x hx, (mem_image x) (hm x hx),
  rw ← finset.card_fin (n + 1),
  exact (finset.card_le_of_subset subset_image).trans (finset.card_image_le),
end

lemma multiplicity.finite_prime_left [wf_dvd_monoid M] {a b : M} (ha : prime a) (hb : b ≠ 0) :
  multiplicity.finite a b :=
begin
  revert hb,
  refine wf_dvd_monoid.induction_on_irreducible b _ _ _,
  { contradiction },
  { intros u hu hu',
    rw [multiplicity.finite_iff_dom, multiplicity.is_unit_right ha.not_unit hu],
    exact enat.dom_coe 0 },
  { intros b p hb hp ih hpb,
    refine multiplicity.finite_mul ha
      (multiplicity.finite_iff_dom.mpr (enat.dom_of_le_coe (show multiplicity a p ≤ ↑1, from _)))
      (ih hb),
    norm_cast,
    exact (((multiplicity.squarefree_iff_multiplicity_le_one p).mp hp.squarefree a)
      .resolve_right ha.not_unit) }
end

lemma multiplicity_eq_multiplicity_associates_mk [wf_dvd_monoid M] {p q : M} (hp : prime p)
  (hq : q ≠ 0) : multiplicity p q = multiplicity (associates.mk p) (associates.mk q) :=
begin
  have finite₁ := multiplicity.finite_prime_left hp hq,
  have finite₂ := multiplicity.finite_prime_left ((associates.prime_mk p).2 hp)
    (associates.mk_ne_zero.2 hq),
  apply le_antisymm,
  suffices : ↑((multiplicity p q).get finite₁) ≤ multiplicity (associates.mk p) (associates.mk q),
  { rw enat.coe_le_iff at this,
    exact enat.get_le_get.1 (this finite₂) },
  apply multiplicity.le_multiplicity_of_pow_dvd,
  rw [← associates.mk_pow, associates.mk_dvd_mk],
  exact multiplicity.pow_multiplicity_dvd finite₁,

  suffices : ↑((multiplicity (associates.mk p) (associates.mk q)).get finite₂) ≤ multiplicity p q,
  { rw enat.coe_le_iff at this,
    exact enat.get_le_get.1 (this finite₁) },
  apply multiplicity.le_multiplicity_of_pow_dvd,
  rw [← associates.mk_dvd_mk, associates.mk_pow],
  exact multiplicity.pow_multiplicity_dvd finite₂,
end

variable [unique_factorization_monoid M]

lemma mem_chain_eq_pow_second_of_chain {q r : associates M} (n : ℕ) (hn : n ≠ 0)
  (c : fin (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r}, r ≤ q ↔ ∃ i, r = c i) (hr : r ∣ q)
  (hq : q ≠ 0) : ∃ (i : fin (n + 1)), r = (c 1) ^ (i : ℕ) :=
begin
  let i := (normalized_factors r).card,
  have hi : normalized_factors r = multiset.repeat (c 1) i,
  { apply multiset.eq_repeat_of_mem,
    intros b hb,
    refine prime_dvd_eq_second_of_chain n hn c h₁ (λ r', h₂) (prime_of_normalized_factor b hb) hr
      (dvd_of_mem_normalized_factors hb) },
  have H : r = (c 1)^i,
  { have := unique_factorization_monoid.normalized_factors_prod (ne_zero_of_dvd_ne_zero hq hr),
    rw [associated_iff_eq, hi, multiset.prod_repeat] at this,
    rw this },

  refine ⟨⟨i, _⟩, H⟩,
  have : (finset.univ.image (λ (m : fin (i + 1)), (c 1) ^ (m : ℕ))).card = i + 1,
  { conv_rhs { rw [← finset.card_fin (i+1)] },
    cases n, { contradiction },
    rw finset.card_image_eq_iff_inj_on,
    refine set.inj_on_of_injective (λ m m' h, fin.ext _) _,
    refine pow_injective_of_not_unit (second_of_chain_not_is_unit (n+1) 1 dec_trivial c h₁) _ h,
    exact irreducible.ne_zero (second_of_chain_is_irreducible _ hn c h₁ (λ r, h₂) hq) },

  suffices H' : ∀ r ∈ (finset.univ.image (λ (m : fin (i + 1)), (c 1) ^ (m : ℕ))), r ≤ q,
  { simp only [← nat.succ_le_iff, nat.succ_eq_add_one, ← this],
    apply card_subset_divisors_le_length_of_chain n c (λ r', h₂) (finset.univ.image
        (λ (m : fin (i + 1)), (c 1) ^ (m : ℕ))) H' },

  simp only [finset.mem_image],
  rintros r ⟨a, ha, rfl⟩,
  refine dvd_trans _ hr,
  use (c 1)^(i - a),
  rw pow_mul_pow_sub (c 1),
  { exact H },
  { exact nat.succ_le_succ_iff.mp a.2 }
end

lemma eq_prime_pow_of_has_chain {q : associates M} (n : ℕ) (hn : n ≠ 0)
  (c : fin (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i, r = c i)
  (hq : q ≠ 0) : q = (c 1)^n :=
begin
  obtain ⟨i, hi'⟩ := mem_chain_eq_pow_second_of_chain n hn c h₁ (λ r, h₂) (dvd_refl q) hq,
  suffices : n ≤ i,
  { rwa le_antisymm (nat.succ_le_succ_iff.mp i.prop) this at hi' },

  refine nat.le_of_succ_le_succ _,
  calc n + 1 = (finset.univ : finset (fin (n + 1))).card : (finset.card_fin _).symm
         ... = (finset.univ.image c).card :
    (finset.card_image_eq_iff_inj_on.mpr (h₁.injective.inj_on _)).symm
         ... ≤ (finset.univ.image (λ (m : fin (i + 1)), (c 1)^(m : ℕ))).card :
          finset.card_le_of_subset _
         ... ≤ (finset.univ : finset (fin (i + 1))).card : finset.card_image_le
         ... = i + 1 : finset.card_fin _,
  intros r hr,
  obtain ⟨j, -, rfl⟩ := finset.mem_image.1 hr,
  have := h₂.2 ⟨j, rfl⟩,
  rw hi' at this,
  obtain ⟨u, hu, hu'⟩ := (dvd_prime_pow (show prime (c 1), from _) i).1 this,
  refine finset.mem_image.mpr ⟨u, finset.mem_univ _, _⟩,
  { rw associated_iff_eq at hu', rw [fin.coe_coe_of_lt (nat.lt_succ_of_le hu), hu'] },
  { rw ← irreducible_iff_prime, exact second_of_chain_is_irreducible n hn c h₁ (λ r, h₂) hq, }
end

variables {N : Type*} [cancel_comm_monoid_with_zero N] [unique_factorization_monoid N]

lemma multiplicity_le_of_monotone {m p : associates M} {n : associates N}
  (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalized_factors m)
  (d : {l : associates M // l ≤ m} ≃ {l : associates N // l ≤ n}) (hd : monotone d)
  (hd' : monotone d.symm) :
  multiplicity p m ≤ multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n :=
begin
  have : ∀ (s ≠ 0), p^s ≤ m → (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : associates N)^s ≤ n,
  { intros s hs hs',
    suffices : (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : associates N)^s = ↑(d ⟨p^s, hs'⟩),
    { rw this,
      apply subtype.prop (d ⟨p^s, hs'⟩) },
    obtain ⟨c₁, rfl, hc₁', hc₁''⟩ := pow_prime_has_chain s hs (prime_of_normalized_factor p hp),

    set c₂ : fin (s + 1) → associates N := λ t, d ⟨c₁ t, le_trans (hc₁''.2 ⟨t, by simp⟩) hs'⟩,
    have c₂.def : ∀ (t), c₂ t = d ⟨c₁ t, _⟩ := λ t, rfl,
    refine (congr_arg (^s) (c₂.def 1).symm).trans _,
    refine (eq_prime_pow_of_has_chain s hs c₂ (λ t u h, _) (λ r, ⟨λ hr, _, _⟩) _).symm,
    { rw c₂.def,
      apply monotone.strict_mono_of_injective hd (equiv.injective d),
      rw [subtype.mk_lt_mk, strict_mono.lt_iff_lt hc₁'],
      exact h },
    { have : r ≤ n := hr.trans (d ⟨c₁ 1 ^ s, _⟩).2,
      suffices : d.symm ⟨r, this⟩ ≤ ⟨c₁ 1 ^ s, hs'⟩,
      { obtain ⟨i, hi⟩ := hc₁''.1 this,
        use i,
        simp only [c₂.def, ← hi, equiv.apply_symm_apply, subtype.coe_eta, subtype.coe_mk] },
      conv_rhs { rw ← d.symm_apply_apply ⟨c₁ 1 ^ s, hs'⟩ },
      apply hd',
      simpa only [← subtype.coe_le_coe, subtype.coe_mk] using hr },
    { rintros ⟨i, hr⟩,
      rw [hr, c₂.def, subtype.coe_le_coe],
      apply hd,
      simpa [subtype.mk_le_mk] using hc₁''.2 ⟨i, rfl⟩ },
    exact ne_zero_of_dvd_ne_zero hn (subtype.prop (d ⟨c₁ 1 ^ s, _⟩)) },

  have H_finite := multiplicity.finite_prime_left (prime_of_normalized_factor p hp) hm,
  have temp : ↑((multiplicity p m).get H_finite) ≤
    (multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n),
  { rw ← multiplicity.pow_dvd_iff_le_multiplicity,
    refine this _ _ (multiplicity.pow_multiplicity_dvd _),
    intro H,
    apply (multiplicity.dvd_iff_multiplicity_pos.2 (dvd_of_mem_normalized_factors hp)).ne',
    refine part.eq_some_iff.mpr _,
    rw ← H,
    exact part.get_mem H_finite },
  by_cases hcases : ((multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n)).dom,
  { rw ← enat.get_le_get,
    apply (enat.coe_le_iff ((multiplicity p m).get H_finite)
      (multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n)).1 temp,
    rwa ← multiplicity.finite_iff_dom },
  { rw [← enat.ne_top_iff_dom, not_not] at hcases,
    rw hcases,
    exact le_top },
end

end factorisations_same_shape

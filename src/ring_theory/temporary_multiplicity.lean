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
of length `n + 1`, aka we can find strictly increasing bijection bewteen `finset.range (n + 1)` and
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

--this should go in `ring_theory/unique_factorization_monoid.lean`
lemma dvd_prime_pow  {p q : M} (hp : prime p) (n : ℕ) :
  q ∣ p^n ↔ ∃ i ≤ n, associated q (p ^ i) :=
begin
  induction n with n ih generalizing q,
  { simp [← is_unit_iff_dvd_one, associated_one_iff_is_unit] },
  split,
  { intro h,
    rw pow_succ at h,
    rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno),
    { rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h,
      rcases h with ⟨i, hi, hq⟩,
      { refine ⟨i + 1, nat.succ_le_succ hi, (hq.mul_left p).trans _⟩,
        rw pow_succ } },
    { obtain ⟨i, hi, hq⟩ := ih.mp hno,
      exact ⟨i, hi.trans n.le_succ, hq⟩ } },
  { rintro ⟨i, hi, hq⟩,
    exact hq.dvd.trans (pow_dvd_pow p hi) },
end

lemma pow_prime_has_chain {p : associates M} (n : ℕ) (hn : 1 ≤ n) (hp : prime p) :
  ∃ c : finset.range (n + 1) → associates M,
  c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩ = p ∧ strict_mono c ∧ ∀ {r : associates M},
  r ≤ p^n ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩ :=
begin
  refine ⟨λ i, p^(i : ℕ), by simp, λ n m h, _, λ y, ⟨_, _⟩⟩,
  { exact associates.dvd_not_unit_iff_lt.mp ⟨pow_ne_zero n hp.ne_zero, p^(m - n : ℕ),
      not_is_unit_of_not_is_unit_dvd hp.not_unit (dvd_pow (dvd_refl _) (nat.sub_pos_of_lt h).ne'),
      (pow_mul_pow_sub p h.le).symm⟩ },
  { simpa only [← associated_iff_eq] using (dvd_prime_pow hp n).1 },
  { rintro ⟨i, hy', rfl⟩,
    exact ⟨p^(n - i : ℕ), by simpa using (pow_mul_pow_sub p hy').symm⟩ }
end

lemma second_of_chain_not_is_unit (n i : ℕ) (hi : 1 ≤ i ∧ i ≤ n)
  (c : finset.range (n + 1) → associates M) (h₁ : strict_mono c) :
  ¬ is_unit (c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le hi.right)⟩) :=
dvd_not_unit.not_unit (associates.dvd_not_unit_iff_lt.2
  (h₁ $ show (⟨0, finset.mem_range.2 n.zero_lt_succ⟩ : finset.range (n + 1))
    < ⟨i, finset.mem_range.2 (nat.lt_succ_of_le hi.right )⟩, by simp [zero_lt_one.trans_le hi.1]))

lemma first_of_chain_is_unit {q : associates M} (n : ℕ) (c : finset.range (n + 1) → associates M)
  (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩):
  is_unit (c ⟨0, finset.mem_range.2 (nat.zero_lt_succ n) ⟩) :=
begin
  obtain ⟨i, hi, hr⟩ := h₂.mp associates.one_le,
  rw [associates.is_unit_iff_eq_one, ← associates.le_one_iff, hr],
  exact h₁.monotone i.zero_le
end

--this should be in another file
lemma associates.is_atom_iff {p : associates M} (h₁ : p ≠ 0) : is_atom p ↔ irreducible p :=
⟨λ hp, ⟨by simpa only [associates.is_unit_iff_eq_one] using hp.1,
        λ a b h, (eq_bot_or_eq_of_le_atom hp ⟨_, h⟩).cases_on
          (λ ha, or.inl (a.is_unit_iff_eq_one.mpr ha))
          (λ ha, or.inr (show is_unit b, by {rw ha at h, apply is_unit_of_associated_mul
          (show associated (p * b) p, by conv_rhs {rw h}) h₁ }))⟩,
 λ hp, ⟨by simpa only [associates.is_unit_iff_eq_one, associates.bot_eq_one] using hp.1,
        λ b ⟨⟨a, hab⟩, hb⟩, (hp.is_unit_or_is_unit hab).cases_on
          (λ hb, show b = ⊥, by rwa [associates.is_unit_iff_eq_one, ← associates.bot_eq_one] at hb)
          (λ ha, absurd (show p ∣ b, from ⟨(ha.unit⁻¹ : units _), by simp [hab]; rw mul_assoc;
            rw is_unit.mul_coe_inv ha; rw mul_one⟩) hb)⟩⟩

lemma second_of_chain_is_irreducible {q : associates M} (n : ℕ) (hn : 1 ≤ n)
  (c : finset.range (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r}, r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩)
  (hq : q ≠ 0) : irreducible (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩) :=
begin
  refine (associates.is_atom_iff (ne_zero_of_dvd_ne_zero hq (h₂.2 ⟨1, hn, rfl⟩))).mp ⟨_, λ b hb, _⟩,
  { exact ne_bot_of_gt (h₁ (show (⟨0, finset.mem_range.2 (nat.zero_lt_succ n)⟩ : finset.range
    (n + 1)) < ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn) ⟩, by simp)) },
  have h : b ∣ q := hb.le.trans (h₂.2 ⟨1, hn, rfl⟩),
  obtain ⟨i, hi, rfl⟩ := h₂.1 h,
  cases nat.lt_one_iff.mp (h₁.lt_iff_lt.mp hb),
  exact (associates.is_unit_iff_eq_one _).mp (first_of_chain_is_unit n c h₁ @h₂),
end

lemma prime_dvd_eq_second_of_chain {p q r : associates M} (n : ℕ) (hn : 1 ≤ n)
  (c : finset.range (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩)
  (hp : prime p) (hr : r ∣ q) (hp' : p ∣ r) :
  p = c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩ :=
begin
  obtain ⟨i, hi, p_eq⟩ := h₂.1 (dvd_trans hp' hr),
  have : 1 ≤ i,
  { rw [nat.succ_le_iff, pos_iff_ne_zero],
    rintro rfl,
    apply prime.not_unit hp,
    rw p_eq,
    exact first_of_chain_is_unit n c h₁ @h₂ },
  by_cases h : 1 = i,
  { simp only [← h, p_eq] },
  { exfalso,
    have : ¬ prime p,
    { by_contra hcontra,
      have hsub_i : i - 1 ∈ finset.range (n + 1),
      { exact finset.mem_range.2 (nat.lt_trans (nat.sub_lt_of_pos_le 1 i (zero_lt_one) this)
          (nat.lt_succ_of_le hi)) },
      refine (not_irreducible_of_not_unit_dvd_not_unit
        (dvd_not_unit.not_unit (associates.dvd_not_unit_iff_lt.2
        (h₁ (show (⟨0, finset.mem_range.2 (nat.zero_lt_succ n)⟩ : finset.range (n + 1)) <
          ⟨i - 1, hsub_i⟩, from _)) )) _) (prime.irreducible hcontra),
      rw [← subtype.coe_lt_coe, subtype.coe_mk, subtype.coe_mk],
      exact nat.sub_pos_of_lt (nat.lt_of_le_and_ne this h),

      rw [associates.dvd_not_unit_iff_lt, p_eq],
      apply h₁,
      rw [← subtype.coe_lt_coe, subtype.coe_mk, subtype.coe_mk],
      exact (nat.sub_lt_of_pos_le 1 i (zero_lt_one) this) },

    exact this hp },
end

lemma card_subset_divisors_le_length_of_chain {q : associates M} (n : ℕ)
  (c : finset.range (n + 1) → associates M)
  (h₂ : ∀ (r : associates M), r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩)
  (m : finset (associates M)) (hm : ∀ r, r ∈ m → r ≤ q) : m.card ≤ n + 1 :=
begin
  let d : ℕ → associates M := λ s, if temp : s < (n + 1)
    then c ⟨s, finset.mem_range.2 temp ⟩ else q,
  have d_def_finset : ∀ (s < n + 1), d s = c ⟨s, finset.mem_range.2 _⟩,
  { intros s hs,
      simp only [hs, d, dif_pos] },
  have sorry_1: ∀ (r : associates M), r ≤ q → r ∈ (finset.range (n+1)).image d,
  { intros r hr,
    rw finset.mem_image,
    obtain ⟨s, hs, hs'⟩ := (h₂ r).1 hr,
    refine exists.intro s (exists.intro (finset.mem_range.2 (nat.lt_succ_of_le hs)) _),
    rw [d_def_finset s (nat.lt_succ_of_le hs), hs'] },
  have sorry_2 : m ⊆ (finset.range (n+1)).image d :=
     λ x hx, (sorry_1 x) (hm x hx),
  rw ← finset.card_range (n + 1),
  exact le_trans (finset.card_le_of_subset sorry_2) (finset.card_image_le),
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

--this should go in `ring_theory/unique_factorization_monoid.lean`
lemma associated_prime_pow_of_unique_normalized_factor [normalization_monoid M] {p r : M}
  (h : ∀ {m}, m ∈ normalized_factors r → m = p ) (hr : r ≠ 0) : ∃ (i : ℕ), associated (p^i) r :=
begin
  have : ∃ (i : ℕ), normalized_factors r = multiset.repeat p i,
  { use (normalized_factors r).card,
    apply multiset.eq_repeat_of_mem,
    exact (λ b hb, h hb)   },
  obtain ⟨i, hi⟩ := this,
  use i,
  have := unique_factorization_monoid.normalized_factors_prod hr,
  rw [hi, multiset.prod_repeat] at this,
  exact this,
end

lemma mem_chain_eq_pow_second_of_chain {q r : associates M} (n : ℕ) (hn : 1 ≤ n)
  (c : finset.range (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r}, r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩) (hr : r ∣ q)
  (hq : q ≠ 0): ∃ (i ≤ n), r = ((c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^i) :=
begin
  have : ∃ (i : ℕ), normalized_factors r = multiset.repeat (c ⟨1, finset.mem_range.2
    (nat.lt_succ_of_le hn)⟩) i,
  { use (normalized_factors r).card,
    apply multiset.eq_repeat_of_mem,
    intros b hb,
    refine prime_dvd_eq_second_of_chain n hn c h₁ (λ r', h₂) (prime_of_normalized_factor b hb) hr
      (dvd_of_mem_normalized_factors hb) },
  obtain ⟨i, hi⟩ := this,
  use i,
  suffices H : r = (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩ )^i,
  { split,
  { have : (finset.image (λ m, (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^m)
    (finset.range (i + 1))).card = i + 1,
    { conv_rhs {rw [← finset.card_range (i+1)] },
      rw finset.card_image_eq_iff_inj_on,
      apply set.inj_on_of_injective,
      apply pow_injective_of_not_unit (second_of_chain_not_is_unit n 1 ⟨le_refl 1, hn⟩ c h₁)
        (irreducible.ne_zero (second_of_chain_is_irreducible n hn c h₁ (λ r, h₂) hq)) },
      suffices H' : ∀ r ∈ (finset.image (λ m, (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^m)
        (finset.range (i + 1))), r ≤ q,
      { apply nat.le_of_succ_le_succ,
        rw [nat.succ_eq_add_one, ← this],
        apply card_subset_divisors_le_length_of_chain n c (λ r', h₂) (finset.image
          (λ m, (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^m) (finset.range (i + 1))) H' },

      intros r hr,
      rw finset.mem_image at hr,
      obtain ⟨a, ha, rfl⟩:= hr,
      refine dvd_trans _ hr,
      use (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^(i - a),
      rw pow_mul_pow_sub (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩),
      exact H,

      apply nat.le_of_lt_succ,
      rw nat.succ_eq_add_one,
      exact (finset.mem_range.1 ha) },
   exact H  },

  have := unique_factorization_monoid.normalized_factors_prod (ne_zero_of_dvd_ne_zero hq hr),
  rw [associated_iff_eq, hi, multiset.prod_repeat] at this,
  rw this,
end

lemma eq_prime_pow_of_has_chain {q : associates M} (n : ℕ) (hn : 1 ≤ n)
  (c : finset.range (n + 1) → associates M) (h₁ : strict_mono c)
  (h₂ : ∀ {r : associates M}, r ≤ q ↔ ∃ i ≤ n, r = c ⟨i, finset.mem_range.2 (nat.lt_succ_of_le H)⟩)
  (hq : q ≠ 0) : q = (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^n :=
begin
  obtain ⟨i, hi, hi'⟩ := mem_chain_eq_pow_second_of_chain n hn c h₁ (λ r, h₂) (dvd_refl q) hq,
  suffices : n ≤ i,
  { rw le_antisymm hi this at hi',
    exact hi' },

  apply nat.le_of_succ_le_succ,
  rw [nat.succ_eq_add_one, ← finset.card_range (n+1)],
  refine le_trans (show (finset.range (n+1)).card ≤ ((finset.range (i + 1)).image
    (λ m, (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩)^m)).card, from _) _,

  { let d : ℕ → associates M := λ s, if temp : s < (n + 1) then c ⟨s, finset.mem_range.2 temp⟩
      else q,
    have d_def_finset : ∀ (s < n + 1), d s = c ⟨s, finset.mem_range.2 _⟩,
    { intros s hs,
      simp only [hs, d, dif_pos] },
    have sorry_1 : ((finset.range (n + 1)).image d).card = (finset.range (n + 1)).card,
    { rw finset.card_image_eq_iff_inj_on,
      rw set.inj_on_iff_injective,
      intros a b h,
      obtain ⟨a', ha'⟩:= a,
      obtain ⟨b', hb'⟩:= b,
      rw [set.restrict_apply, set.restrict_apply, subtype.coe_mk, subtype.coe_mk,
        d_def_finset a' (finset.mem_range.1 ha'), d_def_finset b' (finset.mem_range.1 hb')] at h,
      exact (strict_mono.injective h₁ h) },
    rw sorry_1.symm,
    apply finset.card_le_of_subset,
    intros r hr,
    obtain ⟨j, hj, rfl⟩ := finset.mem_image.1 hr,
      have := (h₂.2 (exists.intro j (exists.intro (nat.le_of_lt_succ (finset.mem_range.1 hj))
        (eq.refl (c ⟨j, hj⟩))))),
      rw hi' at this,
      obtain ⟨u, hu, hu'⟩:= (dvd_prime_pow
        (show prime (c ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hn)⟩ ), from _) i).1 this,
      rw associated_iff_eq at hu',
      rw finset.mem_image,
      use u,
      exact ⟨finset.mem_range.2 (nat.lt_of_le_of_lt hu (nat.lt_add_one_iff.2 (le_refl i))),
        by { rw d_def_finset j (finset.mem_range.1 hj), exact hu'.symm} ⟩,
      rw ← irreducible_iff_prime,
      exact second_of_chain_is_irreducible n hn c h₁(λ r, h₂) hq, },

  conv_rhs { rw [nat.succ_eq_add_one, ← finset.card_range (i + 1)] },
  exact finset.card_image_le,
end

variables {N : Type*} [cancel_comm_monoid_with_zero N] [unique_factorization_monoid N]

lemma multiplicity_le_of_monotone {m p : associates M}
  {n : associates N} (hm : m ≠ 0) (hn : n ≠ 0) (hp : p ∈ normalized_factors m)
  (d : { l : associates M // l ≤ m} ≃ {l : associates N // l ≤ n})
  (hd : monotone d) (hd' : monotone d.symm):
  multiplicity p m ≤ multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n :=
begin
  have : ∀ (s ≥ 1), p^s ≤ m → (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : associates N)^s ≤ n,
  { intros s hs hs',
    suffices : (d ⟨p, dvd_of_mem_normalized_factors hp⟩ : associates N)^s = ↑(d ⟨p^s, hs'⟩),
    { rw this,
      apply subtype.prop (d ⟨p^s, hs'⟩) },
    obtain ⟨c₁, hc₁, hc₁', hc₁''⟩ := pow_prime_has_chain s hs (prime_of_normalized_factor p hp),

    set c₂ : finset.range (s + 1) → associates N := λ t, d ⟨c₁ t, le_trans (hc₁''.2 (exists.intro
      t.val (exists.intro (nat.le_of_lt_succ (finset.mem_range.1 t.prop)) (by simp)))) hs'⟩,
    have c₂.def : ∀ (t), c₂ t = d ⟨c₁ t, _⟩ := λ t, rfl,
    simp_rw [← hc₁],
    rw ← c₂.def ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hs)⟩,
    refine (eq_prime_pow_of_has_chain s hs c₂ _ _ _).symm,
    { intros t u h,
      rw c₂.def,
      apply monotone.strict_mono_of_injective hd (equiv.injective d),
      rw [subtype.mk_lt_mk, strict_mono.lt_iff_lt hc₁'],
      exact h },
    { refine λ r, ⟨_, _⟩,
      { intro hr,
        have : r ≤ n,
          apply le_trans hr
            (show ↑(d ⟨c₁ ⟨1, _⟩ ^ s, _⟩) ≤ n, from subtype.prop (d ⟨c₁ ⟨1, _⟩ ^ s, _⟩)),
        suffices : d.symm ⟨r, this⟩ ≤ ⟨p^s, hs'⟩,
        { obtain ⟨i, hi, hi'⟩ := hc₁''.1 this,
          exact exists.intro i (exists.intro hi (by simp only [c₂.def, ← hi',
            equiv.apply_symm_apply, subtype.coe_eta, subtype.coe_mk] )) },
        conv_rhs {rw ← equiv.symm_apply_apply d ⟨p^s, hs'⟩},
        apply hd',
        simpa [hc₁, hr, subtype.coe_le_coe] using hr },
      { intro H,
        obtain ⟨i, hi, hr⟩ := H,
        rw [hr, c₂.def, subtype.coe_le_coe],
        apply hd,
        simpa [hc₁, subtype.mk_le_mk] using hc₁''.2 (exists.intro i (exists.intro hi rfl)) } },
    apply ne_zero_of_dvd_ne_zero hn (subtype.prop (d ⟨c₁ ⟨1, _⟩ ^ s, _⟩)) },

  have H_finite := multiplicity.finite_prime_left (prime_of_normalized_factor p hp) hm,
  have temp : ↑((multiplicity p m).get H_finite) ≤
    (multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n),
  { rw ← multiplicity.pow_dvd_iff_le_multiplicity,
    apply this,
    rw [← enat.get_one (enat.dom_some 1), ge_iff_le, enat.get_le_get],
    exact enat.pos_iff_one_le.1 (multiplicity.dvd_iff_multiplicity_pos.2
      (dvd_of_mem_normalized_factors hp)),
    apply multiplicity.pow_multiplicity_dvd },
  by_cases hcases : ((multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n)).dom,
  { rw ← enat.get_le_get,
    apply (enat.coe_le_iff ((multiplicity p m).get H_finite)
    (multiplicity ↑(d ⟨p, dvd_of_mem_normalized_factors hp⟩) n)).1 temp,
    rw ← multiplicity.finite_iff_dom,
    exact hcases },
  { rw [← enat.ne_top_iff_dom, not_not] at hcases,
    rw hcases,
    exact le_top },
end

end factorisations_same_shape

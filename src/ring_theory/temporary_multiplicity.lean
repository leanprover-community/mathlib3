import algebra.squarefree
import ring_theory.unique_factorization_domain

open_locale classical

open unique_factorization_monoid

lemma multiplicity.finite_prime_left {R : Type*} [cancel_comm_monoid_with_zero R]
  [wf_dvd_monoid R] [decidable_rel ((∣) : R → R → Prop)] {a b : R} (ha : prime a) (hb : b ≠ 0) :
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

variables {N : Type*} [cancel_comm_monoid_with_zero N] [unique_factorization_monoid N]
variables {M : Type*} [cancel_comm_monoid_with_zero M] [unique_factorization_monoid M]

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
    obtain ⟨c₁, hc₁, hc₁', hc₁''⟩ := pow_prime' s hs (prime_of_normalized_factor p hp),

    set c₂ : finset.range (s + 1) → associates N := λ t, d ⟨c₁ t, le_trans (hc₁''.2 (exists.intro
      t.val (exists.intro (nat.le_of_lt_succ (finset.mem_range.1 t.prop)) (by simp)))) hs'⟩,
    have c₂.def : ∀ (t), c₂ t = d ⟨c₁ t, _⟩ := λ t, rfl,
    simp_rw [← hc₁],
    rw ← c₂.def ⟨1, finset.mem_range.2 (nat.lt_succ_of_le hs)⟩,
    refine (pow_prime₆' s hs c₂ _ _ _).symm,
    { intros t u h,
      rw c₂.def,
      apply monotone.strict_mono_of_injective hd (equiv.injective d),
      rw [subtype.mk_lt_mk, strict_mono.lt_iff_lt hc₁'],
      exact h },
    { intro r,
      split,
      { intro hr,
        have : r ≤ n,
          apply le_trans hr
            (show ↑(d ⟨c₁ ⟨1, _⟩ ^ s, _⟩) ≤ n, from subtype.prop (d ⟨c₁ ⟨1, _⟩ ^ s, _⟩)),
        have temp_r : d.symm ⟨r, this⟩ ≤ ⟨p^s, hs'⟩,
          conv_rhs {rw ← equiv.symm_apply_apply d ⟨p^s, hs'⟩},
          apply hd',
          simpa [hc₁, hr, subtype.coe_le_coe] using hr,
        obtain ⟨i, hi, hi'⟩ := hc₁''.1 temp_r,
        exact exists.intro i (exists.intro hi (by simp only [c₂.def, ← hi', equiv.apply_symm_apply,
          subtype.coe_eta, subtype.coe_mk] )) },
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

lemma multiplicity_eq_multiplicity_mk_monoid_hom [wf_dvd_monoid M] {p q : M} (hp : prime p)
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

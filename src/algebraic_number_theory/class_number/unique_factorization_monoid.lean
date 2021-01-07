import ring_theory.unique_factorization_domain

namespace unique_factorization_monoid

/-- In a unique factorization monoid, there are finitely many divisors of `x`, up to units. -/
noncomputable def finite_divisors
  {R : Type*} [comm_cancel_monoid_with_zero R] [unique_factorization_monoid R]
  {x : R} (x_ne : x ≠ 0) : fintype {y : associates R // y ∣ associates.mk x} :=
begin
  haveI : nontrivial R := ⟨⟨x, 0, x_ne⟩⟩,
  haveI := @unique_factorization_monoid.normalization_monoid R _ _ _,
  haveI := classical.dec_eq R,
  haveI := classical.dec_eq (associates R),
  set divisors := ((factors x).powerset.map (λ (s : multiset R), associates.mk s.prod)).to_finset,
  apply fintype.of_finset divisors,
  intro y,
  obtain ⟨y, rfl⟩ := associates.mk_surjective y,
  simp only [exists_prop, multiset.mem_to_finset, multiset.mem_powerset, exists_eq_right,
    multiset.mem_map, associates.mk_eq_mk_iff_associated],
  split,
  { rintros ⟨s, hs, hy⟩,
    apply associates.mk_dvd_mk.mpr,
    have prod_s_ne : s.prod ≠ 0,
    { intro hz,
      apply x_ne (eq_zero_of_zero_dvd _),
      rw multiset.prod_eq_zero_iff at hz,
      rw ← dvd_iff_dvd_of_rel_right (factors_prod x_ne),
      exact multiset.dvd_prod (multiset.mem_of_le hs hz) },
    have y_ne : y ≠ 0,
    { intro y_eq,
      rw [y_eq, associated_zero_iff_eq_zero] at hy,
      exact prod_s_ne hy },
    rw [← dvd_iff_dvd_of_rel_left hy, ← dvd_iff_dvd_of_rel_right (factors_prod x_ne)],
    exact multiset.prod_dvd_prod hs },
    { rintro (h : associates.mk y ∣ associates.mk x),
      rw associates.mk_dvd_mk at h,
      have hy : y ≠ 0, { refine mt (λ hy, _) x_ne, rwa [hy, zero_dvd_iff] at h },
      refine ⟨factors y, _, factors_prod hy⟩,
      exact (dvd_iff_factors_le_factors hy x_ne).mp h },
end

end unique_factorization_monoid

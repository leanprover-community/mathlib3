import data.zmod.quotient
import algebra.module.pid

open_locale direct_sum

namespace add_comm_group

theorem equiv_free_prod_direct_sum_zmod (G : Type*) [add_comm_group G] [hG : add_group.fg G] :
  ∃ (n : ℕ) (ι : Type) [fintype ι] (p : ι → ℕ) [∀ i, nat.prime $ p i] (e : ι → ℕ),
  nonempty $ G ≃+ (fin n →₀ ℤ) × ⨁ (i : ι), zmod (p i ^ e i) :=
begin
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ :=
    @module.equiv_free_prod_direct_sum _ _ _ _ _ _ _ (module.finite.iff_add_group_fg.mpr hG),
  refine ⟨n, ι, fι, λ i, (p i).nat_abs, λ i, _, e, ⟨_⟩⟩,
  { rw [← int.prime_iff_nat_abs_prime, ← gcd_monoid.irreducible_iff_prime], exact hp i },
  exact f.to_add_equiv.trans ((add_equiv.refl _).prod_congr $ dfinsupp.map_range.add_equiv $
    λ i, ((int.quotient_span_equiv_zmod _).trans $
      zmod.ring_equiv_congr $ (p i).nat_abs_pow _).to_add_equiv)
end

theorem equiv_direct_sum_zmod_of_fintype (G : Type*) [add_comm_group G] [fintype G] :
  ∃ (ι : Type) [fintype ι] (p : ι → ℕ) [∀ i, nat.prime $ p i] (e : ι → ℕ),
  nonempty $ G ≃+ ⨁ (i : ι), zmod (p i ^ e i) :=
begin
  obtain ⟨n, ι, fι, p, hp, e, ⟨f⟩⟩ := equiv_free_prod_direct_sum_zmod G,
  cases n,
  { exact ⟨ι, fι, p, hp, e, ⟨f.trans $ add_equiv.unique_prod _ _⟩⟩ },
  { haveI := @fintype.prod_left _ _ _ (fintype.of_equiv G f.to_equiv) _,
    exact (fintype.of_surjective (λ f : fin n.succ →₀ ℤ, f 0) $
      λ a, ⟨finsupp.single 0 a, finsupp.single_eq_same⟩).false.elim }
end

end add_comm_group

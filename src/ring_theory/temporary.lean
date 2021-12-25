
import ring_theory.dedekind_domain

variables {T : Type u_1} [comm_ring T] [is_domain T] [is_dedekind_domain T] {I : ideal T}
variables {S : Type u_2}  [comm_ring S] [is_domain S] [is_dedekind_domain S] {J : ideal S}
open ideal unique_factorization_monoid

/-- The bijection between the sets of divisors of `I` and `J` induced by the ring isomorphism
    `R/I ≃+* S/J` -/
@[simps]
def ideal_correspondence (f : I.quotient ≃+* J.quotient) :
  {p : ideal T | p ∣ I} ≃ {p : ideal S | p ∣ J} :=
{
  to_fun := λ X, ⟨comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)),
    begin
      rw [set.mem_set_of_eq, dvd_iff_le],
      have : (J^.quotient.mk).ker ≤ comap J^.quotient.mk (map ↑f (map I^.quotient.mk X)),
      { exact ker_le_comap J^.quotient.mk },
      rw mk_ker at this,
      exact this,
    end ⟩,
  inv_fun := λ X, ⟨comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)),
    begin
      rw [set.mem_set_of_eq, dvd_iff_le],
      have : (I^.quotient.mk).ker ≤ comap I^.quotient.mk (map ↑(f.symm) (map J^.quotient.mk X)),
      { exact ker_le_comap I^.quotient.mk },
      rw mk_ker at this,
      exact this,
    end⟩,
  left_inv := λ X,
  begin
    obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective, map_of_equiv _ f, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 hp,
  end,
  right_inv := λ X,
    begin
      obtain ⟨p, hp⟩:= X,
      rw [subtype.mk_eq_mk, subtype.coe_mk, subtype.coe_mk, map_comap_of_surjective _
        quotient.mk_surjective],
      nth_rewrite 0 ← ring_equiv.symm_symm f,
      rw [map_of_equiv _ f.symm, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 hp,
    end
}

lemma ideal_correspondence_symm (f : I.quotient ≃+* J.quotient) :
  (ideal_correspondence f).symm = ideal_correspondence f.symm := rfl

lemma ideal_correspondence_mono (f : I.quotient ≃+* J.quotient)
  {p q : ideal T} (hp : p ∣ I) (hq : q ∣ I) (h : p ≤ q) :
  ↑(ideal_correspondence f ⟨p, hp⟩) ≤ ( ideal_correspondence f ⟨q, hq⟩ : ideal S) :=
begin
  rw [ideal_correspondence_apply_coe, subtype.coe_mk, ideal_correspondence_apply_coe,
    subtype.coe_mk, comap_le_comap_iff_of_surjective J^.quotient.mk quotient.mk_surjective],
  apply le_map_of_comap_le_of_surjective ↑f,
  rw ring_equiv.coe_to_ring_hom,
  exact ring_equiv.surjective f,
  apply le_map_of_comap_le_of_surjective I^.quotient.mk quotient.mk_surjective,
  rw [map_comap_of_equiv, comap_of_equiv, comap_map_of_surjective I^.quotient.mk
    quotient.mk_surjective, ← ring_hom.ker_eq_comap_bot, mk_ker, sup_eq_left.2 (le_of_dvd hp)],
  exact h,
end

lemma ideal_correspondence_mono' (f : I.quotient ≃+* J.quotient)
  {p q : ideal T} (hp : p ∣ I) (hq : q ∣ I) : p ≤ q
    ↔ ↑(ideal_correspondence f ⟨p, hp⟩) ≤ ( ideal_correspondence f ⟨q, hq⟩ : ideal S) :=
begin
  split,
  { exact (λ h, ideal_correspondence_mono f hp hq h) },
  { intro h,
    suffices : (ideal_correspondence f).symm (ideal_correspondence f ⟨p, hp⟩)
      ≤ (ideal_correspondence f).symm (ideal_correspondence f ⟨q, hq⟩),
    { rw [equiv.symm_apply_apply, equiv.symm_apply_apply, subtype.mk_le_mk] at this,
      exact this },
    exact ideal_correspondence_mono f.symm _ _ h  }
end

lemma ideal.mem_normalized_factors_of_dvd_is_prime {p : ideal T} (hI : I ≠ ⊥) (hp : is_prime p)
  (hp' : p ∣ I) : p ∈ normalized_factors I :=
begin
  obtain ⟨q, hq, hq'⟩ := exists_mem_normalized_factors_of_dvd hI (prime_of_is_prime
    (ne_bot_of_le_ne_bot hI (le_of_dvd hp')) hp).irreducible hp',
  rw associated_iff_eq at hq',
  rw hq',
  exact hq,
end

lemma ideal_correspondence_is_prime_of_is_prime (hJ : J ≠ ⊥)
  (f : I.quotient ≃+* J.quotient) {p : ideal T} (hp : p ∈ normalized_factors I) :
  ↑(ideal_correspondence f ⟨p, dvd_of_mem_normalized_factors hp⟩) ∈ normalized_factors J :=
begin
  suffices : is_prime (ideal_correspondence f
    ⟨p, dvd_of_mem_normalized_factors hp⟩ : ideal S),
  { exact ideal.mem_normalized_factors_of_dvd_is_prime hJ this
      (subtype.prop (ideal_correspondence f ⟨p, dvd_of_mem_normalized_factors hp⟩)) },

  rw ideal_correspondence_apply_coe,
  convert comap_is_prime J^.quotient.mk _,
  convert map_is_prime_of_equiv f,
  convert map_is_prime_of_surjective quotient.mk_surjective _,
  rw subtype.coe_mk,
  exact is_prime_of_prime (prime_of_normalized_factor p hp),

  rw mk_ker,
  rw subtype.coe_mk,
  exact le_of_dvd (dvd_of_mem_normalized_factors hp),
end

lemma ideal.dvd_is_prime_pow {p q : ideal T} (hp : p.is_prime) (hp' : p ≠ ⊥){n : ℕ} :
  q ∣ p^n ↔ ∃ i ≤ n, q = p^i :=
begin
  simp_rw [← associated_iff_eq],
  exact dvd_prime_pow (prime_of_is_prime hp' hp) n,
end


def factors_associates (I) :
  {p : ideal T | p ∣ I} ≃ {p : associates (ideal T) | p ∣ (associates.mk I)} :=
equiv.of_bijective (λ p, ⟨associates.mk ↑p, associates.mk_dvd_mk.2 (subtype.prop p)⟩)
begin
  split,
  { intros p p' h,
    rw [subtype.mk_eq_mk, associates.mk_eq_mk_iff_associated, associated_iff_eq] at h,
    exact subtype.ext h },
  { intro p,
    obtain ⟨a, ha⟩ := associates.mk_surjective (p : associates (ideal T)),
    use a,
    apply associates.mk_dvd_mk.1,
    rw ha,
    exact (subtype.prop p),
    simp only [ha, subtype.coe_eta, subtype.coe_mk] },
end


lemma factors_associates_mono :
  strict_mono (factors_associates I) :=
begin
  sorry,
end

def associates_ideal_correspondence (f : I.quotient ≃+* J.quotient) :
  {p : associates (ideal T) | p ∣ (associates.mk I)} ≃
  {p : associates (ideal S) | p ∣ (associates.mk J)} :=
(factors_associates I).symm.trans ((ideal_correspondence f).trans (factors_associates J))


lemma preserves_multiplicityₐ (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p : ideal T} (hp : p ∈ normalized_factors I) :
  multiplicity (associates.mk p) (associates.mk I) =
  multiplicity (associates.mk ↑(ideal_correspondence f ⟨p, dvd_of_mem_normalized_factors hp⟩))
  (associates.mk J) :=
begin
  sorry,

end

lemma preserves_multiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient)
  {p : ideal T} (hp : p ∈ normalized_factors I) : multiplicity p I =
    multiplicity ↑(ideal_correspondence f ⟨p, dvd_of_mem_normalized_factors hp⟩) J :=
sorry


/-- The bijection between the sets of prime factors of `I` and `J` induced by the ring isomorphism
    `R/I ≃+* S/J` -/
@[simps]
def prime_factors_equiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (f : I.quotient ≃+* J.quotient) :
  {p : ideal T | p ∈ normalized_factors I} ≃ {p : ideal S | p ∈ normalized_factors J} :=
{
  to_fun := λ X, ⟨↑(ideal_correspondence f ⟨X.1, dvd_of_mem_normalized_factors X.2⟩),
    ideal_correspondence_is_prime_of_is_prime hJ f X.2⟩,
  inv_fun := λ X, ⟨↑(ideal_correspondence f.symm ⟨X.1, dvd_of_mem_normalized_factors X.2⟩),
    ideal_correspondence_is_prime_of_is_prime hI f.symm X.2⟩,
  left_inv := λ X,
  begin
    obtain ⟨p, hp⟩ := X,
    have : comap (I^.quotient.mk) (map ↑(f.symm) (map (J^.quotient.mk) (comap (J^.quotient.mk)
      (map ↑f (map (I^.quotient.mk) p))))) = p,
      rw [map_comap_of_surjective _
        quotient.mk_surjective, map_of_equiv _ f, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 (dvd_of_mem_normalized_factors hp),
    simp only [subtype.mk_eq_mk, subtype.coe_mk, ideal_correspondence_apply_coe, this],
  end,
  right_inv := λ X,
  begin
    obtain ⟨p, hp⟩ := X,
    have : comap (J^.quotient.mk) (map ↑f (map (I^.quotient.mk) (comap (I^.quotient.mk)
      (map ↑(f.symm) (map (J^.quotient.mk) p))))) = p,
    { rw map_comap_of_surjective _ quotient.mk_surjective,
      nth_rewrite 0 ← ring_equiv.symm_symm f,
      rw [map_of_equiv _ f.symm, comap_map_of_surjective _ quotient.mk_surjective,
        ← ring_hom.ker_eq_comap_bot, mk_ker, sup_of_le_left],
      exact dvd_iff_le.1 (dvd_of_mem_normalized_factors hp) },
    simp only [subtype.mk_eq_mk, subtype.coe_mk, ideal_correspondence_apply_coe, this],
  end
}

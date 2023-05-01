/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.ideal.quotient_operations
import ring_theory.localization.basic

/-!
# Ideals in localizations of commutative rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/

namespace is_localization

section comm_semiring
variables {R : Type*} [comm_semiring R] (M : submonoid R) (S : Type*) [comm_semiring S]
variables [algebra R S] [is_localization M S]

include M

/-- Explicit characterization of the ideal given by `ideal.map (algebra_map R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_algebra_map_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
private def map_ideal (I : ideal R) : ideal S :=
{ carrier := { z : S | ∃ x : I × M, z * algebra_map R S x.2 = algebra_map R S x.1},
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩,
  add_mem' := begin
    rintros a b ⟨a', ha⟩ ⟨b', hb⟩,
    use ⟨a'.2 * b'.1 + b'.2 * a'.1, I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩,
    use a'.2 * b'.2,
    simp only [ring_hom.map_add, submodule.coe_mk, submonoid.coe_mul, ring_hom.map_mul],
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebra_map R S a'.2) (algebra_map R S b'.2),
        ← mul_assoc b, hb],
    ring
  end,
  smul_mem' := begin
    rintros c x ⟨x', hx⟩,
    obtain ⟨c', hc⟩ := is_localization.surj M c,
    use ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩,
    use c'.2 * x'.2,
    simp only [←hx, ←hc, smul_eq_mul, submodule.coe_mk, submonoid.coe_mul, ring_hom.map_mul],
    ring
  end }

theorem mem_map_algebra_map_iff {I : ideal R} {z} :
  z ∈ ideal.map (algebra_map R S) I ↔ ∃ x : I × M, z * algebra_map R S x.2 = algebra_map R S x.1 :=
begin
  split,
  { change _ → z ∈ map_ideal M S I,
    refine λ h, ideal.mem_Inf.1 h (λ z hz, _),
    obtain ⟨y, hy⟩ := hz,
    use ⟨⟨⟨y, hy.left⟩, 1⟩, by simp [hy.right]⟩ },
  { rintros ⟨⟨a, s⟩, h⟩,
    rw [← ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm],
    exact h.symm ▸ ideal.mem_map_of_mem _ a.2 }
end

theorem map_comap (J : ideal S) :
  ideal.map (algebra_map R S) (ideal.comap (algebra_map R S) J) = J :=
le_antisymm (ideal.map_le_iff_le_comap.2 le_rfl) $ λ x hJ,
begin
  obtain ⟨r, s, hx⟩ := mk'_surjective M x,
  rw ←hx at ⊢ hJ,
  exact ideal.mul_mem_right _ _ (ideal.mem_map_of_mem _ (show (algebra_map R S) r ∈ J, from
    mk'_spec S r s ▸ J.mul_mem_right ((algebra_map R S) s) hJ)),
end

theorem comap_map_of_is_prime_disjoint (I : ideal R) (hI : I.is_prime)
  (hM : disjoint (M : set R) I) :
  ideal.comap (algebra_map R S) (ideal.map (algebra_map R S) I) = I :=
begin
  refine le_antisymm (λ a ha, _) ideal.le_comap_map,
  obtain ⟨⟨b, s⟩, h⟩ := (mem_map_algebra_map_iff M S).1 (ideal.mem_comap.1 ha),
  replace h : algebra_map R S (s * a) = algebra_map R S b :=
    by simpa only [←map_mul, mul_comm] using h,
  obtain ⟨c, hc⟩ := (eq_iff_exists M S).1 h,
  have : (↑c * ↑s) * a ∈ I := by { rw [mul_assoc, hc], exact I.mul_mem_left c b.2 },
  exact (hI.mem_or_mem this).resolve_left (λ hsc, hM.le_bot ⟨(c * s).2, hsc⟩)
end

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def order_embedding : ideal S ↪o ideal R :=
{ to_fun := λ J, ideal.comap (algebra_map R S) J,
  inj'   := function.left_inverse.injective (map_comap M S),
  map_rel_iff'   := λ J₁ J₂, ⟨λ hJ, (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ ideal.map_mono hJ,
    ideal.comap_mono⟩ }

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
lemma is_prime_iff_is_prime_disjoint (J : ideal S) :
  J.is_prime ↔ (ideal.comap (algebra_map R S) J).is_prime ∧
    disjoint (M : set R) ↑(ideal.comap (algebra_map R S) J) :=
begin
  split,
  { refine λ h, ⟨⟨_, _⟩, set.disjoint_left.mpr $ λ m hm1 hm2,
      h.ne_top (ideal.eq_top_of_is_unit_mem _ hm2 (map_units S ⟨m, hm1⟩))⟩,
    { refine λ hJ, h.ne_top _,
      rw [eq_top_iff, ← (order_embedding M S).le_iff_le],
      exact le_of_eq hJ.symm },
    { intros x y hxy,
      rw [ideal.mem_comap, ring_hom.map_mul] at hxy,
      exact h.mem_or_mem hxy } },
  { refine λ h, ⟨λ hJ, h.left.ne_top (eq_top_iff.2 _), _⟩,
    { rwa [eq_top_iff, ← (order_embedding M S).le_iff_le] at hJ },
    { intros x y hxy,
      obtain ⟨a, s, ha⟩ := mk'_surjective M x,
      obtain ⟨b, t, hb⟩ := mk'_surjective M y,
      have : mk' S (a * b) (s * t) ∈ J := by rwa [mk'_mul, ha, hb],
      rw [mk'_mem_iff, ← ideal.mem_comap] at this,
      replace this := h.left.mem_or_mem this,
      rw [ideal.mem_comap, ideal.mem_comap] at this,
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff] } }
end

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
lemma is_prime_of_is_prime_disjoint (I : ideal R) (hp : I.is_prime)
  (hd : disjoint (M : set R) ↑I) : (ideal.map (algebra_map R S) I).is_prime :=
begin
  rw [is_prime_iff_is_prime_disjoint M S, comap_map_of_is_prime_disjoint M S I hp hd],
  exact ⟨hp, hd⟩
end

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def order_iso_of_prime :
  {p : ideal S // p.is_prime} ≃o {p : ideal R // p.is_prime ∧ disjoint (M : set R) ↑p} :=
{ to_fun := λ p, ⟨ideal.comap (algebra_map R S) p.1,
                  (is_prime_iff_is_prime_disjoint M S p.1).1 p.2⟩,
  inv_fun := λ p, ⟨ideal.map (algebra_map R S) p.1,
                   is_prime_of_is_prime_disjoint M S p.1 p.2.1 p.2.2⟩,
  left_inv := λ J, subtype.eq (map_comap M S J),
  right_inv := λ I, subtype.eq (comap_map_of_is_prime_disjoint M S I.1 I.2.1 I.2.2),
  map_rel_iff' := λ I I', ⟨λ h, (show I.val ≤ I'.val,
    from (map_comap M S I.val) ▸ (map_comap M S I'.val) ▸ (ideal.map_mono h)), λ h x hx, h hx⟩ }

end comm_semiring

section comm_ring
variables {R : Type*} [comm_ring R] (M : submonoid R) (S : Type*) [comm_ring S]
variables [algebra R S] [is_localization M S]

include M

/-- `quotient_map` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
lemma surjective_quotient_map_of_maximal_of_localization {I : ideal S} [I.is_prime] {J : ideal R}
  {H : J ≤ I.comap (algebra_map R S)} (hI : (I.comap (algebra_map R S)).is_maximal) :
  function.surjective (I.quotient_map (algebra_map R S) H) :=
begin
  intro s,
  obtain ⟨s, rfl⟩ := ideal.quotient.mk_surjective s,
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M s,
  by_cases hM : (ideal.quotient.mk (I.comap (algebra_map R S))) m = 0,
  { have : I = ⊤,
    { rw ideal.eq_top_iff_one,
      rw [ideal.quotient.eq_zero_iff_mem, ideal.mem_comap] at hM,
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM,
      rw [← mk'_eq_mul_mk'_one, mk'_self] },
    exact ⟨0, eq_comm.1 (by simp [ideal.quotient.eq_zero_iff_mem, this])⟩ },
  { rw ideal.quotient.maximal_ideal_iff_is_field_quotient at hI,
    obtain ⟨n, hn⟩ := hI.3 hM,
    obtain ⟨rn, rfl⟩ := ideal.quotient.mk_surjective n,
    refine ⟨(ideal.quotient.mk J) (r * rn), _⟩,
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    rw ← ring_hom.map_mul at hn,
    replace hn := congr_arg (ideal.quotient_map I (algebra_map R S) le_rfl) hn,
    simp only [ring_hom.map_one, ideal.quotient_map_mk, ring_hom.map_mul] at hn,
    rw [ideal.quotient_map_mk, ← sub_eq_zero, ← ring_hom.map_sub,
      ideal.quotient.eq_zero_iff_mem, ← ideal.quotient.eq_zero_iff_mem, ring_hom.map_sub,
      sub_eq_zero, mk'_eq_mul_mk'_one],
    simp only [mul_eq_mul_left_iff, ring_hom.map_mul],
    exact or.inl (mul_left_cancel₀ (λ hn, hM (ideal.quotient.eq_zero_iff_mem.2
      (ideal.mem_comap.2 (ideal.quotient.eq_zero_iff_mem.1 hn)))) (trans hn
      (by rw [← ring_hom.map_mul, ← mk'_eq_mul_mk'_one, mk'_self, ring_hom.map_one]))) }
end

open_locale non_zero_divisors

lemma bot_lt_comap_prime [is_domain R] (hM : M ≤ R⁰)
  (p : ideal S) [hpp : p.is_prime] (hp0 : p ≠ ⊥) :
  ⊥ < ideal.comap (algebra_map R S) p :=
begin
  haveI : is_domain S := is_domain_of_le_non_zero_divisors _ hM,
  convert (order_iso_of_prime M S).lt_iff_lt.mpr
    (show (⟨⊥, ideal.bot_prime⟩ : {p : ideal S // p.is_prime}) < ⟨p, hpp⟩, from hp0.bot_lt),
  exact (ideal.comap_bot_of_injective (algebra_map R S) (is_localization.injective _ hM)).symm,
end

end comm_ring

end is_localization

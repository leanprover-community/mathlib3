/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import field_theory.splitting_field
import ring_theory.integral_closure
import ring_theory.localization.integral

/-!
# Integrally closed rings

An integrally closed domain `R` contains all the elements of `Frac(R)` that are
integral over `R`. A special case of integrally closed domains are the Dedekind domains.

## Main definitions

* `is_integrally_closed R` states `R` contains all integral elements of `Frac(R)`

## Main results

* `is_integrally_closed_iff K`, where `K` is a fraction field of `R`, states `R`
  is integrally closed iff it is the integral closure of `R` in `K`
-/

open_locale non_zero_divisors polynomial

open polynomial

/-- `R` is integrally closed if all integral elements of `Frac(R)` are also elements of `R`.

This definition uses `fraction_ring R` to denote `Frac(R)`. See `is_integrally_closed_iff`
if you want to choose another field of fractions for `R`.
-/
class is_integrally_closed (R : Type*) [comm_ring R] [is_domain R] : Prop :=
(algebra_map_eq_of_integral :
  ∀ {x : fraction_ring R}, is_integral R x → ∃ y, algebra_map R (fraction_ring R) y = x)

section iff

variables {R : Type*} [comm_ring R] [is_domain R]
variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]

/-- `R` is integrally closed iff all integral elements of its fraction field `K`
are also elements of `R`. -/
theorem is_integrally_closed_iff :
  is_integrally_closed R ↔ ∀ {x : K}, is_integral R x → ∃ y, algebra_map R K y = x :=
begin
  let e : K ≃ₐ[R] fraction_ring R := is_localization.alg_equiv R⁰_ _,
  split,
  { rintros ⟨cl⟩,
    refine λ x hx, _,
    obtain ⟨y, hy⟩ := cl ((is_integral_alg_equiv e).mpr hx),
    exact ⟨y, e.algebra_map_eq_apply.mp hy⟩ },
  { rintros cl,
    refine ⟨λ x hx, _⟩,
    obtain ⟨y, hy⟩ := cl ((is_integral_alg_equiv e.symm).mpr hx),
    exact ⟨y, e.symm.algebra_map_eq_apply.mp hy⟩ },
end

/-- `R` is integrally closed iff it is the integral closure of itself in its field of fractions. -/
theorem is_integrally_closed_iff_is_integral_closure :
  is_integrally_closed R ↔ is_integral_closure R R K :=
(is_integrally_closed_iff K).trans $
begin
  let e : K ≃ₐ[R] fraction_ring R := is_localization.alg_equiv R⁰_ _,
  split,
  { intros cl,
    refine ⟨is_fraction_ring.injective _ _, λ x, ⟨cl, _⟩⟩,
    rintros ⟨y, y_eq⟩,
    rw ← y_eq,
    exact is_integral_algebra_map },
  { rintros ⟨-, cl⟩ x hx,
    exact cl.mp hx }
end

end iff

namespace is_integrally_closed

variables {R : Type*} [comm_ring R] [id : is_domain R] [iic : is_integrally_closed R]
variables {K : Type*} [field K] [algebra R K] [ifr : is_fraction_ring R K]

include iic ifr

instance : is_integral_closure R R K := (is_integrally_closed_iff_is_integral_closure K).mp iic

lemma is_integral_iff {x : K} : is_integral R x ↔ ∃ y : R, algebra_map R K y = x :=
is_integral_closure.is_integral_iff

lemma exists_algebra_map_eq_of_is_integral_pow {x : K} {n : ℕ} (hn : 0 < n)
  (hx : is_integral R $ x ^ n) : ∃ y : R, algebra_map R K y = x :=
is_integral_iff.mp $ is_integral_of_pow hn hx

omit iic ifr

lemma exists_algebra_map_eq_of_pow_mem_subalgebra {K : Type*} [field K] [algebra R K]
  {S : subalgebra R K} [is_integrally_closed S] [is_fraction_ring S K] {x : K} {n : ℕ} (hn : 0 < n)
  (hx : x ^ n ∈ S) : ∃ y : S, algebra_map S K y = x :=
exists_algebra_map_eq_of_is_integral_pow hn $ is_integral_iff.mpr ⟨⟨x ^ n, hx⟩, rfl⟩

include id ifr

variables {R} (K)
lemma integral_closure_eq_bot_iff :
  integral_closure R K = ⊥ ↔ is_integrally_closed R :=
begin
  refine eq_bot_iff.trans _,
  split,
  { rw is_integrally_closed_iff K,
    intros h x hx,
    exact set.mem_range.mp (algebra.mem_bot.mp (h hx)),
    assumption },
  { intros h x hx,
    rw [algebra.mem_bot, set.mem_range],
    exactI is_integral_iff.mp hx },
end

include iic
variables (R K)
@[simp] lemma integral_closure_eq_bot : integral_closure R K = ⊥ :=
(integral_closure_eq_bot_iff K).mpr ‹_›

end is_integrally_closed

namespace integral_closure

open is_integrally_closed

variables {R : Type*} [comm_ring R] [is_domain R]
variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
variables {L : Type*} [field L] [algebra K L] [algebra R L] [is_scalar_tower R K L]

-- Can't be an instance because you need to supply `K`.
lemma is_integrally_closed_of_finite_extension [finite_dimensional K L] :
  is_integrally_closed (integral_closure R L) :=
begin
  letI : is_fraction_ring (integral_closure R L) L := is_fraction_ring_of_finite_extension K L,
  exact (integral_closure_eq_bot_iff L).mp integral_closure_idem
end

theorem frange_subset_integral_closure
  {f : R[X]} (hf : f.monic) {g : K[X]} (hg : g.monic) (hd : g ∣ f.map (algebra_map R K)) :
  (g.frange : set K) ⊆ (integral_closure R K).to_subring :=
begin
  haveI : is_scalar_tower R K g.splitting_field := splitting_field_aux.is_scalar_tower _ _ _,
  have := coeff_mem_subring_of_splits ((splits_id_iff_splits _).2 $ splitting_field.splits g)
    (hg.map _) (integral_closure R _).to_subring (λ a ha, roots_mem_integral_closure hf _),
  { intros a ha, obtain ⟨n, -, rfl⟩ := mem_frange_iff.1 ha,
    obtain ⟨p, hp, he⟩ := this n, use [p, hp],
    rw [is_scalar_tower.algebra_map_eq R K, coeff_map, ← eval₂_map, eval₂_at_apply] at he,
    rw eval₂_eq_eval_map, apply (injective_iff_map_eq_zero _).1 _ _ he,
    { apply ring_hom.injective } },
  rw [is_scalar_tower.algebra_map_eq R K _, ← map_map],
  refine multiset.mem_of_le (roots.le_of_dvd ((hf.map _).map _).ne_zero _) ha,
  { apply_instance },
  { exact map_dvd (algebra_map K g.splitting_field) hd },
  { apply splitting_field_aux.is_scalar_tower },
end

end integral_closure

namespace is_integrally_closed

variables {R : Type*} [comm_ring R] [is_domain R]
variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]

theorem eq_map_of_dvd_of_monic [is_integrally_closed R] {f : R[X]} (hf : f.monic)
  (g : K[X]) (hg : g.monic) (hd : g ∣ f.map (algebra_map R K)) :
  ∃ g' : R[X], g'.map (algebra_map R K) = g :=
begin
  let algeq := (subalgebra.equiv_of_eq _ _ $
    is_integrally_closed.integral_closure_eq_bot R _).trans
    (algebra.bot_equiv_of_injective $ is_fraction_ring.injective R $ K),
  have : (algebra_map R _).comp algeq.to_alg_hom.to_ring_hom =
    (integral_closure R _).to_subring.subtype,
  { ext, conv_rhs { rw ← algeq.symm_apply_apply x }, refl },
  refine ⟨map algeq.to_alg_hom.to_ring_hom _, _⟩,
  use g.to_subring _ (frange_subset_integral_closure hf hg hd),
  rw [map_map, this],
  apply g.map_to_subring,
end

lemma eq_map_mul_C_of_dvd [nontrivial R] [is_integrally_closed R] {f : R[X]} (hf : f.monic)
  (g : K[X]) (hd : g ∣ f.map (algebra_map R K)) :
  ∃ g' : R[X], (g'.map (algebra_map R K)) * (C $ leading_coeff g) = g :=
begin
  have : g ≠ 0 := ne_zero_of_dvd_ne_zero (monic.ne_zero $ hf.map (algebra_map R K)) hd,
  obtain ⟨g', hg'⟩ := eq_map_of_dvd_of_monic K hf (g * (C (g.leading_coeff⁻¹)))
    (monic_mul_leading_coeff_inv this) _,
  use g',
  rw [hg', mul_assoc, ← C_mul, inv_mul_cancel (leading_coeff_ne_zero.mpr this), C_1, mul_one],
  { rwa associated.dvd_iff_dvd_left (show associated (g * (C (g.leading_coeff⁻¹))) g, from _),
    rw associated_mul_is_unit_left_iff,
    exact is_unit_C.mpr (inv_ne_zero $ leading_coeff_ne_zero.mpr this).is_unit },
end


end is_integrally_closed

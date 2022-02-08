/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import ring_theory.integral_closure
import ring_theory.localization

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

open_locale non_zero_divisors

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

variables {R : Type*} [comm_ring R] [is_domain R] [iic : is_integrally_closed R]
variables {K : Type*} [field K] [algebra R K] [is_fraction_ring R K]

instance : is_integral_closure R R K :=
(is_integrally_closed_iff_is_integral_closure K).mp iic

include iic

lemma is_integral_iff {x : K} : is_integral R x ↔ ∃ y, algebra_map R K y = x :=
is_integral_closure.is_integral_iff

omit iic
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

variables {R : Type*} [comm_ring R] [is_domain R] [iic : is_integrally_closed R]
variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
variables {L : Type*} [field L] [algebra K L] [algebra R L] [is_scalar_tower R K L]

-- Can't be an instance because you need to supply `K`.
lemma is_integrally_closed_of_finite_extension [finite_dimensional K L] :
  is_integrally_closed (integral_closure R L) :=
begin
  letI : is_fraction_ring (integral_closure R L) L := is_fraction_ring_of_finite_extension K L,
  exact (integral_closure_eq_bot_iff L).mp integral_closure_idem
end

end integral_closure

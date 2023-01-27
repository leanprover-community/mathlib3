/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu
-/
import data.finsupp.fintype
import data.mv_polynomial.equiv
import set_theory.cardinal.ordinal
/-!
# Cardinality of Multivariate Polynomial Ring

The main result in this file is `mv_polynomial.cardinal_mk_le_max`, which says that
the cardinality of `mv_polynomial σ R` is bounded above by the maximum of `#R`, `#σ`
and `ℵ₀`.
-/
universes u v

open cardinal
open_locale cardinal

namespace mv_polynomial

section two_universes

variables {σ : Type u} {R : Type v} [comm_semiring R]

@[simp] lemma cardinal_mk_eq_max_lift [nonempty σ] [nontrivial R] :
  #(mv_polynomial σ R) = max (max (cardinal.lift.{u} $ #R) $ cardinal.lift.{v} $ #σ) ℵ₀ :=
(mk_finsupp_lift_of_infinite _ R).trans $
by rw [mk_finsupp_nat, max_assoc, lift_max, lift_aleph_0, max_comm]

@[simp] lemma cardinal_mk_eq_lift [is_empty σ] : #(mv_polynomial σ R) = cardinal.lift.{u} (#R) :=
((is_empty_ring_equiv R σ).to_equiv.trans equiv.ulift.{u}.symm).cardinal_eq

lemma cardinal_lift_mk_le_max {σ : Type u} {R : Type v} [comm_semiring R] :
  #(mv_polynomial σ R) ≤ max (max (cardinal.lift.{u} $ #R) $ cardinal.lift.{v} $ #σ) ℵ₀ :=
begin
  casesI subsingleton_or_nontrivial R,
  { exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0) },
  casesI is_empty_or_nonempty σ,
  { exact cardinal_mk_eq_lift.trans_le (le_max_of_le_left $ le_max_left _ _) },
  { exact cardinal_mk_eq_max_lift.le },
end

end two_universes

variables {σ R : Type u} [comm_semiring R]

lemma cardinal_mk_eq_max [nonempty σ] [nontrivial R] :
  #(mv_polynomial σ R) = max (max (#R) (#σ)) ℵ₀ := by simp

/-- The cardinality of the multivariate polynomial ring, `mv_polynomial σ R` is at most the maximum
of `#R`, `#σ` and `ℵ₀` -/
lemma cardinal_mk_le_max : #(mv_polynomial σ R) ≤ max (max (#R) (#σ)) ℵ₀ :=
cardinal_lift_mk_le_max.trans $ by rw [lift_id, lift_id]

end mv_polynomial

/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import ring_theory.nilpotent
import ring_theory.ideal.quotient_operations

/-!
# Nilpotent elements in quotient rings
-/

lemma ideal.is_radical_iff_quotient_reduced {R : Type*} [comm_ring R] (I : ideal R) :
  I.is_radical ↔ is_reduced (R ⧸ I) :=
by { conv_lhs { rw ← @ideal.mk_ker R _ I },
  exact ring_hom.ker_is_radical_iff_reduced_of_surjective (@ideal.quotient.mk_surjective R _ I) }

variables {R S : Type*} [comm_semiring R] [comm_ring S] [algebra R S] (I : ideal S)

/-- Let `P` be a property on ideals. If `P` holds for square-zero ideals, and if
  `P I → P (J ⧸ I) → P J`, then `P` holds for all nilpotent ideals. -/
lemma ideal.is_nilpotent.induction_on
  (hI : is_nilpotent I)
  {P : ∀ ⦃S : Type*⦄ [comm_ring S], by exactI ∀ I : ideal S, Prop}
  (h₁ : ∀ ⦃S : Type*⦄ [comm_ring S], by exactI ∀ I : ideal S, I ^ 2 = ⊥ → P I)
  (h₂ : ∀ ⦃S : Type*⦄ [comm_ring S], by exactI
    ∀ I J : ideal S, I ≤ J → P I → P (J.map (ideal.quotient.mk I)) → P J) : P I :=
begin
  obtain ⟨n, hI : I ^ n = ⊥⟩ := hI,
  unfreezingI { revert S },
  apply nat.strong_induction_on n,
  clear n,
  introsI n H S _ I hI,
  by_cases hI' : I = ⊥,
  { subst hI', apply h₁, rw [← ideal.zero_eq_bot, zero_pow], exact zero_lt_two },
  cases n,
  { rw [pow_zero, ideal.one_eq_top] at hI,
    haveI := subsingleton_of_bot_eq_top hI.symm,
    exact (hI' (subsingleton.elim _ _)).elim },
  cases n,
  { rw [pow_one] at hI,
    exact (hI' hI).elim },
  apply h₂ (I ^ 2) _ (ideal.pow_le_self two_ne_zero),
  { apply H n.succ _ (I ^ 2),
    { rw [← pow_mul, eq_bot_iff, ← hI, nat.succ_eq_add_one, nat.succ_eq_add_one],
      exact ideal.pow_le_pow (by linarith) },
    { exact le_refl n.succ.succ } },
  { apply h₁, rw [← ideal.map_pow, ideal.map_quotient_self] },
end

lemma is_nilpotent.is_unit_quotient_mk_iff {R : Type*} [comm_ring R] {I : ideal R}
  (hI : is_nilpotent I) {x : R} : is_unit (ideal.quotient.mk I x) ↔ is_unit x :=
begin
  refine ⟨_, λ h, h.map I^.quotient.mk⟩,
  revert x,
  apply ideal.is_nilpotent.induction_on I hI; clear hI I,
  swap,
  { introv e h₁ h₂ h₃,
    apply h₁,
    apply h₂,
    exactI h₃.map ((double_quot.quot_quot_equiv_quot_sup I J).trans
      (ideal.quot_equiv_of_eq (sup_eq_right.mpr e))).symm.to_ring_hom },
  { introv e H,
    resetI,
    obtain ⟨y, hy⟩ := ideal.quotient.mk_surjective (↑(H.unit⁻¹) : S ⧸ I),
    have : ideal.quotient.mk I (x * y) = ideal.quotient.mk I 1,
    { rw [map_one, _root_.map_mul, hy, is_unit.mul_coe_inv] },
    rw ideal.quotient.eq at this,
    have : (x * y - 1) ^ 2 = 0,
    { rw [← ideal.mem_bot, ← e], exact ideal.pow_mem_pow this _ },
    have : x * (y * (2 - x * y)) = 1,
    { rw [eq_comm, ← sub_eq_zero, ← this], ring },
    exact is_unit_of_mul_eq_one _ _ this }
end

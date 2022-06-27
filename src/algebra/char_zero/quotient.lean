/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.char_zero
import group_theory.quotient_group

/-- # Lemmas about quotients in characteristic zero -/

variables {R : Type*} [division_ring R] [char_zero R] {p : R}

namespace quotient_add_group

lemma zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ add_subgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
  z • ψ = z • θ ↔ (∃ k : fin z.nat_abs, ψ = θ + (k : ℕ) • (p / z : R)) :=
begin
  induction ψ using quotient.induction_on',
  induction θ using quotient.induction_on',
  have : (quotient.mk' : R → R ⧸ add_subgroup.zmultiples p) = coe := rfl,
  simp only [this],
  simp_rw [←coe_zsmul, ←coe_nsmul, ←coe_add, quotient_add_group.eq_iff_sub_mem, ←smul_sub,
    add_subgroup.mem_zmultiples_iff, ←sub_sub, (eq_sub_iff_add_eq : _ = (ψ - θ) - _ ↔ _)],
  simp_rw [div_eq_mul_inv, ←smul_mul_assoc],
  have hz' : (z : R) ≠ 0 := int.cast_ne_zero.mpr hz,
  conv_rhs { simp only [←(mul_right_injective₀ hz').eq_iff] { single_pass := tt}, },
  simp_rw [←zsmul_eq_mul, smul_add, ←mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel hz',
    mul_one, ←coe_nat_zsmul, ←mul_smul, ←add_smul],
  split,
  { rintro ⟨k, h⟩,
    simp_rw ← h,
    refine ⟨⟨(k % z).to_nat, _⟩, k / z, _⟩,
    { rw [←int.coe_nat_lt, int.to_nat_of_nonneg (int.mod_nonneg _ hz)],
      exact (int.mod_lt _ hz).trans_eq (int.abs_eq_nat_abs _) },
    rw [subtype.coe_mk, int.to_nat_of_nonneg (int.mod_nonneg _ hz), int.div_add_mod] },
  { rintro ⟨k, n, h⟩,
    exact ⟨_, h⟩, },
end

lemma zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ add_subgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
  n • ψ = n • θ ↔ (∃ k : fin n, ψ = θ + (k : ℕ) • (p / n : R)) :=
begin
  simp_rw [←coe_nat_zsmul ψ, ←coe_nat_zsmul θ,
    zmultiples_zsmul_eq_zsmul_iff (int.coe_nat_ne_zero.mpr hz),  int.cast_coe_nat],
  refl,
end

end quotient_add_group

/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.quotient_group

/-!
# Lemmas about quotients in characteristic zero

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {R : Type*} [division_ring R] [char_zero R] {p : R}

namespace add_subgroup

/-- `z • r` is a multiple of `p` iff `r` is `pk/z` above a multiple of `p`, where `0 ≤ k < |z|`. -/
lemma zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
  z • r ∈ add_subgroup.zmultiples p ↔
    ∃ k : fin z.nat_abs, r - (k : ℕ) • (p / z : R) ∈ add_subgroup.zmultiples p:=
begin
  rw [add_subgroup.mem_zmultiples_iff],
  simp_rw [add_subgroup.mem_zmultiples_iff, div_eq_mul_inv, ←smul_mul_assoc, eq_sub_iff_add_eq],
  have hz' : (z : R) ≠ 0 := int.cast_ne_zero.mpr hz,
  conv_rhs { simp only [←(mul_right_injective₀ hz').eq_iff] { single_pass := tt}, },
  simp_rw [←zsmul_eq_mul, smul_add, ←mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel hz',
    mul_one, ←coe_nat_zsmul, smul_smul, ←add_smul],
  split,
  { rintro ⟨k, h⟩,
    simp_rw ← h,
    refine ⟨⟨(k % z).to_nat, _⟩, k / z, _⟩,
    { rw [←int.coe_nat_lt, int.to_nat_of_nonneg (int.mod_nonneg _ hz)],
      exact (int.mod_lt _ hz).trans_eq (int.abs_eq_nat_abs _) },
    rw [fin.coe_mk, int.to_nat_of_nonneg (int.mod_nonneg _ hz), int.div_add_mod] },
  { rintro ⟨k, n, h⟩,
    exact ⟨_, h⟩, },
end

lemma nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
  n • r ∈ add_subgroup.zmultiples p ↔
    ∃ k : fin n, r - (k : ℕ) • (p / n : R) ∈ add_subgroup.zmultiples p:=
begin
  simp_rw [←coe_nat_zsmul r, zsmul_mem_zmultiples_iff_exists_sub_div (int.coe_nat_ne_zero.mpr hn),
    int.cast_coe_nat],
  refl,
end

end add_subgroup

namespace quotient_add_group

lemma zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ add_subgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
  z • ψ = z • θ ↔ (∃ k : fin z.nat_abs, ψ = θ + (k : ℕ) • (p / z : R)) :=
begin
  induction ψ using quotient.induction_on',
  induction θ using quotient.induction_on',
  have : (quotient.mk' : R → R ⧸ add_subgroup.zmultiples p) = coe := rfl,
  simp only [this],
  simp_rw [←coe_zsmul, ←coe_nsmul, ←coe_add, quotient_add_group.eq_iff_sub_mem, ←smul_sub,
    ←sub_sub, add_subgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz],
end

lemma zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ add_subgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
  n • ψ = n • θ ↔ (∃ k : fin n, ψ = θ + (k : ℕ) • (p / n : R)) :=
begin
  simp_rw [←coe_nat_zsmul ψ, ←coe_nat_zsmul θ,
    zmultiples_zsmul_eq_zsmul_iff (int.coe_nat_ne_zero.mpr hz),  int.cast_coe_nat],
  refl,
end

end quotient_add_group

/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import group_theory.finiteness
import number_theory.number_field

import algebraic_geometry.EllipticCurve.torsion

/-!
# The Mordell-Weil theorem
-/

open_locale classical
noncomputable theory

variables {F : Type*} [field F]
variables (E : EllipticCurve F)
variables (K : Type*) [field K] [algebra F K]

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Reduction lemma -/

section reduction

variables (n : ℕ)

/-- `nE(F)` is a subgroup of `ιₚ⁻¹(nE(K))`. -/
lemma range_le_comap_range : (E⟮F⟯•n) ≤ add_subgroup.comap (ιₚ E F K) (E⟮K⟯•n) :=
begin
  intros P hP,
  cases hP with Q hQ,
  rw [← hQ],
  change ∃ R : E⟮K⟯, n • R = ιₚ E F K (n • Q),
  existsi ιₚ E F K Q,
  rw [map_nsmul]
end

/-- The kernel `Φ` of the cokernel map `E(F)/nE(F) → E(K)/nE(K)` induced by `ιₚ : E(F) ↪ E(K)`. -/
def Φ := (quotient_add_group.map _ _ _ $ range_le_comap_range E K n).ker

/-- If `[P] ∈ Φ`, then `ιₚ(P) ∈ nE(K)`. -/
lemma Φ_of_range (P : Φ E K n) : ιₚ E F K (quot.out P.val) ∈ (E⟮K⟯•n) :=
begin
  cases P with P hP,
  change (quotient_add_group.lift _ ((quotient_add_group.mk' _).comp _) _) P = 0 at hP,
  rw [← quot.out_eq P, quotient_add_group.lift_quot_mk, add_monoid_hom.coe_comp,
      quotient_add_group.coe_mk', quotient_add_group.eq_zero_iff] at hP,
  exact hP
end

/-- The map `δ : Φ → H¹(Gal(K/F), E(K)[n])` induced by the inflation-restriction exact sequence. -/
def δ [finite_dimensional F K] [is_galois F K] : Φ E K n → (K ≃ₐ[F] K) → (E⟮K⟯[n]) :=
λ P σ, ⟨σ • (Φ_of_range E K n P).some - (Φ_of_range E K n P).some,
begin
  change n • (σ • _ - _ : E⟮K⟯) = 0,
  rw [smul_sub, mul_by.map_smul],
  change σ • mul_by n E K _ - mul_by n E K _ = 0,
  rw [(Φ_of_range E K n P).some_spec, sub_eq_zero],
  apply point_gal.fixed.smul
end⟩

/-- `δ : Φ → H¹(Gal(K/F), E(K)[n])` is injective. -/
lemma δ.injective [finite_dimensional F K] [is_galois F K] : function.injective (δ E K n) :=
begin
  intros P₁_ P₂_ hP_,
  let P₁ := quot.out P₁_.val,
  let P₂ := quot.out P₂_.val,
  have hP₁ : ∃ Q₁ : E⟮K⟯, n • Q₁ = ιₚ E F K P₁ := Φ_of_range E K n P₁_,
  have hP₂ : ∃ Q₂ : E⟮K⟯, n • Q₂ = ιₚ E F K P₂ := Φ_of_range E K n P₂_,
  have hP : hP₁.some - hP₂.some ∈ (ιₚ E F K).range :=
  begin
    rw [function.funext_iff] at hP_,
    rw [← point_gal.fixed.eq],
    intro σ,
    rw [smul_sub, sub_eq_sub_iff_sub_eq_sub],
    injection hP_ σ,
  end,
  cases hP with Q hQ,
  apply_fun ((•) n) at hQ,
  rw [smul_sub, hP₁.some_spec, hP₂.some_spec] at hQ,
  rw [← P₁_.eta P₁_.property, ← P₂_.eta P₂_.property, subtype.mk_eq_mk, ← quotient.out_equiv_out],
  change ∃ S : E⟮F⟯, n • S = -P₁ + P₂,
  existsi -Q,
  apply_fun ιₚ E F K using point_hom.injective,
  rw [← neg_inj, ← map_neg, smul_neg, neg_neg, map_nsmul, ← map_neg, neg_add', neg_neg, map_sub],
  exact hQ
end

/-- For an exact sequence `0 → K → G → H`, if `K` and `H` are finite, then `G` is finite. -/
def ker_of_codom_of.fintype {G H : Type*} [add_comm_group G] [add_comm_group H] {f : G →+ H} :
  fintype f.ker → fintype H → fintype G :=
λ hK hH, @fintype.of_equiv _ _
  (@prod.fintype _ _ (@fintype.of_injective _ _ hH _ $ quotient_add_group.ker_lift_injective f) hK)
  add_subgroup.add_group_equiv_quotient_times_add_subgroup.symm

/-- If `E(K)/2E(K)` is finite, then `E(F)/2E(F)` is finite. -/
def coker_2_hom.fintype [char_zero K] [finite_dimensional F K] [is_galois F K] :
  fintype (E⟮K⟯/2) → fintype (E⟮F⟯/2) :=
ker_of_codom_of.fintype $ fintype.of_injective (δ E K 2) $ δ.injective E K 2

end reduction

----------------------------------------------------------------------------------------------------
/-! ## The weak Mordell-Weil theorem -/

section weak_mordell_weil

variables [number_field F]

/-- The weak Mordell-Weil theorem for `n = 2`: `E(F)/2E(F)` is finite. -/
instance : fintype (E⟮F⟯/2) := sorry

end weak_mordell_weil

----------------------------------------------------------------------------------------------------
/-! ## The Mordell-Weil theorem -/

section mordell_weil

variables [number_field F]

/-- The Mordell-Weil theorem: `E(F)` is finitely generated. -/
instance : add_group.fg (E⟮F⟯) := sorry

end mordell_weil

----------------------------------------------------------------------------------------------------

end EllipticCurve

/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import group_theory.finiteness
import number_theory.number_field

import algebraic_geometry.EllipticCurve.torsion

/-!
# The Mordell-Weil theorem for an elliptic curve over a number field
-/

noncomputable theory
open_locale classical

variables {F : Type*} [field F]
variables (E : EllipticCurve F)
variables (K : Type*) [field K] [algebra F K]

----------------------------------------------------------------------------------------------------
/-! ## Group theory -/

section group_theory

variables {G H : Type*} [add_comm_group G] [add_comm_group H]

/-- For an exact sequence `0 → K → G → H`, if `K` and `H` are finite, then `G` is finite. -/
def fintype.of_fintype_ker_codom {f : G →+ H} : fintype f.ker → fintype H → fintype G :=
λ hK hH, @fintype.of_equiv _ _
  (@prod.fintype _ _ (@fintype.of_injective _ _ hH _ $ quotient_add_group.ker_lift_injective f) hK)
  add_subgroup.add_group_equiv_quotient_times_add_subgroup.symm

local notation n`⬝`G := (distrib_mul_action.to_add_monoid_hom G n).range
local notation G/n := G ⧸ (n⬝G)

/-- If `G ≃ H`, then `G / nG ≃ H / nH`. -/
def quotient_add_group.quotient_equiv_of_equiv (n : ℕ) (hGH : G ≃+ H) : G/n ≃+ H/n :=
begin
  have ker_eq_range : (n⬝G) = ((quotient_add_group.mk' (n⬝H)).comp hGH.to_add_monoid_hom).ker :=
  begin
    ext g,
    change (∃ h : G, n • h = g) ↔ ↑(hGH.to_add_monoid_hom g) = (0 : H/n),
    rw [quotient_add_group.eq_zero_iff],
    change _ ↔ ∃ h : H, n • h = hGH.to_add_monoid_hom g,
    split,
    { intro hg,
      existsi [hGH.to_add_monoid_hom hg.some],
      rw [← map_nsmul, hg.some_spec] },
    { intro hg,
      existsi [hGH.symm.to_add_monoid_hom hg.some],
      rw [← map_nsmul, hg.some_spec],
      exact hGH.left_inv g }
  end,
  rw [ker_eq_range],
  apply quotient_add_group.quotient_ker_equiv_of_surjective,
  intro g,
  existsi [hGH.inv_fun $ quot.out g],
  change ↑(hGH.to_fun $ hGH.inv_fun $ quot.out g) = g,
  rw [hGH.right_inv],
  exact quot.out_eq g
end

end group_theory

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Reduction lemma -/

section reduction

variables (n : ℕ)

/-- `nE(F)` is a subgroup of `ιₚ⁻¹(nE(K))`. -/
lemma range_le_comap_range : (E⟮F⟯•n) ≤ add_subgroup.comap (ιₚ E F K) E⟮K⟯•n :=
begin
  rintro P ⟨Q, hQ⟩,
  rw [← hQ],
  change ∃ R : E⟮K⟯, n • R = ιₚ E F K (n • Q),
  existsi [ιₚ E F K Q],
  rw [map_nsmul]
end

/-- The kernel `Φ` of the cokernel map `E(F)/nE(F) → E(K)/nE(K)` induced by `ιₚ : E(F) ↪ E(K)`. -/
def Φ : add_subgroup E⟮F⟯/n := (quotient_add_group.map _ _ _ $ range_le_comap_range E K n).ker

/-- If `[P] ∈ Φ`, then `ιₚ(P) ∈ nE(K)`. -/
lemma Φ_mem_range (P : Φ E K n) : ιₚ E F K (quot.out P.val) ∈ E⟮K⟯•n :=
begin
  cases P with P hP,
  change (quotient_add_group.lift _ ((quotient_add_group.mk' _).comp _) _) P = 0 at hP,
  rw [← quot.out_eq P, quotient_add_group.lift_quot_mk, add_monoid_hom.coe_comp,
      quotient_add_group.coe_mk', quotient_add_group.eq_zero_iff] at hP,
  exact hP
end

/-- The map `δ : Φ → H¹(Gal(K/F), E(K)[n])` induced by the inflation-restriction exact sequence. -/
def δ [finite_dimensional F K] [is_galois F K] : Φ E K n → (K ≃ₐ[F] K) → E⟮K⟯[n] :=
λ P σ, ⟨σ • (Φ_mem_range E K n P).some - (Φ_mem_range E K n P).some,
begin
  change n • (σ • _ - _ : E⟮K⟯) = 0,
  rw [smul_sub, mul_by.map_smul],
  change σ • mul_by n E K _ - mul_by n E K _ = 0,
  rw [(Φ_mem_range E K n P).some_spec, sub_eq_zero],
  apply point_gal.fixed.smul
end⟩

/-- `δ` is injective. -/
lemma δ.injective [finite_dimensional F K] [is_galois F K] : function.injective $ δ E K n :=
begin
  intros P₁_ P₂_ hP_,
  let P₁ := quot.out P₁_.val,
  let P₂ := quot.out P₂_.val,
  have hP₁ : ∃ Q₁ : E⟮K⟯, n • Q₁ = ιₚ E F K P₁ := Φ_mem_range E K n P₁_,
  have hP₂ : ∃ Q₂ : E⟮K⟯, n • Q₂ = ιₚ E F K P₂ := Φ_mem_range E K n P₂_,
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
  existsi [-Q],
  apply_fun ιₚ E F K using point_hom.injective,
  rw [← neg_inj, ← map_neg, smul_neg, neg_neg, map_nsmul, ← map_neg, neg_add', neg_neg, map_sub],
  exact hQ
end

/-- If `E(K)/2E(K)` is finite, then `E(F)/2E(F)` is finite. -/
def fintype.of_coker_2_hom [invertible (2 : F)] [finite_dimensional F K] [is_galois F K] :
  fintype (E⟮K⟯/2) → fintype E⟮F⟯/2 :=
fintype.of_fintype_ker_codom $ fintype.of_injective (δ E K 2) (δ.injective E K 2)

end reduction

----------------------------------------------------------------------------------------------------
/-! ## The weak Mordell-Weil theorem -/

section weak_mordell_weil

variables [number_field F]

/-- `2` is invertible in a number field. -/
instance number_field.invertible_two : invertible (2 : F) := invertible_of_nonzero two_ne_zero'

/-- A splitting field of a number field is Galois. -/
instance number_field.splitting_field_is_galois : is_galois F F⟮E[2]⟯ := ⟨⟩

lemma fintype.of_covₘ_coker_2 : fintype E.covₘ⟮F⟮E[2]⟯⟯/2 := sorry

/-- The weak Mordell-Weil theorem for `n = 2`: `E(F)/2E(F)` is finite. -/
instance fintype.of_coker_2 : fintype E⟮F⟯/2 :=
fintype.of_coker_2_hom _ _ $ @fintype.of_equiv _ _ (fintype.of_covₘ_coker_2 E)
  (quotient_add_group.quotient_equiv_of_equiv 2 $ covₘ.equiv_add E F⟮E[2]⟯).to_equiv

end weak_mordell_weil

----------------------------------------------------------------------------------------------------
/-! ## The Mordell-Weil theorem -/

section mordell_weil

variables [number_field F]

/-- The Mordell-Weil theorem: `E(F)` is finitely generated. -/
instance : add_group.fg E⟮F⟯ := sorry

end mordell_weil

----------------------------------------------------------------------------------------------------

end EllipticCurve

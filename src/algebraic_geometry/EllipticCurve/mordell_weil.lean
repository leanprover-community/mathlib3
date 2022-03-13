/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.char_p.algebra
import group_theory.finiteness

import algebraic_geometry.EllipticCurve.kummer
import algebraic_geometry.EllipticCurve.torsion

/-!
# The Mordell-Weil theorem for an elliptic curve over a number field
-/

noncomputable theory
open_locale classical number_field

universe u

variables {F : Type u} [field F]
variables {E : EllipticCurve F}
variables {K : Type u} [field K] [algebra F K]

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Reduction lemma -/

section reduction

variables (n : ℕ)

/-- `nE(F)` is a subgroup of `ιₚ⁻¹(nE(K))`. -/
lemma range_le_comap_range : (E⟮F⟯⬝n) ≤ add_subgroup.comap ιₚ E⟮K⟯⬝n :=
by { rintro _ ⟨Q, hQ⟩, rw [← hQ], exact ⟨ιₚ Q, (map_nsmul ιₚ Q n).symm⟩ }

/-- The kernel `Φ` of the cokernel map `E(F)/nE(F) → E(K)/nE(K)` induced by `ιₚ : E(F) ↪ E(K)`. -/
def Φ (E : EllipticCurve F) (K : Type u) [field K] [algebra F K] : add_subgroup E⟮F⟯/n :=
(quotient_add_group.map _ _ _ $ @range_le_comap_range _ _ _ K _ _ n).ker

/-- If `[P] ∈ Φ`, then `ιₚ(P) ∈ nE(K)`. -/
lemma Φ_mem_range (P : Φ n E K) : ιₚ P.val.out' ∈ E⟮K⟯⬝n :=
begin
  cases P with P hP,
  change (quotient_add_group.lift _ ((quotient_add_group.mk' _).comp _) _) P = 0 at hP,
  rw [← quot.out_eq P, quotient_add_group.lift_quot_mk, add_monoid_hom.coe_comp,
      quotient_add_group.coe_mk', quotient_add_group.eq_zero_iff] at hP,
  exact hP
end

variables [finite_dimensional F K] [is_galois F K]

/-- The map `κ : Φ → H¹(Gal(K/F), E(K)[n])` induced by the inflation-restriction exact sequence. -/
def κ : Φ n E K → (K ≃ₐ[F] K) → E⟮K⟯[n] :=
λ P σ, ⟨σ • (Φ_mem_range n P).some - (Φ_mem_range n P).some,
begin
  change n • (σ • _ - _ : E⟮K⟯) = 0,
  rw [smul_sub, mul_by.map_smul],
  change σ • mul_by n _ - mul_by n _ = 0,
  rw [(Φ_mem_range n P).some_spec, sub_eq_zero],
  revert σ,
  change ιₚ P.val.out' ∈ E⟮K⟯^F,
  rw [point_gal.fixed.eq],
  exact ⟨P.val.out', rfl⟩
end⟩

/-- `κ` is injective. -/
lemma κ.injective : function.injective $ @κ _ _ E K _ _ n _ _ :=
begin
  intros P₁_ P₂_ hP_,
  let P₁ := P₁_.val.out',
  let P₂ := P₂_.val.out',
  have hP₁ : ∃ Q₁ : E⟮K⟯, n • Q₁ = ιₚ P₁ := Φ_mem_range n P₁_,
  have hP₂ : ∃ Q₂ : E⟮K⟯, n • Q₂ = ιₚ P₂ := Φ_mem_range n P₂_,
  have hP : hP₁.some - hP₂.some ∈ (ιₚ : E⟮F⟯ →+ E⟮K⟯).range :=
  begin
    rw [← point_gal.fixed.eq],
    intro σ,
    rw [smul_sub, sub_eq_sub_iff_sub_eq_sub],
    injection (congr_fun hP_) σ
  end,
  cases hP with Q hQ,
  apply_fun ((•) n) at hQ,
  rw [smul_sub, hP₁.some_spec, hP₂.some_spec] at hQ,
  rw [← P₁_.eta P₁_.property, ← P₂_.eta P₂_.property, subtype.mk_eq_mk, ← quotient.out_equiv_out],
  change ∃ S : E⟮F⟯, n • S = -P₁ + P₂,
  existsi [-Q],
  apply_fun (ιₚ : E⟮F⟯ →+ E⟮K⟯) using point_hom.injective,
  rw [← neg_inj, ← map_neg, smul_neg, neg_neg, map_nsmul, ← map_neg, neg_add', neg_neg, map_sub],
  exact hQ
end

/-- If `E(K)/2E(K)` is finite, then `E(F)/2E(F)` is finite. -/
def coker_2_of_fg_extension.fintype [invertible (2 : F)] : fintype (E⟮K⟯/2) → fintype E⟮F⟯/2 :=
add_group.fintype_of_ker_codom $ fintype.of_injective (κ 2) (κ.injective 2)

end reduction

----------------------------------------------------------------------------------------------------
/-! ## Complete 2-descent -/

section complete_2_descent

-- Note: requires minimality of Weierstrass equation
/-- The primes of a number field dividing `n` or at which `E` has bad reduction. -/
lemma bad_primes [number_field K] (n : ℕ) : finset $ maximal_spectrum $ 𝓞 K :=
@set.to_finset _ {p : maximal_spectrum $ 𝓞 K | (p.valuation ((F↑K)E.disc_unit) ≠ 1) ∨ (p.valuation ((ℤ↑K)n) < 1)}
begin
  sorry
end

variables [number_field F] [number_field K] [algebra F⟮E[2]⟯ K] [is_scalar_tower F F⟮E[2]⟯ K]

notation K⟮E; n⟯² := K⟮@bad_primes _ _ E _ _ _ infer_instance n, n⟯²

/-- `2` is invertible in a number field. -/
instance number_field.invertible_two : invertible (2 : F) := invertible_of_nonzero two_ne_zero'

variables (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0)
variables {a b c : K} (h3 : (cubic.map (F↑K) $ ψ₂_x E F).roots = {a, b, c})

include ha₁ ha₃ h3

local notation n`⬝`K := (zpow_group_hom n : Kˣ →* Kˣ).range

/-- The complete 2-descent function `δ : E(K) → Kˣ/(Kˣ)² × Kˣ/(Kˣ)²`. -/
def δ.to_fun : E⟮K⟯ → (Kˣ ⧸ (2⬝K)) × (Kˣ ⧸ (2⬝K))
| 0            := 1
| (some x y w) :=
if ha : x = a then
  (units.mk0 ((a - c) * (a - b)⁻¹) $ mul_ne_zero (sub_ne_zero.mpr (ψ₂_x.roots_ne h3).2.1) $
    inv_ne_zero $ sub_ne_zero.mpr (ψ₂_x.roots_ne h3).1,
  units.mk0 (a - b) $ sub_ne_zero.mpr (ψ₂_x.roots_ne h3).1)
else if hb : x = b then
  (units.mk0 (b - a) $ sub_ne_zero.mpr (ψ₂_x.roots_ne h3).1.symm,
  units.mk0 ((b - c) * (b - a)⁻¹) $ mul_ne_zero (sub_ne_zero.mpr (ψ₂_x.roots_ne h3).2.2) $
    inv_ne_zero $ sub_ne_zero.mpr (ψ₂_x.roots_ne h3).1.symm)
else
  (units.mk0 (x - a) $ sub_ne_zero.mpr ha, units.mk0 (x - b) $ sub_ne_zero.mpr hb)

omit ha₁ ha₃ h3

-- Input: explicit computation
/-- The complete 2-descent homomorphism `δ : E(K) → Kˣ/(Kˣ)² × Kˣ/(Kˣ)²`. -/
def δ : E⟮K⟯ →+ additive ((Kˣ ⧸ (2⬝K)) × (Kˣ ⧸ (2⬝K))) :=
{ to_fun    := δ.to_fun ha₁ ha₃ h3,
  map_zero' := rfl,
  map_add'  := sorry }

@[simp] lemma δ.map_zero : δ ha₁ ha₃ h3 (0 : E⟮K⟯) = 0 := (δ ha₁ ha₃ h3).map_zero'

@[simp] lemma δ.map_add (P Q : E⟮K⟯) : δ ha₁ ha₃ h3 (P + Q) = δ ha₁ ha₃ h3 P + δ ha₁ ha₃ h3 Q :=
(δ ha₁ ha₃ h3).map_add' P Q

-- Input: constructive proof for `ker δ = 2E(K)`
lemma δ.ker : (δ ha₁ ha₃ h3).ker = E⟮K⟯⬝2 :=
begin
  ext P,
  split,
  { intro hP,
    cases P with x y w,
    { exact ⟨0, rfl⟩ },
    { change δ.to_fun ha₁ ha₃ h3 _ = 1 at hP,
      simp only [δ.to_fun] at hP,
      split_ifs at hP,
      { sorry },
      { sorry },
      { sorry } } },
  { rintro ⟨Q, hQ⟩,
    rw [← hQ],
    change δ ha₁ ha₃ h3 (2 • Q) = 0,
    rw [map_nsmul],
    change ((δ ha₁ ha₃ h3 Q).1 ^ 2, (δ ha₁ ha₃ h3 Q).2 ^ 2) = 1,
    apply prod.ext,
    all_goals { rw [← quotient_group.out_eq' (δ ha₁ ha₃ h3 Q).1,
                    ← quotient_group.out_eq' (δ ha₁ ha₃ h3 Q).2],
                exact (quotient_group.eq_one_iff _).mpr ⟨quotient.out' _, rfl⟩ } }
end

-- Input: local analysis for `im δ ≤ K(E; 2) × K(E; 2)`
lemma δ.range_le : (δ ha₁ ha₃ h3).range ≤ K⟮E; 2⟯² :=
begin
  sorry
end

/-- The lift `δ' : E(K)/2E(K) → K(E; 2) × K(E; 2)` of `δ`. -/
def δ.lift : (E⟮K⟯/2) →+ K⟮E; 2⟯² :=
(add_subgroup.inclusion $ δ.range_le ha₁ ha₃ h3).comp $
  (quotient_add_group.range_ker_lift $ δ ha₁ ha₃ h3).comp $
  (quotient_add_group.equiv_quotient_of_eq $ δ.ker ha₁ ha₃ h3).symm.to_add_monoid_hom

lemma δ.lift.injective : function.injective $ @δ.lift _ _ _ K _ _ _ _ _ _ ha₁ ha₃ _ _ _ h3 :=
begin
  apply function.injective.comp,
  { intros x y hxy,
    rw [← set_like.coe_eq_coe, add_subgroup.coe_inclusion, add_subgroup.coe_inclusion,
        set_like.coe_eq_coe] at hxy,
    exact hxy },
  simp only,
  apply function.injective.comp,
  { exact quotient_add_group.range_ker_lift_injective (δ ha₁ ha₃ h3) },
  simp only,
  { intros x y hxy,
    rw [add_equiv.coe_to_add_monoid_hom, add_equiv.apply_eq_iff_eq] at hxy,
    exact hxy }
end

end complete_2_descent

----------------------------------------------------------------------------------------------------
/-! ## The weak Mordell-Weil theorem -/

section weak_mordell_weil

variables [number_field F]

/-- A splitting field of a number field has characteristic zero. -/
instance : char_zero F⟮E[2]⟯ := char_zero_of_injective_algebra_map (F↑F⟮E[2]⟯).injective

/-- A splitting field of a number field is a number field. -/
instance : number_field F⟮E[2]⟯ :=
@number_field.mk _ _ _ $ @finite_dimensional.trans _ F _ _ _ _ _ _
  (@algebra.to_module _ _ _ _ $ @algebra_rat F⟮E[2]⟯ _ _) (by convert is_scalar_tower.rat) _ _

/-- A splitting field of a number field is Galois. -/
instance : is_galois F F⟮E[2]⟯ := ⟨⟩

/-- The weak Mordell-Weil theorem for `n = 2` assuming `E[2] ⊂ E(F)`: `E(F)/2E(F)` is finite. -/
instance coker_2_of_rat_E₂.fintype (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0) : fintype E⟮F⟮E[2]⟯⟯/2 :=
fintype.of_injective _ $ δ.lift.injective ha₁ ha₃
  ((cubic.splits_iff_roots_eq_three $ ψ₂_x.a_ne_zero E F).mp $ ψ₂_x.splits F⟮E[2]⟯)
    .some_spec.some_spec.some_spec

/-- The weak Mordell-Weil theorem for `n = 2`: `E(F)/2E(F)` is finite. -/
instance : fintype E⟮F⟯/2 :=
begin
  apply @coker_2_of_fg_extension.fintype _ _ E F⟮E[2]⟯,
  apply @fintype.of_equiv _ _ (@coker_2_of_rat_E₂.fintype _ _ E.covₘ _ (covₘ.a₁ E) (covₘ.a₃ E)),
  apply (quotient_add_group.quotient_equiv_of_equiv _ 2).to_equiv,
  rw [← ψ₂_x.eq_covₘ],
  apply covₘ.equiv_add
end

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

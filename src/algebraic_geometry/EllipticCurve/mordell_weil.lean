/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.char_p.algebra
import group_theory.finiteness
import number_theory.number_field

import algebraic_geometry.EllipticCurve.torsion

-- Note: temporary
import algebraic_geometry.EllipticCurve.valuation

/-!
# The Mordell-Weil theorem for an elliptic curve over a number field
-/

noncomputable theory
open_locale classical

universe u

variables {F : Type u} [field F]
variables {E : EllipticCurve F}
variables {K : Type u} [field K] [algebra F K]

----------------------------------------------------------------------------------------------------
/-! ## Group theory -/

section group_theory

variables {G H : Type u} [add_comm_group G] [add_comm_group H]

/-- For an exact sequence `0 → K → G → H`, if `K` and `H` are finite, then `G` is finite. -/
def fintype.of_fintype_ker_codom {f : G →+ H} : fintype f.ker → fintype H → fintype G :=
λ hK hH, @fintype.of_equiv _ _
  (@prod.fintype _ _ (@fintype.of_injective _ _ hH _ $ quotient_add_group.ker_lift_injective f) hK)
  add_subgroup.add_group_equiv_quotient_times_add_subgroup.symm

local notation n`⬝`G := (zsmul_add_group_hom n : G →+ G).range

/-- If `G ≃ H`, then `G / nG ≃ H / nH`. -/
def quotient_add_group.quotient_equiv_of_equiv (n : ℤ) (hGH : G ≃+ H) : G ⧸ (n⬝G) ≃+ H ⧸ (n⬝H) :=
begin
  have ker_eq_range : (n⬝G) = ((quotient_add_group.mk' (n⬝H)).comp hGH.to_add_monoid_hom).ker :=
  begin
    ext g,
    change (∃ h : G, n • h = g) ↔ ↑(hGH.to_add_monoid_hom g) = (0 : H ⧸ (n⬝H)),
    rw [quotient_add_group.eq_zero_iff],
    change _ ↔ ∃ h : H, n • h = hGH.to_add_monoid_hom g,
    exact ⟨λ hg, ⟨hGH.to_add_monoid_hom hg.some, by rw [← map_zsmul, hg.some_spec]⟩,
           λ hg, ⟨hGH.symm.to_add_monoid_hom hg.some, by simpa only [← map_zsmul, hg.some_spec]
                                                         using hGH.left_inv g⟩⟩
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
lemma range_le_comap_range : (E⟮F⟯⬝n) ≤ add_subgroup.comap ιₚ E⟮K⟯⬝n :=
by { rintro P ⟨Q, hQ⟩, rw [← hQ], exact ⟨ιₚ Q, (map_nsmul ιₚ Q n).symm⟩ }

/-- The kernel `Φ` of the cokernel map `E(F)/nE(F) → E(K)/nE(K)` induced by `ιₚ : E(F) ↪ E(K)`. -/
def Φ (E : EllipticCurve F) (K : Type u) [field K] [algebra F K] : add_subgroup E⟮F⟯/n :=
(quotient_add_group.map _ _ _ $ @range_le_comap_range _ _ _ K _ _ n).ker

/-- If `[P] ∈ Φ`, then `ιₚ(P) ∈ nE(K)`. -/
lemma Φ_mem_range (P : Φ n E K) : ιₚ (quot.out P.val) ∈ E⟮K⟯⬝n :=
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
  change ιₚ (quot.out P.val) ∈ E⟮K⟯^F,
  rw [point_gal.fixed.eq],
  exact ⟨quot.out P.val, rfl⟩
end⟩

/-- `κ` is injective. -/
lemma κ.injective : function.injective $ @κ _ _ E K _ _ n _ _ :=
begin
  intros P₁_ P₂_ hP_,
  let P₁ := quot.out P₁_.val,
  let P₂ := quot.out P₂_.val,
  have hP₁ : ∃ Q₁ : E⟮K⟯, n • Q₁ = ιₚ P₁ := Φ_mem_range n P₁_,
  have hP₂ : ∃ Q₂ : E⟮K⟯, n • Q₂ = ιₚ P₂ := Φ_mem_range n P₂_,
  have hP : hP₁.some - hP₂.some ∈ (ιₚ : E⟮F⟯ →+ E⟮K⟯).range :=
  begin
    rw [function.funext_iff] at hP_,
    rw [← point_gal.fixed.eq],
    intro σ,
    rw [smul_sub, sub_eq_sub_iff_sub_eq_sub],
    injection hP_ σ
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
fintype.of_fintype_ker_codom $ fintype.of_injective (κ 2) (κ.injective 2)

end reduction

----------------------------------------------------------------------------------------------------
/-! ## The subgroup `K(S, n)` -/

section K_S_n

private def with_zero_units {α : Type u} [group α] : (with_zero α)ˣ ≃* α :=
{ to_fun    := λ x, (with_zero.ne_zero_iff_exists.mp x.ne_zero).some,
  inv_fun   := λ x,
  ⟨_, _, mul_inv_cancel $ @with_zero.coe_ne_zero _ x, inv_mul_cancel $ @with_zero.coe_ne_zero _ x⟩,
  left_inv  := λ x,
  by simp only [(with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec, units.mk_coe],
  right_inv := λ x,
  by { rw [← with_zero.coe_inj,
           (with_zero.ne_zero_iff_exists.mp (_ : (with_zero α)ˣ).ne_zero).some_spec],
       refl },
  map_mul'  := λ x y,
  by { rw [← with_zero.coe_inj, with_zero.coe_mul,
           (with_zero.ne_zero_iff_exists.mp (x * y).ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp x.ne_zero).some_spec,
           (with_zero.ne_zero_iff_exists.mp y.ne_zero).some_spec],
       refl } }

/-- The primes of a number field. -/
@[nolint has_inhabited_instance]
def primes (K : Type u) [field K] [number_field K] : Type u :=
maximal_spectrum $ number_field.ring_of_integers K

variables [number_field K] {S : finset $ primes K} {n : ℕ}

private def valuation_of_unit (p : primes K) : Kˣ →* multiplicative ℤ :=
with_zero_units.to_monoid_hom.comp $ units.map $ @maximal_spectrum.valuation _ _ _ _ K _ _ _ p

local notation n`⬝`K := (zpow_group_hom n : Kˣ →* Kˣ).range

private def coker_valuation_of_unit (p : primes K) :
  Kˣ ⧸ (n⬝K) →* ℤ ⧸ (zpow_group_hom n : multiplicative ℤ →* multiplicative ℤ).range :=
@quotient_group.map _ _ _ _ _ _ _ _ _ $
  by { rintro x ⟨y, hy⟩, rw [← hy], exact ⟨valuation_of_unit p y, (map_zpow _ y n).symm⟩ }

/-- The subgroup `K(S, n) = {b(Kˣ)ⁿ ∈ Kˣ/(Kˣ)ⁿ | ∀ p ∉ S, ord_p(b) ≡ 0 mod n}`. -/
def K_S_n : subgroup (Kˣ ⧸ (n⬝K)) :=
{ carrier  := {b : Kˣ ⧸ (n⬝K) | ∀ p ∉ S, coker_valuation_of_unit p b = 1},
  one_mem' := λ p _, by rw [map_one],
  mul_mem' := λ _ _ hx hy p hp, by rw [map_mul, hx p hp, hy p hp, one_mul],
  inv_mem' := λ _ hx p hp, by rw [map_inv, hx p hp, one_inv] }

notation K⟮S, n⟯ := @K_S_n K _ _ S n

-- Input: finiteness of ideal class group and finite generation of `S`-unit group
/-- `K(S, n)` is finite. -/
lemma K_S_n.fintype : fintype K⟮S, n⟯ :=
begin
  sorry
end

notation K⟮S, n⟯`²` := (K⟮S, n⟯.prod K⟮S, n⟯).to_add_subgroup

-- Note: redundant once `K_S_n.fintype` is an instance
lemma K_S_n.fintype' : fintype K⟮S, n⟯² :=
@fintype.of_equiv _ _ (@prod.fintype _ _ K_S_n.fintype K_S_n.fintype)
  (subgroup.prod_equiv K⟮S, n⟯ K⟮S, n⟯).symm.to_equiv

end K_S_n

----------------------------------------------------------------------------------------------------
/-! ## Complete 2-descent -/

section complete_2_descent

-- Input: reduction at a prime
/-- The primes of a number field dividing `n` or at which `E` has bad reduction. -/
def bad_primes [number_field K] (n : ℕ) : finset $ primes K :=
@set.to_finset _ {p : primes K | E = sorry} sorry

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

-- Input: constructive proof
/-- `ker δ = 2E(K)`. -/
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
                exact (quotient_group.eq_one_iff _).mpr ⟨quot.out _, rfl⟩ } }
end

-- Input: local analysis
/-- `im δ ≤ K(E; 2) × K(E; 2)`. -/
lemma δ.range_le : (quotient_add_group.ker_lift (δ ha₁ ha₃ h3 : E⟮K⟯ →+ _)).range ≤ K⟮E; 2⟯² :=
begin
  sorry
end

/-- The lift `δ' : E(K)/2E(K) → K(E; 2) × K(E; 2)` of `δ`. -/
def δ.lift : (E⟮K⟯/2) →+ K⟮E; 2⟯² :=
(add_subgroup.inclusion $ δ.range_le ha₁ ha₃ h3).comp $
  (quotient_add_group.ker_lift (δ ha₁ ha₃ h3 : E⟮K⟯ →+ _)).range_restrict.comp
  (quotient_add_group.equiv_quotient_of_eq $ δ.ker ha₁ ha₃ h3).symm.to_add_monoid_hom

/-- `δ'` is injective. -/
lemma δ.lift.injective : function.injective $ @δ.lift _ _ _ K _ _ _ _ _ _ ha₁ ha₃ _ _ _ h3 :=
begin
  apply function.injective.comp,
  { intros x y hxy,
    rw [← set_like.coe_eq_coe, add_subgroup.coe_inclusion, add_subgroup.coe_inclusion,
        set_like.coe_eq_coe] at hxy,
    exact hxy },
  simp only,
  apply function.injective.comp,
  { intros x y hxy,
    rw [← set_like.coe_eq_coe, add_monoid_hom.coe_range_restrict,
        add_monoid_hom.coe_range_restrict] at hxy,
    revert x y hxy,
    exact quotient_add_group.ker_lift_injective (δ ha₁ ha₃ h3) },
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
def coker_2_of_rat_E₂.fintype (ha₁ : E.a₁ = 0) (ha₃ : E.a₃ = 0) : fintype E⟮F⟮E[2]⟯⟯/2 :=
@fintype.of_injective _ _
  (@K_S_n.fintype' F⟮E[2]⟯ _ _ (@bad_primes _ _ E F⟮E[2]⟯ _ _ infer_instance 2) 2) _ $
  @δ.lift.injective _ _ E F⟮E[2]⟯ _ _ _ _ _ _ ha₁ ha₃ _ _ _ $
  ((cubic.splits_iff_roots_eq_three $ ψ₂_x.a_ne_zero E F).mp $ ψ₂_x.splits F⟮E[2]⟯)
    .some_spec.some_spec.some_spec

/-- The weak Mordell-Weil theorem for `n = 2`: `E(F)/2E(F)` is finite. -/
instance : fintype E⟮F⟯/2 :=
begin
  apply @coker_2_of_fg_extension.fintype _ _ E F⟮E[2]⟯,
  apply @fintype.of_equiv _ _ (@coker_2_of_rat_E₂.fintype _ _ E.covₘ _ (covₘ.a₁ E) (covₘ.a₃ E)),
  apply (quotient_add_group.quotient_equiv_of_equiv 2 _).to_equiv,
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

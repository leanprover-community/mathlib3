/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebra.cubic_discriminant

import algebraic_geometry.EllipticCurve.point

/-!
# Torsion points of an elliptic curve over a field
-/

noncomputable theory
open_locale classical

universe u

variables (n : ℕ)
variables {F : Type u} [field F]
variables {E : EllipticCurve F}
variables {K : Type u} [field K] [algebra F K]
variables {L : Type u} [field L] [algebra F L] [algebra K L] [is_scalar_tower F K L]

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Multiplication by `n` on `E(L)` -/

section multiplication

/-- The Galois-equivariant multiplication by `n` isogeny. -/
def mul_by' : E⟮L⟯ →+[L ≃ₐ[K] L] E⟮L⟯ :=
{ to_fun    := (•) n,
  map_smul' := λ _ _,
  begin
    induction n with n hn,
    { refl },
    { simp only [nat.succ_eq_add_one, add_smul, smul_add, one_smul, hn] }
  end,
  map_zero' := smul_zero n,
  map_add'  := smul_add n }

lemma mul_by.map_smul (σ : L ≃ₐ[K] L) (P : E⟮L⟯) : n • σ • P = σ • n • P :=
(mul_by' n).map_smul' σ P

/-- The multiplication by `n` isogeny. -/
def mul_by : E⟮K⟯ →+ E⟮K⟯ := (mul_by' n : E⟮K⟯ →+[K ≃ₐ[K] K] E⟮K⟯)

notation E⟮K⟯[n] := (mul_by n : E⟮K⟯ →+ E⟮K⟯).ker
notation E⟮K⟯`⬝`n := (mul_by n : E⟮K⟯ →+ E⟮K⟯).range
notation E⟮K⟯/n := E⟮K⟯ ⧸ E⟮K⟯⬝n

end multiplication

----------------------------------------------------------------------------------------------------
/-! ## Functoriality of `K ↦ E(K)[n]` -/

section functoriality

variables (φ : K →ₐ[F] L)

/-- The group homomorphism `E(K)[n] → E(L)[n]`. -/
def ker_hom : E⟮K⟯[n] →+ E⟮L⟯[n] :=
{ to_fun    := λ ⟨P, hP⟩, ⟨point_hom φ P,
  by { change n • P = 0 at hP, change n • _ = (0 : E⟮L⟯), simpa only [← map_nsmul, hP] }⟩,
  map_zero' := rfl,
  map_add'  := λ ⟨P, _⟩ ⟨Q, _⟩, subtype.mk_eq_mk.mpr $ map_add (point_hom φ) P Q }

@[simp] lemma ker_hom.id (P : E⟮K⟯[n]) : ker_hom n (K⟶[F]K) P = P := by rcases P with _ | _; refl

@[simp] lemma ker_hom.comp {M : Type u} [field M] [algebra F M] [algebra K M] [algebra L M]
  [is_scalar_tower F L M] [is_scalar_tower F K M] (P : E⟮K⟯[n]) :
  ker_hom n (L⟶[F]M) (ker_hom n (K⟶[F]L) P) = ker_hom n ((L⟶[F]M).comp (K⟶[F]L)) P :=
by rcases P with _ | _; refl

lemma ker_hom.injective : function.injective $ @ker_hom n _ _ E _ _ _ _ _ _ _ _ φ :=
λ ⟨_, _⟩ ⟨_, _⟩ hPQ, subtype.mk_eq_mk.mpr $ point_hom.injective φ $ subtype.mk_eq_mk.mp hPQ

/-- The canonical inclusion `E(K)[n] ↪ E(L)[n]`. -/
def ιₙ : E⟮K⟯[n] →+ E⟮L⟯[n] := ker_hom n $ K⟶[F]L

end functoriality

----------------------------------------------------------------------------------------------------
/-! ## Galois module structure of `E(L)[n]` -/

section galois

variables (σ τ : L ≃ₐ[K] L)

/-- The Galois action `Gal(L/K) ↷ E(L)[n]`. -/
def ker_gal : E⟮L⟯[n] → E⟮L⟯[n] := λ ⟨P, hP⟩,
⟨σ • P, by { change n • P = 0 at hP, change n • σ • P = 0, simpa only [mul_by.map_smul, hP] }⟩

/-- `Gal(L/K) ↷ E(L)[n]` is a scalar action. -/
instance : has_scalar (L ≃ₐ[K] L) E⟮L⟯[n] := ⟨ker_gal n⟩

/-- `Gal(L/K) ↷ E(L)[n]` is a multiplicative action. -/
instance : mul_action (L ≃ₐ[K] L) E⟮L⟯[n] :=
{ smul     := ker_gal n,
  one_smul := λ ⟨P, _⟩, subtype.mk_eq_mk.mpr $ one_smul (L ≃ₐ[K] L) P,
  mul_smul := λ σ τ ⟨P, _⟩, subtype.mk_eq_mk.mpr $ mul_smul σ τ P }

/-- The Galois invariant subgroup `E(L)[n]ᴷ` of `E(L)[n]` fixed by `Gal(L/K)`. -/
def ker_gal.fixed : add_subgroup E⟮L⟯[n] :=
{ carrier   := mul_action.fixed_points (L ≃ₐ[K] L) E⟮L⟯[n],
  zero_mem' := λ _, rfl,
  add_mem'  := λ P Q hP hQ σ,
  by { rcases ⟨P, Q⟩ with ⟨⟨_, _⟩, ⟨_, _⟩⟩,
       exact subtype.mk_eq_mk.mpr (point_gal.fixed.add_mem (λ τ, subtype.mk_eq_mk.mp $ hP τ)
                                                           (λ τ, subtype.mk_eq_mk.mp $ hQ τ) σ) },
  neg_mem'  := λ ⟨_, _⟩ hP σ,
  subtype.mk_eq_mk.mpr $ point_gal.fixed.neg_mem (λ τ, subtype.mk_eq_mk.mp $ hP τ) σ }

notation E⟮L⟯[n`]^`K := @ker_gal.fixed n _ _ E K _ _ L _ _ _ _

variables [finite_dimensional K L] [is_galois K L]

lemma ker_gal.fixed.eq : (E⟮L⟯[n]^K) = (ιₙ n : E⟮K⟯[n] →+ E⟮L⟯[n]).range :=
begin
  ext ⟨P, hP : n • P = 0⟩,
  change (∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, hP⟩) ↔ _,
  simp only,
  change P ∈ (E⟮L⟯^K) ↔ _,
  rw [point_gal.fixed.eq],
  split,
  { rintro ⟨Q, rfl⟩,
    exact ⟨⟨Q, by { rw [← map_nsmul] at hP, exact point_hom.injective (K⟶[F]L) hP }⟩, rfl⟩ },
  { exact λ ⟨⟨Q, _⟩, hQ⟩, ⟨Q, by injection hQ⟩ }
end

end galois

----------------------------------------------------------------------------------------------------
/-! ## The 2-torsion polynomial -/

section ψ₂_x

/-- The cubic polynomial `ψ₂(x)` of the `x`-coordinate in `E(K)[2]`. -/
def ψ₂_x (E : EllipticCurve F) (K : Type u) [field K] [algebra F K] : cubic K :=
⟨4, (F↑K)E.a₁ ^ 2 + 4 * (F↑K)E.a₂, 4 * (F↑K)E.a₄ + 2 * (F↑K)E.a₁ * (F↑K)E.a₃,
  (F↑K)E.a₃ ^ 2 + 4 * (F↑K)E.a₆⟩

notation F⟮E`[2]⟯` := (ψ₂_x E F).to_poly.splitting_field

lemma ψ₂_x.eq_map : ψ₂_x E K = cubic.map (F↑K) (ψ₂_x E F) :=
begin
  rw [ψ₂_x, cubic.map, ψ₂_x],
  simp only [map_add, map_mul, map_pow],
  simp only [map_one, map_bit0, map_bit1, algebra.id.map_eq_self],
  exact ⟨rfl, rfl, rfl, rfl⟩
end

lemma ψ₂_x.eq_cov (s t : F) : ψ₂_x E K = ψ₂_x (E.cov 1 0 s t) K :=
begin
  simp only [ψ₂_x, cov, units.inv],
  simp only [map_add, map_sub, map_mul, map_pow],
  simp only [map_zero, map_one, map_bit0, map_bit1],
  exact ⟨rfl, by ring1, by ring1, by ring1⟩
end

lemma ψ₂_x.disc_eq_disc : (ψ₂_x E K).disc = 4 * 4 * (F↑K)E.disc :=
begin
  rw [cubic.disc, ψ₂_x, disc, disc_aux],
  simp only [map_neg, map_add, map_sub, map_mul, map_pow],
  simp only [map_one, map_bit0, map_bit1],
  ring1
end

lemma ψ₂_x.splits (K : Type u) [field K] [algebra F K] [algebra F⟮E[2]⟯ K]
  [is_scalar_tower F F⟮E[2]⟯ K] : polynomial.splits (F↑K) (ψ₂_x E F).to_poly :=
begin
  convert polynomial.splits_comp_of_splits (F↑F⟮E[2]⟯) (F⟮E[2]⟯↑K)
    (polynomial.splitting_field.splits (ψ₂_x E F).to_poly),
  symmetry,
  exact ring_hom.ext (alg_hom.commutes $ (ψ₂_x E F).to_poly.splitting_field⟶[F]K)
end

variables [invertible (2 : F)]

private def invertible_two (K : Type u) [field K] [algebra F K] (h2 : invertible (2 : F)) :
  invertible (2 : K) :=
begin
  rw [← algebra.id.map_eq_self (2 : F)] at h2,
  replace h2 := @is_scalar_tower.invertible.algebra_tower _ _ K _ _ _ _ _ _ _ _ h2,
  rw [map_bit0, map_one] at h2,
  exact h2
end

private lemma two_ne_zero (K : Type u) [field K] [algebra F K] (h2 : invertible (2 : F)) :
  2 ≠ (0 : K) :=
@nonzero_of_invertible _ _ (2 : K) _ $ invertible_two K h2

private lemma four_ne_zero (K : Type u) [field K] [algebra F K] (h2 : invertible (2 : F)) :
  4 ≠ (0 : K) :=
begin
  convert_to 2 * 2 ≠ (0 : K),
  { norm_num1 },
  exact mul_ne_zero (two_ne_zero K h2) (two_ne_zero K h2)
end

lemma ψ₂_x.a_ne_zero (E : EllipticCurve F) (K : Type u) [field K] [algebra F K] :
  (ψ₂_x E K).a ≠ 0 :=
four_ne_zero K _inst_8

lemma ψ₂_x.eq_covₘ : ψ₂_x E K = ψ₂_x E.covₘ K := ψ₂_x.eq_cov (-⅟2 * E.a₁) (-⅟2 * E.a₃)

lemma ψ₂_x.mem_roots_iff (x : K) :
  x ∈ (ψ₂_x E K).roots ↔ ((F↑K)E.a₁ * x + (F↑K)E.a₃) ^ 2 +
                         4 * (x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆) = 0 :=
begin
  have rhs_rw : ∀ a₁ a₂ a₃ a₄ a₆ : K,
    (a₁ * x + a₃) ^ 2 + 4 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
      = 4 * x ^ 3 + (a₁ ^ 2 + 4 * a₂) * x ^ 2 + (4 * a₄ + 2 * a₁ * a₃) * x + (a₃ ^ 2 + 4 * a₆) :=
  by { intros, ring1 },
  rw [cubic.mem_roots_iff $ cubic.ne_zero_of_a_ne_zero $ ψ₂_x.a_ne_zero E K, ψ₂_x, rhs_rw]
end

lemma ψ₂_x.disc_ne_zero : (ψ₂_x E K).disc ≠ 0 :=
begin
  rw [ψ₂_x.disc_eq_disc],
  apply mul_ne_zero,
  apply mul_ne_zero,
  any_goals { exact four_ne_zero K _inst_8 },
  simpa only [ring_hom.map_ne_zero, disc, ← disc_unit_eq] using units.ne_zero E.disc_unit
end

lemma ψ₂_x.roots_ne {a b c : K} (h3 : (cubic.map (F↑K) $ ψ₂_x E F).roots = {a, b, c}) :
  a ≠ b ∧ a ≠ c ∧ b ≠ c :=
(cubic.disc_ne_zero_iff_roots_ne (ψ₂_x.a_ne_zero E F) h3).mp ψ₂_x.disc_ne_zero

end ψ₂_x

----------------------------------------------------------------------------------------------------
/-! ## Structure of `E(K)[2]` -/

section E₂

variables [invertible (2 : F)]

lemma E₂_y {x y w} : some x y w ∈ E⟮K⟯[2] ↔ y = 2⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃) :=
begin
  change 2 • some x y w = 0 ↔ _,
  rw [two_smul, add_eq_zero_iff_eq_neg, EllipticCurve.neg_some,
      eq_inv_mul_iff_mul_eq₀ $ two_ne_zero K _inst_8, two_mul, ← eq_neg_add_iff_add_eq,
      ← sub_eq_add_neg, sub_add_eq_sub_sub],
  simp only [true_and, eq_self_iff_true]
end

lemma E₂_x {x y w} : some x y w ∈ E⟮K⟯[2] ↔ x ∈ (ψ₂_x E K).roots :=
begin
  have lhs_rw : ∀ a₁ a₃ : K,
    (a₁ * x + a₃) ^ 2 + 4 * (y ^ 2 + a₁ * x * y + a₃ * y) = (2 * y + a₁ * x + a₃) ^ 2 :=
  by { intros, ring1 },
  rw [E₂_y, eq_inv_mul_iff_mul_eq₀ $ two_ne_zero K _inst_8, eq_neg_iff_add_eq_zero,
      ← add_semigroup.add_assoc, ψ₂_x.mem_roots_iff, ← w, lhs_rw, pow_eq_zero_iff two_pos],
  { refl },
  { exact is_domain.to_no_zero_divisors K }
end

/-- The projection map `E₂_to_ψ₂ : E(K)[2] → {0} ∪ ψ₂(x).roots`. -/
def E₂_to_ψ₂ : E⟮K⟯[2] → option ({x // x ∈ (ψ₂_x E K).roots})
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨x, E₂_x.mp h⟩

lemma E₂_to_ψ₂.injective : function.injective $ @E₂_to_ψ₂ _ _ E K _ _ _ :=
begin
  rintro ⟨_ | _, hP⟩ ⟨_ | _, hQ⟩ hPQ,
  any_goals { contradiction },
  { refl },
  { simp only [E₂_to_ψ₂] at hPQ,
    rw [E₂_y] at hP hQ,
    substs hP hQ hPQ }
end

/-- `E(K)[2]` is finite. -/
instance : fintype E⟮K⟯[2] := fintype.of_injective E₂_to_ψ₂ E₂_to_ψ₂.injective

theorem E₂.card_le_four : fintype.card E⟮K⟯[2] ≤ 4 :=
begin
  change fintype.card E⟮K⟯[2] ≤ 3 + 1,
  apply le_trans (fintype.card_le_of_injective E₂_to_ψ₂ E₂_to_ψ₂.injective),
  rw [fintype.card_option, add_le_add_iff_right,
      fintype.card_of_subtype (ψ₂_x E K).roots.to_finset (λ _, multiset.mem_to_finset)],
  { exact cubic.card_roots_le },
  { exact _inst_8 }
end

lemma E₂_to_ψ₂.surjective : function.surjective $ @E₂_to_ψ₂ _ _ E K _ _ _ :=
begin
  rintro (_ | ⟨x⟩),
  { exact ⟨⟨0, add_subgroup.zero_mem E⟮K⟯[2]⟩, rfl⟩ },
  { existsi [(⟨some x (2⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃)) _, E₂_y.mpr rfl⟩ : E⟮K⟯[2])],
    { rw [E₂_to_ψ₂, subtype.coe_eta] },
    convert_to 4⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃) ^ 2
               = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆,
    { have lhs_rw : ∀ a₁ a₃ t : K,
      (t * -(a₁ * x + a₃)) ^ 2 + a₁ * x * (t * -(a₁ * x + a₃)) + a₃ * (t * -(a₁ * x + a₃))
        = (1 - t) * t * -(a₁ * x + a₃) ^ 2 :=
      by { intros, ring1 },
      have half_sub_fourth : ((1 : K) - 2⁻¹) * 2⁻¹ = 4⁻¹ :=
      by { nth_rewrite 0 [← mul_inv_cancel $ two_ne_zero K _inst_8],
           rw [two_mul, add_sub_cancel, ← mul_inv], norm_num1 },
      rw [lhs_rw, half_sub_fourth] },
    rw [inv_mul_eq_iff_eq_mul₀ $ four_ne_zero K _inst_8, neg_eq_iff_add_eq_zero,
        ← ψ₂_x.mem_roots_iff],
    exact x.property }
end

lemma E₂_to_ψ₂.bijective : function.bijective $ @E₂_to_ψ₂ _ _ E K _ _ _ :=
⟨E₂_to_ψ₂.injective, E₂_to_ψ₂.surjective⟩

/-- `E(K)[2] ≃ {0} ∪ ψ₂(x).roots`. -/
def E₂_to_ψ₂.equiv : E⟮K⟯[2] ≃ option {x // x ∈ (ψ₂_x E K).roots} :=
equiv.of_bijective E₂_to_ψ₂ E₂_to_ψ₂.bijective

variables [algebra F⟮E[2]⟯ K] [is_scalar_tower F F⟮E[2]⟯ K]
variables [algebra F⟮E[2]⟯ L] [is_scalar_tower F F⟮E[2]⟯ L]

theorem E₂.card_eq_four : fintype.card E⟮K⟯[2] = 4 :=
begin
  let h3 := ((cubic.splits_iff_roots_eq_three $ ψ₂_x.a_ne_zero E F).mp $ ψ₂_x.splits K)
    .some_spec.some_spec.some_spec,
  change fintype.card E⟮K⟯[2] = 3 + 1,
  rw [fintype.card_congr E₂_to_ψ₂.equiv, fintype.card_option, add_left_inj,
      fintype.card_of_subtype (ψ₂_x E K).roots.to_finset $ λ _, multiset.mem_to_finset, ψ₂_x.eq_map,
      cubic.card_roots_of_disc_ne_zero (ψ₂_x.a_ne_zero E F) h3 ψ₂_x.disc_ne_zero],
  exact _inst_8
end

lemma E₂.hom.bijective : function.bijective $ @ιₙ 2 _ _ E K _ _ L _ _ _ _ :=
begin
  rw [fintype.bijective_iff_injective_and_card],
  exact ⟨ker_hom.injective 2 $ K⟶[F]L, by rw [E₂.card_eq_four, E₂.card_eq_four]⟩
end

/-- `E(K)[2] ≃ E(L)[2]`. -/
def E₂.hom.equiv : E⟮K⟯[2] ≃ E⟮L⟯[2] := equiv.of_bijective (ιₙ 2) E₂.hom.bijective

variables [finite_dimensional K L] [is_galois K L]

lemma E₂.gal.fixed.smul (σ : L ≃ₐ[K] L) (P : E⟮L⟯[2]) : σ • P = P :=
begin
  revert σ,
  change P ∈ E⟮L⟯[2]^K,
  rw [ker_gal.fixed.eq],
  exact ⟨E₂.hom.equiv.inv_fun P, function.surj_inv_eq E₂.hom.bijective.surjective P⟩
end

end E₂

----------------------------------------------------------------------------------------------------

end EllipticCurve

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

variables (n : ℕ)
variables {F : Type*} [field F]
variables (E : EllipticCurve F)
variables (K : Type*) [field K] [algebra F K]
variables (L : Type*) [field L] [algebra F L] [algebra K L] [is_scalar_tower F K L]

----------------------------------------------------------------------------------------------------

namespace EllipticCurve

open point

----------------------------------------------------------------------------------------------------
/-! ## Multiplication by `n` on `E(L)` -/

section multiplication

variables (σ : L ≃ₐ[K] L)

/-- Multiplication by `n` is Galois-equivariant. -/
lemma mul_by.map_smul (P : E⟮L⟯) : n • σ • P = σ • n • P :=
begin
  induction n with n h,
  { refl },
  { change (n + 1) • σ • P = σ • (n + 1) • P,
    simp only [add_smul, smul_add, one_smul, h] }
end

/-- Multiplication by `n` respects zero. -/
lemma mul_by.map_zero : n • (0 : E⟮L⟯) = 0 := smul_zero n

/-- Multiplication by `n` respects addition. -/
lemma mul_by.map_add (P Q : E⟮L⟯) : n • (P + Q) = n • P + n • Q := smul_add n P Q

/-- The Galois-equivariant multiplication by `n` isogeny. -/
def mul_by' : E⟮L⟯ →+[L ≃ₐ[K] L] E⟮L⟯ :=
{ to_fun    := (•) n,
  map_smul' := mul_by.map_smul n E K L,
  map_zero' := mul_by.map_zero n E L,
  map_add'  := mul_by.map_add n E L }

/-- The multiplication by `n` isogeny. -/
def mul_by : E⟮K⟯ →+ E⟮K⟯ := mul_by' n E K K

notation E⟮K⟯[n] := (mul_by n E K).ker
notation E⟮K⟯`⬝`n := (mul_by n E K).range
notation E⟮K⟯/n := E⟮K⟯ ⧸ E⟮K⟯⬝n

end multiplication

----------------------------------------------------------------------------------------------------
/-! ## Functoriality of `K ↦ E(K)[n]` -/

section functoriality

variables (φ : K →ₐ[F] L)

/-- Set function `E(K)[n] → E(L)[n]`. -/
def ker_hom.to_fun : E⟮K⟯[n] → E⟮L⟯[n] := λ ⟨P, hP⟩, ⟨point_hom E K L φ P,
by { change n • P = 0 at hP, change n • _ = (0 : E⟮L⟯), rw [← map_nsmul, hP], refl }⟩

/-- `E(K)[n] → E(L)[n]` respects zero. -/
lemma ker_hom.map_zero : ker_hom.to_fun n E K L φ 0 = 0 := rfl

/-- `E(K)[n] → E(L)[n]` respects addition. -/
lemma ker_hom.map_add (P Q : E⟮K⟯[n]) :
  ker_hom.to_fun n E K L φ (P + Q) = ker_hom.to_fun n E K L φ P + ker_hom.to_fun n E K L φ Q :=
begin
  rcases ⟨P, Q⟩ with ⟨⟨P, _⟩, ⟨Q, _⟩⟩,
  change (⟨_, _⟩ : E⟮L⟯[n]) = ⟨_ + _, _⟩,
  simp only,
  apply point_hom.map_add
end

/-- Group homomorphism `E(K)[n] → E(L)[n]`. -/
def ker_hom : E⟮K⟯[n] →+ E⟮L⟯[n] :=
{ to_fun    := ker_hom.to_fun n E K L φ,
  map_zero' := ker_hom.map_zero n E K L φ,
  map_add'  := ker_hom.map_add n E K L φ }

/-- `K ↦ E(K)[n]` respects identity. -/
lemma ker_hom.id (P : E⟮K⟯[n]) : ker_hom n E K K (K⟶[F]K) P = P :=
by rcases P with ⟨_ | _⟩; refl

/-- `K ↦ E(K)[n]` respects composition. -/
lemma ker_hom.comp (P : E⟮K⟯[n]) (M : Type*) [field M] [algebra F M] [algebra K M] [algebra L M]
  [is_scalar_tower F L M] [is_scalar_tower F K M] :
  ker_hom n E L M (L⟶[F]M) (ker_hom n E K L (K⟶[F]L) P)
    = ker_hom n E K M ((L⟶[F]M).comp (K⟶[F]L)) P :=
by rcases P with ⟨_ | _⟩; refl

/-- `E(K)[n] → E(L)[n]` is injective. -/
lemma ker_hom.injective : function.injective $ ker_hom n E K L φ :=
begin
  intros P Q hPQ,
  rcases ⟨P, Q⟩ with ⟨⟨P, _⟩, ⟨Q, _⟩⟩,
  change (⟨point_hom E K L φ P, _⟩ : E⟮L⟯[n]) = ⟨point_hom E K L φ Q, _⟩ at hPQ,
  simp only at hPQ,
  rw [subtype.mk_eq_mk],
  exact point_hom.injective E K L φ hPQ
end

/-- Canonical inclusion map `E(K)[n] ↪ E(L)[n]`. -/
def ιₙ : E⟮K⟯[n] →+ E⟮L⟯[n] := ker_hom n E K L $ K⟶[F]L

end functoriality

----------------------------------------------------------------------------------------------------
/-! ## Galois module structure of `E(L)[n]` -/

section galois

variables (σ τ : L ≃ₐ[K] L)

/-- The Galois action `Gal(L/K) ↷ E(L)[n]`. -/
def ker_gal : E⟮L⟯[n] → E⟮L⟯[n] := λ ⟨P, hP⟩, ⟨σ • P,
begin
  change n • P = 0 at hP,
  change n • σ • P = 0,
  rw [mul_by.map_smul, hP],
  refl
end⟩

/-- `Gal(L/K) ↷ E(L)[n]` is a scalar action. -/
instance : has_scalar (L ≃ₐ[K] L) E⟮L⟯[n] := ⟨ker_gal n E K L⟩

/-- `Gal(L/K) ↷ E(L)[n]` respects scalar one. -/
lemma ker_gal.one_smul (P : E⟮L⟯[n]) : (1 : L ≃ₐ[K] L) • P = P :=
begin
  cases P with P hP,
  change (⟨(1 : L ≃ₐ[K] L) • P, _⟩ : E⟮L⟯[n]) = ⟨P, hP⟩,
  simp only [point_gal.one_smul]
end

/-- `Gal(L/K) ↷ E(L)[n]` respects scalar multiplication. -/
lemma ker_gal.mul_smul (P : E⟮L⟯[n]) : (σ * τ) • P = σ • τ • P :=
begin
  cases P with P,
  change (⟨(σ * τ) • P, _⟩ : E⟮L⟯[n]) = ⟨σ • τ • P, _⟩,
  simp only [point_gal.mul_smul]
end

/-- `Gal(L/K) ↷ E(L)[n]` is a multiplicative action. -/
instance : mul_action (L ≃ₐ[K] L) E⟮L⟯[n] := ⟨ker_gal.one_smul n E K L, ker_gal.mul_smul n E K L⟩

local notation E⟮L⟯[n]^K := mul_action.fixed_points (L ≃ₐ[K] L) E⟮L⟯[n]

/-- Zero is in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.zero_mem : (0 : E⟮L⟯[n]) ∈ E⟮L⟯[n]^K := by { intro, refl }

/-- Addition is closed in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.add_mem (P Q : E⟮L⟯[n]) :
  P ∈ (E⟮L⟯[n]^K) → Q ∈ (E⟮L⟯[n]^K) → P + Q ∈ E⟮L⟯[n]^K :=
begin
  intros hP hQ σ,
  rcases ⟨P, Q⟩ with ⟨⟨P, _⟩, ⟨Q, _⟩⟩,
  change ∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, _⟩ at hP,
  change ∀ σ : L ≃ₐ[K] L, (⟨σ • Q, _⟩ : E⟮L⟯[n]) = ⟨Q, _⟩ at hQ,
  simp only at hP hQ,
  change (⟨σ • (P + Q), _⟩ : E⟮L⟯[n]) = ⟨P + Q, _⟩,
  simp only,
  rw [point_gal.fixed.add_mem E K L P Q hP hQ]
end

/-- Negation is closed in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.neg_mem (P : E⟮L⟯[n]) : P ∈ (E⟮L⟯[n]^K) → -P ∈ E⟮L⟯[n]^K :=
begin
  intros hP σ,
  cases P with P,
  change ∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, _⟩ at hP,
  simp only at hP,
  change (⟨σ • -P, _⟩ : E⟮L⟯[n]) = ⟨-P, _⟩,
  simp only,
  rw [point_gal.fixed.neg_mem E K L P hP]
end

/-- The Galois invariant subgroup `E(L)[n]ᴷ` of `E(L)[n]` fixed by `Gal(L/K)`. -/
def ker_gal.fixed : add_subgroup E⟮L⟯[n] :=
{ carrier   := E⟮L⟯[n]^K,
  zero_mem' := ker_gal.fixed.zero_mem n E K L,
  add_mem'  := ker_gal.fixed.add_mem n E K L,
  neg_mem'  := ker_gal.fixed.neg_mem n E K L }

notation E⟮L⟯[n`]^`K := ker_gal.fixed n E K L

/-- `E(L)[n]ᴷ = ιₚ(E(K)[n])`. -/
lemma ker_gal.fixed.eq [finite_dimensional K L] [is_galois K L] :
  (E⟮L⟯[n]^K) = (ιₙ n E K L).range :=
begin
  ext P,
  cases P with P hP,
  change n • P = 0 at hP,
  change (∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, hP⟩) ↔ _,
  simp only,
  change P ∈ point_gal.fixed E K L ↔ _,
  rw [point_gal.fixed.eq],
  split,
  { rintro ⟨Q, hQ⟩,
    existsi [(⟨Q, _⟩ : E⟮K⟯[n])],
    change (⟨ιₚ E K L Q, _⟩ : E⟮L⟯[n]) = _,
    simp only [hQ],
    rw [← hQ, ← map_nsmul] at hP,
    change n • Q = 0,
    apply_fun ιₚ E K L using point_hom.injective,
    rw [hP],
    refl },
  { rintro ⟨⟨Q⟩, hQ⟩,
    existsi [Q],
    injection hQ }
end

/-- `Gal(L/K)` fixes `ιₚ(E(K)[n])`. -/
lemma ker_gal.fixed.smul (P : E⟮K⟯[n]) [finite_dimensional K L] [is_galois K L] :
  σ • ιₙ n E K L P = ιₙ n E K L P :=
by { revert σ, change ιₙ n E K L P ∈ E⟮L⟯[n]^K, rw [ker_gal.fixed.eq], use P }

end galois

----------------------------------------------------------------------------------------------------
/-! ## The 2-torsion polynomial -/

section ψ₂_x

/-- The cubic polynomial `ψ₂(x)` of the `x`-coordinate in `E(K)[2]`. -/
def ψ₂_x : cubic K :=
⟨4, (F↑K)E.a₁ ^ 2 + 4 * (F↑K)E.a₂, 4 * (F↑K)E.a₄ + 2 * (F↑K)E.a₁ * (F↑K)E.a₃,
  (F↑K)E.a₃ ^ 2 + 4 * (F↑K)E.a₆⟩

notation F⟮E`[2]⟯` := (ψ₂_x E F).to_poly.splitting_field

/-- `ψ₂(x)` in `K` is equal to `ψ₂(x)` in `F` mapped across the embedding `F ↪ K`. -/
lemma ψ₂_x.eq_map : ψ₂_x E K = cubic.map (F↑K) (ψ₂_x E F) :=
begin
  rw [ψ₂_x, cubic.map, ψ₂_x],
  simp only [map_add, map_mul, map_pow],
  simp only [map_one, map_bit0, map_bit1, algebra.id.map_eq_self],
  exact ⟨rfl, rfl, rfl, rfl⟩
end

/-- `ψ₂(x)` is invariant under `(x, y) ↦ (x, y + sx + t)` for any `s, t ∈ R`. -/
lemma ψ₂_x.eq_cov (s t : F) : ψ₂_x E K = ψ₂_x (E.cov 1 0 s t) K :=
begin
  simp only [ψ₂_x, cov, units.inv],
  simp only [map_add, map_sub, map_mul, map_pow],
  simp only [map_zero, map_one, map_bit0, map_bit1],
  exact ⟨rfl, by ring1, by ring1, by ring1⟩
end

/-- The cubic discriminant of `ψ₂(x)` is sixteen times the discriminant of `E`. -/
lemma ψ₂_x.disc_eq_disc : (ψ₂_x E K).disc = 4 * 4 * (F↑K)E.disc :=
begin
  rw [cubic.disc, ψ₂_x, disc, disc_aux],
  simp only [map_neg, map_add, map_sub, map_mul, map_pow],
  simp only [map_one, map_bit0, map_bit1],
  ring1
end

/-- If `F(E[2]) ⊆ K`, then `ψ₂(x)` splits over `K`. -/
lemma ψ₂_x.splits [algebra F⟮E[2]⟯ K] [is_scalar_tower F F⟮E[2]⟯ K] :
  polynomial.splits (F↑K) (ψ₂_x E F).to_poly :=
begin
  convert polynomial.splits_comp_of_splits (F↑F⟮E[2]⟯) (F⟮E[2]⟯↑K)
    (polynomial.splitting_field.splits (ψ₂_x E F).to_poly),
  symmetry,
  exact ring_hom.ext (alg_hom.commutes $ (ψ₂_x E F).to_poly.splitting_field⟶[F]K)
end

variables [invertible (2 : F)]

/-- `2` is invertible in `K`. -/
private def invertible_two (h2 : invertible (2 : F)) : invertible (2 : K) :=
begin
  rw [← algebra.id.map_eq_self (2 : F)] at h2,
  replace h2 := @is_scalar_tower.invertible.algebra_tower _ _ K _ _ _ _ _ _ _ _ h2,
  rw [map_bit0, map_one] at h2,
  exact h2
end

/-- `2 ≠ 0` in `K`. -/
private lemma two_ne_zero (h2 : invertible (2 : F)) : 2 ≠ (0 : K) :=
@nonzero_of_invertible _ _ (2 : K) _ (invertible_two K h2)

/-- `4 ≠ 0` in `K`. -/
private lemma four_ne_zero (h2 : invertible (2 : F)) : 4 ≠ (0 : K) :=
begin
  convert_to 2 * 2 ≠ (0 : K),
  { norm_num1 },
  exact mul_ne_zero (two_ne_zero K h2) (two_ne_zero K h2)
end

/-- The leading coefficient of `ψ₂(x)` is not zero. -/
lemma ψ₂_x.a_ne_zero : (ψ₂_x E K).a ≠ 0 := four_ne_zero K _inst_8

/-- `ψ₂(x)` is invariant under completing a square. -/
lemma ψ₂_x.eq_covₘ : ψ₂_x E K = ψ₂_x E.covₘ K := ψ₂_x.eq_cov E K (-⅟2 * E.a₁) (-⅟2 * E.a₃)

/-- `α ∈ ψ₂(x).roots` iff `ψ₂(α) = 0`. -/
lemma ψ₂_x.mem_roots_iff (x : K) :
  x ∈ (ψ₂_x E K).roots ↔ ((F↑K)E.a₁ * x + (F↑K)E.a₃) ^ 2 +
                         4 * (x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆) = 0 :=
begin
  have rhs_rw : ∀ a₁ a₂ a₃ a₄ a₆ : K,
    (a₁ * x + a₃) ^ 2 + 4 * (x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
      = (a₃ ^ 2 + 4 * a₆) + (4 * a₄ + 2 * a₁ * a₃) * x + (a₁ ^ 2 + 4 * a₂) * x ^ 2 + 4 * x ^ 3 :=
  by { intros, ring1 },
  rw [cubic.mem_roots_iff $ cubic.ne_zero_of_a_ne_zero $ ψ₂_x.a_ne_zero E K, ψ₂_x, rhs_rw]
end

/-- The cubic discriminant of `ψ₂(x)` is not zero. -/
lemma ψ₂_x.disc_ne_zero : (ψ₂_x E K).disc ≠ 0 :=
begin
  rw [ψ₂_x.disc_eq_disc],
  apply mul_ne_zero,
  apply mul_ne_zero,
  any_goals { exact four_ne_zero K _inst_8 },
  rw [ring_hom.map_ne_zero, disc, ← disc_unit_eq],
  exact units.ne_zero E.disc_unit
end

/-- If `ψ₂(x)` has three roots over `K`, then they are distinct. -/
lemma ψ₂_x.roots_ne {x y z : K} (h3 : (cubic.map (F↑K) $ ψ₂_x E F).roots = {x, y, z}) :
  x ≠ y ∧ x ≠ z ∧ y ≠ z :=
(cubic.disc_ne_zero_iff_roots_ne (ψ₂_x.a_ne_zero E F) h3).mp $ ψ₂_x.disc_ne_zero E F

/-- If `F(E[2]) ⊆ K`, then `ψ₂(x)` has no duplicate roots over `K`. -/
lemma ψ₂_x.roots_nodup [algebra F⟮E[2]⟯ K] [is_scalar_tower F F⟮E[2]⟯ K] :
  (cubic.map (F↑K) $ ψ₂_x E F).roots.nodup :=
begin
  let h3 := (cubic.splits_iff_roots_eq_three $ ψ₂_x.a_ne_zero E F).mp (ψ₂_x.splits E K),
  rw [← cubic.disc_ne_zero_iff_roots_nodup (ψ₂_x.a_ne_zero E F) h3.some_spec.some_spec.some_spec],
  apply ψ₂_x.disc_ne_zero
end

end ψ₂_x

----------------------------------------------------------------------------------------------------
/-! ## Structure of `E(K)[2]` -/

section E₂

variables [invertible (2 : F)]

/-- The `y`-coordinate in `E(K)[2]`. -/
lemma E₂_y {x y w} : some x y w ∈ E⟮K⟯[2] ↔ y = 2⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃) :=
begin
  change 2 • some x y w = 0 ↔ _,
  rw [two_smul, add_eq_zero_iff_eq_neg, neg_some, eq_inv_mul_iff_mul_eq₀ $ two_ne_zero K _inst_8,
      two_mul, ← eq_neg_add_iff_add_eq, ← sub_eq_add_neg, sub_add_eq_sub_sub],
  simp only [true_and, eq_self_iff_true]
end

/-- The `x`-coordinate in `E(K)[2]`. -/
lemma E₂_x {x y w} : some x y w ∈ E⟮K⟯[2] ↔ x ∈ (ψ₂_x E K).roots :=
begin
  have lhs_rw : ∀ a₁ a₃ : K,
    (a₁ * x + a₃) ^ 2 + 4 * (y ^ 2 + a₁ * x * y + a₃ * y) = (2 * y + a₁ * x + a₃) ^ 2 :=
  by { intros, ring1 },
  rw [E₂_y, eq_inv_mul_iff_mul_eq₀ $ two_ne_zero K _inst_8, eq_neg_iff_add_eq_zero,
      ← add_semigroup.add_assoc, ψ₂_x.mem_roots_iff E K, ← w, lhs_rw, pow_eq_zero_iff],
  refl,
  exact dec_trivial
end

/-- The projection map `E₂_to_ψ₂ : E(K)[2] → {0} ∪ ψ₂(x).roots`. -/
def E₂_to_ψ₂ : E⟮K⟯[2] → option ({x // x ∈ (ψ₂_x E K).roots})
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨x, (E₂_x E K).mp h⟩

/-- `E₂_to_ψ₂` is injective. -/
lemma E₂_to_ψ₂.injective : function.injective $ E₂_to_ψ₂ E K :=
begin
  rintro ⟨⟨_ | _⟩, hP⟩ ⟨⟨_ | _⟩, hQ⟩ hPQ,
  any_goals { contradiction },
  { refl },
  { simp only [E₂_to_ψ₂] at hPQ,
    rw [E₂_y] at hP hQ,
    substs hP hQ hPQ }
end

/-- `E(K)[2]` is finite. -/
instance : fintype E⟮K⟯[2] := fintype.of_injective (E₂_to_ψ₂ E K) (E₂_to_ψ₂.injective E K)

/-- `#E(K)[2] ≤ 4`. -/
theorem E₂.card_le_four : fintype.card E⟮K⟯[2] ≤ 4 :=
begin
  change fintype.card E⟮K⟯[2] ≤ 3 + 1,
  apply le_trans (fintype.card_le_of_injective (E₂_to_ψ₂ E K) (E₂_to_ψ₂.injective E K)),
  rw [fintype.card_option, add_le_add_iff_right,
      fintype.card_of_subtype (ψ₂_x E K).roots.to_finset $ λ x, multiset.mem_to_finset],
  exact cubic.card_roots_le
end

/-- `E₂_to_ψ₂` is surjective. -/
lemma E₂_to_ψ₂.surjective : function.surjective $ E₂_to_ψ₂ E K :=
begin
  rintro (_ | ⟨x⟩),
  { existsi [(⟨0, by { change 2 • (0 : E⟮K⟯) = 0, refl }⟩ : E⟮K⟯[2])],
    refl },
  { existsi [(⟨some x (2⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃)) _, _⟩ : E⟮K⟯[2])],
    rw [E₂_to_ψ₂, subtype.coe_eta],
    convert_to 4⁻¹ * -((F↑K)E.a₁ * x + (F↑K)E.a₃) ^ 2
               = x ^ 3 + (F↑K)E.a₂ * x ^ 2 + (F↑K)E.a₄ * x + (F↑K)E.a₆,
    { have lhs_rw : ∀ a₁ a₃ t : K,
      (t * -(a₁ * x + a₃)) ^ 2 + a₁ * x * (t * -(a₁ * x + a₃)) + a₃ * (t * -(a₁ * x + a₃))
        = (1 - t) * t * -(a₁ * x + a₃) ^ 2 :=
      by { intros, ring1 },
      have half_sub_fourth : ((1 : K) - 2⁻¹) * 2⁻¹ = 4⁻¹ :=
      by { nth_rewrite 0 [← mul_inv_cancel $ two_ne_zero K _inst_8],
           rw [two_mul, add_sub_cancel, ← mul_inv₀], norm_num1 },
      rw [lhs_rw, half_sub_fourth] },
    rw [inv_mul_eq_iff_eq_mul₀ $ four_ne_zero K _inst_8, neg_eq_iff_add_eq_zero,
        ← ψ₂_x.mem_roots_iff],
    exact x.property,
    apply (E₂_y E K).mpr,
    refl }
end

/-- `E₂_to_ψ₂` is bijective. -/
lemma E₂_to_ψ₂.bijective : function.bijective $ E₂_to_ψ₂ E K :=
⟨E₂_to_ψ₂.injective E K, E₂_to_ψ₂.surjective E K⟩

/-- `E(K)[2] ≃ {0} ∪ ψ₂(x).roots`. -/
def E₂_to_ψ₂.equiv : E⟮K⟯[2] ≃ option {x // x ∈ (ψ₂_x E K).roots} :=
equiv.of_bijective (E₂_to_ψ₂ E K) (E₂_to_ψ₂.bijective E K)

variables [algebra F⟮E[2]⟯ K] [is_scalar_tower F F⟮E[2]⟯ K]
variables [algebra F⟮E[2]⟯ L] [is_scalar_tower F F⟮E[2]⟯ L]

/-- `#E(K)[2] = 4`. -/
theorem E₂.card_eq_four : fintype.card E⟮K⟯[2] = 4 :=
begin
  change fintype.card E⟮K⟯[2] = 3 + 1,
  rw [fintype.card_congr $ E₂_to_ψ₂.equiv E K, fintype.card_option, add_left_inj,
      fintype.card_of_subtype (ψ₂_x E K).roots.to_finset $ λ x, multiset.mem_to_finset, ψ₂_x.eq_map,
      cubic.card_roots_of_roots_nodup (ψ₂_x.a_ne_zero E F) (ψ₂_x.splits E K) (ψ₂_x.roots_nodup E K)]
end

/-- `E(K)[2] → E(L)[2]` is bijective. -/
lemma E₂.hom.bijective : function.bijective $ ιₙ 2 E K L :=
begin
  rw [fintype.bijective_iff_injective_and_card],
  split,
  { apply ker_hom.injective },
  { rw [E₂.card_eq_four, E₂.card_eq_four] }
end

/-- `E(K)[2] ≃ E(L)[2]`. -/
def E₂.hom.equiv : E⟮K⟯[2] ≃ E⟮L⟯[2] := equiv.of_bijective (ιₙ 2 E K L) (E₂.hom.bijective E K L)

/-- `Gal(L/K)` fixes `E(L)[2]`. -/
lemma E₂.gal.fixed.smul [finite_dimensional K L] [is_galois K L] (σ : L ≃ₐ[K] L) (P : E⟮L⟯[2]) :
  σ • P = P :=
begin
  revert σ,
  change P ∈ E⟮L⟯[2]^K,
  rw [ker_gal.fixed.eq],
  existsi [function.surj_inv (E₂.hom.bijective E K L).surjective P],
  apply function.surj_inv_eq
end

end E₂

----------------------------------------------------------------------------------------------------

end EllipticCurve

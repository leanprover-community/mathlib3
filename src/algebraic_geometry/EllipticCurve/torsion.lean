/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.EllipticCurve.point

/-!
# The torsion points of `E(K)`
-/

open_locale classical
noncomputable theory

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
def mul_by : E⟮K⟯ →+ (E⟮K⟯) := mul_by' n E K K

notation E⟮K⟯[n] := (mul_by n E K).ker
notation E⟮K⟯•n := (mul_by n E K).range
notation E⟮K⟯/n := E⟮K⟯ ⧸ (E⟮K⟯•n)

end multiplication

----------------------------------------------------------------------------------------------------
/-! ## Functoriality of `K ↦ E(K)[n]` -/

section functoriality

variables (φ : K →ₐ[F] L)

/-- Set function `E(K)[n] → E(L)[n]`. -/
def ker_hom.to_fun : E⟮K⟯[n] → (E⟮L⟯[n]) := λ ⟨P, hP⟩, ⟨point_hom E K L φ P,
by { change n • P = 0 at hP, change n • _ = (0 : E⟮L⟯), rw [← map_nsmul, hP], refl }⟩

/-- `E(K)[n] → E(L)[n]` respects zero. -/
lemma ker_hom.map_zero : ker_hom.to_fun n E K L φ 0 = 0 := rfl

/-- `E(K)[n] → E(L)[n]` respects addition. -/
lemma ker_hom.map_add (P Q : E⟮K⟯[n]) :
  ker_hom.to_fun n E K L φ (P + Q) = ker_hom.to_fun n E K L φ P + ker_hom.to_fun n E K L φ Q :=
begin
  cases P with P,
  cases Q with Q,
  change (⟨point_hom E K L φ (P + Q), _⟩ : E⟮L⟯[n]) = ⟨point_hom E K L φ P + point_hom E K L φ Q, _⟩,
  simp only,
  apply point_hom.map_add
end

/-- Group homomorphism `E(K)[n] → E(L)[n]`. -/
def ker_hom : E⟮K⟯[n] →+ (E⟮L⟯[n]) :=
{ to_fun    := ker_hom.to_fun n E K L φ,
  map_zero' := ker_hom.map_zero n E K L φ,
  map_add'  := ker_hom.map_add n E K L φ }

/-- `K ↦ E(K)[n]` respects identity. -/
lemma ker_hom.id (P : E⟮K⟯[n]) : ker_hom n E K K (K⟶[F]K) P = P :=
by { cases P with P, cases P; refl }

/-- `K ↦ E(K)[n]` respects composition. -/
lemma ker_hom.comp (P : E⟮K⟯[n]) (M : Type*) [field M] [algebra F M] [algebra K M] [algebra L M]
  [is_scalar_tower F L M] [is_scalar_tower F K M] :
  ker_hom n E L M (L⟶[F]M) (ker_hom n E K L (K⟶[F]L) P)
    = ker_hom n E K M ((L⟶[F]M).comp (K⟶[F]L)) P :=
by { cases P with P, cases P; refl }

/-- `E(K)[n] → E(L)[n]` is injective. -/
lemma ker_hom.injective : function.injective (ker_hom n E K L φ) :=
begin
  intros P Q hPQ,
  cases P with P,
  cases Q with Q,
  change (⟨point_hom E K L φ P, _⟩ : E⟮L⟯[n]) = ⟨point_hom E K L φ Q, _⟩ at hPQ,
  simp only at hPQ,
  rw [subtype.mk_eq_mk],
  exact point_hom.injective E K L φ hPQ
end

/-- Canonical inclusion map `E(K)[n] ↪ E(L)[n]`. -/
def ιₙ : E⟮K⟯[n] →+ (E⟮L⟯[n]) := ker_hom n E K L $ K⟶[F]L

end functoriality

----------------------------------------------------------------------------------------------------
/-! ## Galois module structure of `E(L)[n]` -/

section galois

variables (σ τ : L ≃ₐ[K] L)

/-- The Galois action `Gal(L/K) ↷ E(L)[n]`. -/
def ker_gal : E⟮L⟯[n] → (E⟮L⟯[n]) := λ ⟨P, hP⟩, ⟨σ • P,
begin
  change n • P = 0 at hP,
  change n • σ • P = 0,
  rw [mul_by.map_smul, hP],
  refl
end⟩

/-- `Gal(L/K) ↷ E(L)[n]` is a scalar action. -/
instance : has_scalar (L ≃ₐ[K] L) (E⟮L⟯[n]) := ⟨ker_gal n E K L⟩

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
instance : mul_action (L ≃ₐ[K] L) (E⟮L⟯[n]) :=
⟨ker_gal.one_smul n E K L, ker_gal.mul_smul n E K L⟩

local notation E⟮L⟯[n]^K := mul_action.fixed_points (L ≃ₐ[K] L) (E⟮L⟯[n])

/-- Zero is in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.zero_mem : (0 : E⟮L⟯[n]) ∈ (E⟮L⟯[n]^K) := by { intro, refl }

/-- Addition is closed in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.add_mem (P Q : E⟮L⟯[n]) :
  P ∈ (E⟮L⟯[n]^K) → Q ∈ (E⟮L⟯[n]^K) → P + Q ∈ (E⟮L⟯[n]^K) :=
begin
  intros hP hQ σ,
  cases P with P,
  cases Q with Q,
  change ∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, _⟩ at hP,
  change ∀ σ : L ≃ₐ[K] L, (⟨σ • Q, _⟩ : E⟮L⟯[n]) = ⟨Q, _⟩ at hQ,
  simp only at hP hQ,
  change (⟨σ • (P + Q), _⟩ : E⟮L⟯[n]) = ⟨P + Q, _⟩,
  simp only,
  rw [point_gal.fixed.add_mem E K L P Q hP hQ]
end

/-- Negation is closed in `E(L)[n]ᴷ`. -/
lemma ker_gal.fixed.neg_mem (P : E⟮L⟯[n]) : P ∈ (E⟮L⟯[n]^K) → -P ∈ (E⟮L⟯[n]^K) :=
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
def ker_gal.fixed : add_subgroup (E⟮L⟯[n]) :=
{ carrier   := E⟮L⟯[n]^K,
  zero_mem' := ker_gal.fixed.zero_mem n E K L,
  add_mem'  := ker_gal.fixed.add_mem n E K L,
  neg_mem'  := ker_gal.fixed.neg_mem n E K L }

notation E⟮L⟯[n`]^`K := ker_gal.fixed n E K L

/-- `E(L)[n]ᴷ = ιₚ(E(K)[n])`. -/
lemma ker_gal.fixed.eq [finite_dimensional K L] [is_galois K L] : (E⟮L⟯[n]^K) = (ιₙ n E K L).range :=
begin
  ext P,
  cases P with P hP,
  change n • P = 0 at hP,
  change (∀ σ : L ≃ₐ[K] L, (⟨σ • P, _⟩ : E⟮L⟯[n]) = ⟨P, hP⟩) ↔ _,
  simp only,
  change P ∈ point_gal.fixed E K L ↔ _,
  rw [point_gal.fixed.eq],
  split,
  { intro hP',
    cases hP' with Q hQ,
    existsi (⟨Q, _⟩ : E⟮K⟯[n]),
    change (⟨ιₚ E K L Q, _⟩ : E⟮L⟯[n]) = _,
    simp only [hQ],
    rw [← hQ, ← map_nsmul] at hP,
    change n • Q = 0,
    apply_fun ιₚ E K L using point_hom.injective,
    rw [hP],
    refl },
  { intro hP',
    cases hP' with Q hQ,
    cases Q with Q,
    existsi Q,
    injection hQ }
end

/-- `Gal(L/K)` fixes `ιₚ(E(K)[n])`. -/
lemma ker_gal.fixed.smul (P : E⟮K⟯[n]) [finite_dimensional K L] [is_galois K L] :
  σ • ιₙ n E K L P = ιₙ n E K L P :=
by { revert σ, change ιₙ n E K L P ∈ (E⟮L⟯[n]^K), rw [ker_gal.fixed.eq], use P }

end galois

----------------------------------------------------------------------------------------------------
/-! ## `E(K)[2]` is finite -/

section E₂_finite

variables [char_zero K]

open polynomial

/-- If `2 ≠ 0` in `K`, then `4 ≠ 0` in `K`. -/
lemma four_ne_zero : 4 ≠ (0 : K) :=
by { convert_to 2 * 2 ≠ (0 : K), { norm_num }, exact mul_ne_zero two_ne_zero' two_ne_zero' }

/-- The `y`-coordinate in `E(K)[2]`. -/
lemma E₂_y {x y w} : some x y w ∈ (E⟮K⟯[2]) ↔ y = -((F↑K)E.a1 * x + (F↑K)E.a3) / 2 :=
begin
  change 2 • some x y w = 0 ↔ _,
  rw [two_smul, add_eq_zero_iff_eq_neg, neg_some, eq_div_iff (two_ne_zero' : 2 ≠ (0 : K)), mul_two,
      ← eq_neg_add_iff_add_eq, ← sub_eq_add_neg, sub_add_eq_sub_sub],
  simp only [true_and, eq_self_iff_true]
end

/-- The polynomial `ψ₂(x)` of the `x`-coordinate in `E(K)[2]`. -/
def ψ₂_x : polynomial K :=
(C ((F↑K)E.a1) * X + C ((F↑K)E.a3)) ^ 2
+ C 4 * (X ^ 3 + C ((F↑K)E.a2) * X ^ 2 + C ((F↑K)E.a4) * X + C ((F↑K)E.a6))

/-- `ψ₂(x)` has degree three. -/
lemma ψ₂_x.degree_3 : degree (ψ₂_x E K) = ↑3 :=
begin
  rw [ψ₂_x],
  convert_to degree (C ((F↑K)E.a3 ^ 2 + (F↑K)E.a6 * 4)
                     + C ((F↑K)E.a1 * (F↑K)E.a3 * 2 + (F↑K)E.a4 * 4) * X
                     + C ((F↑K)E.a1 ^ 2 + (F↑K)E.a2 * 4) * X ^ 2
                     + C 4 * X ^ 3) = 3,
  { simp only [C_add, C_mul, mul_two, pow_two],
    ring },
  rw [degree_add_eq_right_of_degree_lt],
  { exact degree_C_mul_X_pow 3 (four_ne_zero K) },
  rw [degree_C_mul_X_pow 3 (four_ne_zero K)],
  apply lt_of_le_of_lt (degree_add_le _ _),
  rw [max_lt_iff],
  split,
  { apply lt_of_le_of_lt (degree_add_le _ _),
    rw [max_lt_iff],
    split,
    { apply lt_of_le_of_lt degree_C_le,
      exact dec_trivial },
    { apply lt_of_le_of_lt (degree_C_mul_X_le _),
      exact dec_trivial } },
  { apply lt_of_le_of_lt (degree_C_mul_X_pow_le 2 _),
    exact dec_trivial }
end

/-- `ψ₂(x)` is non-zero. -/
lemma ψ₂_x.ne_zero : ψ₂_x E K ≠ 0 :=
ne_zero_of_degree_gt (by { rw [ψ₂_x.degree_3, with_bot.coe_lt_coe], exact zero_lt_three })

/-- `α ∈ ψ₂(x).roots` iff `ψ₂(α) = 0`. -/
lemma ψ₂_x.roots_iff (x : K) :
  x ∈ (ψ₂_x E K).roots ↔ ((F↑K)E.a1 * x + (F↑K)E.a3) ^ 2 +
                         4 * (x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6) = 0 :=
begin
  rw [mem_roots (ψ₂_x.ne_zero E K), is_root, ψ₂_x],
  simp only [eval_C, eval_X, eval_add, eval_mul, eval_pow]
end

/-- The projection `E(K)[2] → {0} ∪ ψ₂(x).roots`. -/
def E₂_of_ψ₂ : E⟮K⟯[2] → option ({x // x ∈ (ψ₂_x E K).roots})
| ⟨0         , _⟩ := none
| ⟨some x y w, h⟩ := some ⟨x, by { rw [ψ₂_x.roots_iff, ← w, (E₂_y E K).mp h], ring }⟩

/-- `E(K)[2] → {0} ∪ ψ₂(x).roots` is injective. -/
lemma E₂_of_ψ₂.injective : function.injective (E₂_of_ψ₂ E K) :=
begin
  intros P Q hPQ,
  cases P with P hP,
  cases Q with Q hQ,
  cases P,
  { cases Q,
    { refl },
    { contradiction } },
  { cases Q,
    { contradiction },
    { simp only [E₂_of_ψ₂] at hPQ,
      rw [E₂_y] at hP hQ,
      substs hP hQ hPQ } }
end

/-- `E(K)[2]` is finite. -/
instance : fintype (E⟮K⟯[2]) := fintype.of_injective (E₂_of_ψ₂ E K) (E₂_of_ψ₂.injective E K)

/-- `E(K)[2] → {0} ∪ ψ₂(x).roots` is surjective. -/
lemma E₂_of_ψ₂.surjective : function.surjective (E₂_of_ψ₂ E K) :=
begin
  intro x,
  cases x,
  { existsi (⟨0, (by { change 2 • (0 : E⟮K⟯) = 0, refl })⟩ : E⟮K⟯[2]),
    refl },
  { existsi (⟨some x (-((F↑K)E.a1 * x + (F↑K)E.a3) / 2) _, _⟩ : E⟮K⟯[2]),
    rw [E₂_of_ψ₂, subtype.coe_eta],
    convert_to -((F↑K)E.a1 * x + (F↑K)E.a3) ^ 2 / 4
               = x ^ 3 + (F↑K)E.a2 * x ^ 2 + (F↑K)E.a4 * x + (F↑K)E.a6,
    { ring },
    rw [div_eq_iff (four_ne_zero K), mul_comm _ (4 : K), neg_eq_iff_add_eq_zero, ← ψ₂_x.roots_iff],
    exact x.property,
    apply (E₂_y E K).mpr,
    refl }
end

/-- `E(K)[2] → {0} ∪ ψ₂(x).roots` is bijective. -/
lemma E₂_of_ψ₂.bijective : function.bijective (E₂_of_ψ₂ E K) :=
⟨E₂_of_ψ₂.injective E K, E₂_of_ψ₂.surjective E K⟩

/-- `E(K)[2] ≃ {0} ∪ ψ₂(x).roots`. -/
def E₂_of_ψ₂.equiv : E⟮K⟯[2] ≃ option {x // x ∈ (ψ₂_x E K).roots} :=
equiv.of_bijective (E₂_of_ψ₂ E K) (E₂_of_ψ₂.bijective E K)

end E₂_finite

----------------------------------------------------------------------------------------------------

end EllipticCurve

import ring_theory.witt_vector.basic

namespace witt_vector

variables {p : ℕ} {R S σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
local attribute [-simp] coe_eval₂_hom

include hp
variables (p)

section sub_coeff

lemma sub_def (x y : 𝕎 R) : x - y =  λ n,
  aeval
    (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2)
      (aeval (λ m : unit × ℕ, (y.coeff m.2)) (witt_neg p bn.2)))
    (witt_add p n) :=
rfl

noncomputable def Sub : ℕ → mv_polynomial (bool × ℕ) ℤ :=
λ n, bind₁ (function.uncurry $ λ b, cond b
    (λ k, X (tt, k))
    (λ k, rename (λ un : unit × ℕ, (ff, un.2)) (witt_neg p k)))
  (witt_add p n)

lemma sub_eq (x y : 𝕎 R) (n : ℕ) :
  (x - y).coeff n =
  aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (y.coeff bn.2)) (Sub p n) :=
begin
  dsimp [Sub],
  show aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2)
    (aeval (λ m : unit × ℕ, (y.coeff m.2)) (witt_neg p bn.2))) (witt_add p n) = _,
  conv_rhs { rw [aeval_eq_eval₂_hom, hom_bind₁] },
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  ext ⟨⟨⟩, k⟩; dsimp [function.uncurry],
  { rw eval₂_hom_rename,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext ⟨⟨⟩, i⟩, refl },
  { rw eval₂_hom_X', refl, }
end

lemma Sub_eq : Sub p = witt_sub p :=
begin
  apply eq_witt_structure_int,
  intro n,
  erw [Sub, ← bind₁_bind₁, witt_structure_int_prop p (X tt + X ff) n, bind₁_bind₁],
  rw [alg_hom.map_add, alg_hom.map_sub, sub_eq_add_neg, ← alg_hom.map_neg],
  apply congr₂,
  { rw [bind₁_X_right, bind₁_X_right, bind₁_rename],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1 i,
    refl },
  { rw [← witt_structure_int_prop p (- X ff), bind₁_X_right, bind₁_rename],
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext1 i,
    dsimp [function.uncurry],
    rw witt_neg,
    apply mv_polynomial.map_injective (int.cast_ring_hom ℚ) int.cast_injective,
    simp only [map_rename, map_witt_structure_int, map_X, ring_hom.map_neg],
    simp only [witt_structure_rat, rename_bind₁, rename_rename,
      alg_hom.map_neg, ring_hom.map_neg, bind₁_X_right], }
end

lemma sub_coeff (x y : 𝕎 R) (n : ℕ) :
  (x - y).coeff n =
  aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (y.coeff bn.2)) (witt_sub p n) :=
by rw [← Sub_eq, sub_eq]

end sub_coeff

end witt_vector

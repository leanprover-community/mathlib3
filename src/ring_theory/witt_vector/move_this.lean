import ring_theory.witt_vector.basic
import ring_theory.witt_vector.nice_poly
import ring_theory.witt_vector.init_tail
import ring_theory.witt_vector.witt_vector_preps

namespace witt_vector

variables {p : ℕ} {R S σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

open mv_polynomial
local attribute [-simp] coe_eval₂_hom


include hp

variables (p)

lemma sub_def (x y : 𝕎 R) :
  x - y = λ n, aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (aeval (λ m : unit × ℕ, (y.coeff m.2)) (witt_neg p bn.2))) (witt_add p n) :=
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
  show aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (aeval (λ m : unit × ℕ, (y.coeff m.2)) (witt_neg p bn.2))) (witt_add p n) = _,
  conv_rhs { rw [aeval_eq_eval₂_hom, hom_bind₁] },
  apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
  ext ⟨⟨⟩, k⟩; dsimp [function.uncurry],
  { rw eval₂_hom_rename,
    apply eval₂_hom_congr (ring_hom.ext_int _ _) _ rfl,
    ext ⟨⟨⟩, i⟩,
    dsimp, refl },
  { rw eval₂_hom_X', dsimp, refl, }
end

lemma Sub_eq : Sub p = witt_sub p :=
begin
  apply unique_of_exists_unique (witt_structure_int_exists_unique p (X tt - X ff)),
  swap, { apply witt_structure_int_prop },
  sorry
end

lemma sub_coeff (x y : 𝕎 R) (n : ℕ) :
  (x - y).coeff n =
  aeval (λ bn : bool × ℕ, cond bn.1 (x.coeff bn.2) (y.coeff bn.2)) (witt_sub p n) :=
begin
  rw [← Sub_eq, sub_eq]
end

section disjoint

lemma witt_add_sub_nice (n : ℕ) :
  (witt_add p n - (X (tt, n) + X (ff, n))).nice :=
begin
  apply nice.of_map_of_injective (int.cast_ring_hom ℚ) (int.cast_injective),
  simp only [ring_hom.map_nat_cast, ring_hom.map_sub, ring_hom.map_add, map_X,
    ring_hom.map_pow, ring_hom.map_mul],
  rw [witt_add, map_witt_structure_int, ring_hom.map_add, map_X, map_X],
  rw [witt_structure_rat, X_in_terms_of_W_eq, alg_hom.map_mul, bind₁_C_right, alg_hom.map_sub,
    bind₁_X_right, alg_hom.map_add, bind₁_X_right, bind₁_X_right],
end

lemma coeff_add_of_disjoint (x y : 𝕎 R) (n : ℕ) (hn : ∀ i < n, x.coeff i = 0 ∨ y.coeff i = 0) :
  (x + y).coeff n = x.coeff n + y.coeff n :=
begin
  rw add_coeff,
  have : witt_add p n = (witt_add p n - (X (tt, n) + X (ff, n))) + (X (tt, n) + X (ff, n)),
  { simp only [sub_add_cancel] },
  rw [this, alg_hom.map_add, alg_hom.map_add, aeval_X, aeval_X], clear this,
  dsimp,
  convert zero_add _,
end

lemma init_tail_disjoint (x : 𝕎 R) (n : ℕ) (i : ℕ) :
  (init x n).coeff i = 0 ∨ (tail x n).coeff i = 0 :=
begin
  simp only [init, tail, coeff_mk],
  split_ifs; simp only [eq_self_iff_true, or_true, true_or]
end

lemma coeff_init_add_tail (x : 𝕎 R) (n : ℕ) (i : ℕ) :
  coeff i (init x n + tail x n) = coeff i (init x n) + coeff i (tail x n) :=
by { rw coeff_add_of_disjoint, intros, apply init_tail_disjoint }

lemma eq_init_add_tail (x : 𝕎 R) (n : ℕ) :
  x = init x n + tail x n :=
begin
  rw ext_iff,
  intro k,
  rw coeff_init_add_tail,
  simp only [init, tail, coeff_mk], split_ifs; simp only [add_zero, zero_add]
end


end disjoint

end witt_vector

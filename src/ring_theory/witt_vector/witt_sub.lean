import ring_theory.witt_vector.is_poly

/-!
# Subtraction of Witt vectors

In Lean, subtraction in a ring is by definition equal to `x + -y`.
For Witt vectors, this means that subtraction is not defined in terms of
the polynomials `witt_sub p`.

We then show by a computation that evaluating `witt_sub p` on the coefficients of `x` and `y`
gives the coefficients of `x - y`.
-/

namespace witt_vector

variables {p : ℕ} {R S σ idx : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]

local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector

open mv_polynomial
local attribute [-simp] coe_eval₂_hom

include hp
variables (p)

lemma sub_eq (x y : 𝕎 R) :
  x - y = eval (witt_sub p) ![x, y] :=
begin
  apply is_poly₂.ext ((add_is_poly₂).comp_right (neg_is_poly)) ⟨witt_sub p, by intros; refl⟩ _ _ x y,
  unfreezingI { clear_dependent R }, introsI R _Rcr x y n,
  simp only [←sub_eq_add_neg, ring_hom.map_sub],
  symmetry,
  have := witt_structure_int_prop p (X 0 - X 1 : mv_polynomial (fin 2) ℤ) n,
  apply_fun (aeval (function.uncurry ![x.coeff, y.coeff])) at this,
  simp only [aeval_bind₁, alg_hom.map_sub, bind₁_X_right] at this,
  simp only [aeval_eq_eval₂_hom, eval₂_hom_rename] at this,
  exact this,
end

lemma sub_coeff (x y : 𝕎 R) (n : ℕ) :
  (x - y).coeff n = peval (witt_sub p n) ![x.coeff, y.coeff] :=
by { rw [sub_eq], refl }

end witt_vector

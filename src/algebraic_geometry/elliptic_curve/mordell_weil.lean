/-
Copyright (c) 2021 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import algebraic_geometry.elliptic_curve.group_law
import data.polynomial
import field_theory.galois
import group_theory.finiteness
import number_theory.number_field

/-!
# The Mordell-Weil theorem
-/

open_locale classical
noncomputable theory

namespace EllipticCurve

-- let `K` be a number field
variables {K : Type*} [field K] [number_field K]
-- let `E` be an elliptic curve over `K`
variables (E : EllipticCurve K)
-- let `L` be a finite Galois extension of `K`
variables (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [is_galois K L]
-- TODO: unnecessary
variables [nontrivial L] [number_field L]

open point polynomial

/-- The multiplication by `n` isogeny. -/
def mul_by_n (n : ℕ) : E{L} →+ E{L} := distrib_mul_action.to_add_monoid_hom (E{L}) n

-- kernel of multiplication by `n`
notation E{L}[n] := add_monoid_hom.ker $ mul_by_n E L n

-- cokernel of multiplication by `n`
notation E{L}/n := E{L} ⧸ (add_monoid_hom.range $ mul_by_n E L n)

----------------------------------------------------------------------------------------------------
/-!
## `E(L)[2]` is finite
-/
----------------------------------------------------------------------------------------------------

/-- The `y`-coordinate in `E(L)[2]`. -/
lemma tor_2_y {x y w} (h : some x y w ∈ E{L}[2]) : y = -((K↑L)E.a1 * x + (K↑L)E.a3) / 2 :=
begin
  rw [eq_div_iff (two_ne_zero' : 2 ≠ (0 : L)), mul_two],
  rw [← eq_neg_add_iff_add_eq, ← sub_eq_add_neg, sub_add_eq_sub_sub],
  change 2 • some _ _ _ = 0 at h,
  rw [two_smul, add_eq_zero_iff_eq_neg, neg_some] at h,
  injection h,
end

/-- The polynomial `ψ_2` of the `x`-coordinate in `E(L)[2]`. -/
def ψ_2_x : polynomial L :=
(C ((K↑L)E.a1 / 2) * X + C ((K↑L)E.a3 / 2)) ^ 2
+ (X ^ 3 + C ((K↑L)E.a2) * X ^ 2 + C ((K↑L)E.a4) * X + C ((K↑L)E.a6))

/-- `ψ_2_x` has degree three. -/
lemma ψ_2_x.degree : degree (ψ_2_x E L) = ↑3 :=
begin
  rw [ψ_2_x],
  convert_to (degree (C (((K↑L)E.a3 / 2) ^ 2 + (K↑L)E.a6)
                      + C (((K↑L)E.a1 / 2) * ((K↑L)E.a3 / 2) * 2 + (K↑L)E.a4) * X
                      + C (((K↑L)E.a1 / 2) ^ 2 + (K↑L)E.a2) * X ^ 2
                      + X ^ 3) = 3),
  { simp only [C_add, C_mul, mul_two, pow_two],
    ring },
  rw [degree_add_eq_right_of_degree_lt],
  { exact degree_X_pow 3 },
  rw [degree_X_pow 3],
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
    exact dec_trivial },
  assumption,
end

/-- The function from `E(L)[2]` to the roots of `ψ_2_x`. -/
def tor_2_to_ψ_2_x : E{L}[2] → option ({x // x ∈ roots (ψ_2_x E L)})
  | ⟨0         , _ ⟩ := none
  | ⟨some x y w, hP⟩ := some ⟨x,
    begin
      rw [mem_roots, is_root, ψ_2_x],
      simp,
      simp only [tor_2_y E L hP] at w,
      rw [← w],
      ring,
      exact ne_zero_of_degree_gt (by rw [ψ_2_x.degree E L, with_bot.coe_lt_coe];
                                     exact zero_lt_three)
    end⟩

/-- The function from `E(L)[2]` to the roots of `ψ_2_x` is injective. -/
lemma tor_2_to_ψ_2_x.injective : function.injective (tor_2_to_ψ_2_x E L) :=
begin
  intros P₁ P₂,
  intro hP,
  cases P₁ with P₁ hP₁,
  cases P₂ with P₂ hP₂,
  cases P₁,
  { cases P₂,
    { refl },
    { contradiction }, },
  { cases P₂,
    { contradiction },
    { simp only [tor_2_y E L hP₁, tor_2_y E L hP₂],
      simp only [tor_2_to_ψ_2_x] at hP,
      subst hP } }
end

/-- `E(L)[2]` is finite. -/
instance tor_2.fintype : fintype (E{L}[2]) :=
fintype.of_injective (tor_2_to_ψ_2_x E L) (tor_2_to_ψ_2_x.injective E L)

----------------------------------------------------------------------------------------------------
/-!
## The Mordell-Weil theorem
-/
----------------------------------------------------------------------------------------------------

/-- The weak Mordell-Weil theorem: `E(K)/nE(K)` is finite. -/
instance (n : ℕ) [fact (0 < n)] : fintype (E{K}/n) := sorry

/-- The Mordell-Weil theorem: `E(K)` is finitely generated. -/
instance : add_group.fg (E{K}) := sorry

end EllipticCurve

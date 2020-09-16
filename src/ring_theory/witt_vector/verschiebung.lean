/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/

import ring_theory.witt_vector.basic
import ring_theory.witt_vector.is_poly


/-! ## The Verschiebung operator -/

namespace witt_vector
open mv_polynomial

variables {p : ℕ} {R S : Type*} [hp : fact p.prime] [comm_ring R] [comm_ring S]
local notation `𝕎` := witt_vector p -- type as `\bbW`

local attribute [semireducible] witt_vector
local attribute [instance] mv_polynomial.invertible_rat_coe_nat

noncomputable theory

/--
`verschiebung_fun x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung_fun x).coeff (i + 1)`.

`verschiebung_fun` is the underlying function of the additive monoid hom `witt_vector.verschiebung`.
-/
def verschiebung_fun (x : 𝕎 R) : 𝕎 R :=
mk p $ λ n, if n = 0 then 0 else x.coeff (n - 1)

lemma verschiebung_fun_coeff (x : 𝕎 R) (n : ℕ) :
  (verschiebung_fun x).coeff n = if n = 0 then 0 else x.coeff (n - 1) :=
by rw [verschiebung_fun, coeff_mk]

lemma verschiebung_fun_coeff_zero (x : 𝕎 R) :
  (verschiebung_fun x).coeff 0 = 0 :=
by rw [verschiebung_fun_coeff, if_pos rfl]

@[simp] lemma verschiebung_fun_coeff_succ (x : 𝕎 R) (n : ℕ) :
  (verschiebung_fun x).coeff n.succ = x.coeff n := rfl

/--
The 0th Verschiebung polynomial is 0. For `n > 0`, the `n`th Verschiebung polynomial is the
variable `X (n-1)`.
-/
def verschiebung_poly (n : ℕ) : mv_polynomial ℕ ℤ :=
if n = 0 then 0 else X (n-1)

@[simp] lemma verschiebung_poly_zero :
  verschiebung_poly 0 = 0 := rfl

include hp
lemma bind₁_verschiebung_poly_witt_polynomial (n : ℕ) :
  bind₁ verschiebung_poly (witt_polynomial p ℤ n) =
  if n = 0 then 0 else p * witt_polynomial p ℤ (n-1) :=
begin
  have aux : ∀ k : ℕ, p ^ k ≠ 0,
  { intro k, apply pow_ne_zero _ hp.ne_zero, },
  split_ifs with hn,
  { rw [hn, witt_polynomial_zero, bind₁_X_right, verschiebung_poly, if_pos rfl] },
  { obtain ⟨n, rfl⟩ := nat.exists_eq_succ_of_ne_zero hn,
    rw [nat.succ_eq_add_one, nat.add_sub_cancel],
    dsimp [witt_polynomial],
    rw [alg_hom.map_sum, finset.sum_range_succ', finset.mul_sum],
    rw [bind₁_monomial],
    simp only [finsupp.support_single_ne_zero, aux, add_zero, finset.prod_singleton,
      nat.succ_sub_succ_eq_sub, finsupp.single_eq_same, verschiebung_poly_zero, ne.def,
      nat.sub_zero, not_false_iff, int.nat_cast_eq_coe_nat, C_1, mul_zero, pow_zero, zero_pow'],
    apply finset.sum_congr rfl,
    intros i hi,
    rw bind₁_monomial,
    simp only [finsupp.support_single_ne_zero, aux, int.cast_coe_nat, finset.prod_singleton,
      ring_hom.eq_int_cast, finsupp.single_eq_same, C_pow, ne.def, not_false_iff],
    rw [verschiebung_poly],
    simp only [monomial_eq, finsupp.prod_single_index, int.cast_coe_nat, nat.add_succ_sub_one,
      add_zero, ring_hom.eq_int_cast, C_pow, eq_self_iff_true, add_eq_zero_iff, if_false,
      one_ne_zero, pow_zero, and_false],
    ring_exp, }
end

variable (p)
omit hp

/--
`witt_vector.verschiebung` has polynomial structure given by `witt_vector.verschiebung_poly`.
-/
@[simps { fully_applied := ff }]
def verschiebung_fun_is_poly : is_poly p (λ R _Rcr, @verschiebung_fun p R _Rcr) :=
{ poly := verschiebung_poly,
  coeff :=
  begin
    rintro R _Rcr x, resetI,
    funext n, cases n,
    { simp only [verschiebung_poly, verschiebung_fun_coeff_zero, if_pos rfl, alg_hom.map_zero] },
    { rw [verschiebung_poly, verschiebung_fun_coeff_succ, if_neg (n.succ_ne_zero),
          aeval_X, nat.succ_eq_add_one, nat.add_sub_cancel], }
  end }

variable {p}
include hp

/--
`verschiebung x` shifts the coefficients of `x` up by one, by inserting 0 as the 0th coefficient.
`x.coeff i` then becomes `(verchiebung x).coeff (i + 1)`.

This is a additive monoid hom with underlying function `verschiebung_fun`.
-/
noncomputable
def verschiebung : 𝕎 R →+ 𝕎 R :=
{ to_fun := verschiebung_fun,
  map_zero' :=
  by ext ⟨⟩; rw [verschiebung_fun_coeff]; simp only [if_true, eq_self_iff_true, zero_coeff, if_t_t],
  map_add' :=
  begin
    apply is_poly₂.ext'
      ((verschiebung_fun_is_poly p).comp₂ (add_is_poly₂ p))
      ((add_is_poly₂ p).comp (verschiebung_fun_is_poly p) (verschiebung_fun_is_poly p)),
    intro n,
    by_cases hn : n = 0;
    simp only [hn, is_poly.comp₂_poly, verschiebung_fun_is_poly_poly, add_is_poly₂_poly, is_poly₂.comp_poly,
      ← bind₁_bind₁, bind₁_verschiebung_poly_witt_polynomial, witt_add, witt_structure_int_prop,
      alg_hom.map_add, bind₁_X_right, function.uncurry, bind₁_rename, function.comp,
      matrix.head_cons, matrix.cons_val_one, matrix.cons_val_zero, ← rename_bind₁,
      add_zero, if_true, ring_hom.map_zero, eq_self_iff_true, alg_hom.map_zero,
      ring_hom.map_nat_cast, alg_hom.map_nat_cast, if_false, ring_hom.map_mul, alg_hom.map_mul, mul_add],
  end }

omit hp

/--
`witt_vector.verschiebung` has polynomial structure given by `witt_vector.verschiebung_poly`.
-/
@[simps { fully_applied := ff }]
def verschiebung_is_poly : is_poly p (λ R _Rcr, @verschiebung p R hp _Rcr) :=
{ poly := verschiebung_poly,
  coeff := (verschiebung_fun_is_poly p).coeff }

include hp

/-- verschiebung is a natural transformation -/
@[simp] lemma map_verschiebung (f : R →+* S) (x : 𝕎 R) :
  map f (verschiebung x) = verschiebung (map f x) :=
by { ext ⟨-, -⟩, exact f.map_zero, refl }

omit hp
@[simp] lemma ghost_component_zero_verschiebung (x : 𝕎 R) :
  ghost_component 0 (verschiebung_fun x) = 0 :=
by rw [ghost_component_apply, aeval_witt_polynomial, finset.range_one, finset.sum_singleton,
       verschiebung_fun_coeff_zero, pow_zero, pow_zero, pow_one, one_mul]

include hp
@[simp] lemma ghost_component_verschiebung (x : 𝕎 R) (n : ℕ) :
  ghost_component (n + 1) (verschiebung_fun x) = p * ghost_component n x :=
begin
  simp only [ghost_component, aeval_witt_polynomial],
  rw [finset.sum_range_succ', verschiebung_fun_coeff, if_pos rfl, zero_pow (nat.pow_pos hp.pos _),
      mul_zero, add_zero, finset.mul_sum, finset.sum_congr rfl],
  rintro i -,
  simp only [pow_succ, mul_assoc, verschiebung_fun_coeff, if_neg (nat.succ_ne_zero i),
    nat.succ_sub_succ, nat.sub_zero]
end

@[simp] lemma verschiebung_coeff_zero (x : 𝕎 R) :
  (verschiebung x).coeff 0 = 0 := rfl

-- simp_nf complains if this is simp
lemma verschiebung_coeff_add_one (x : 𝕎 R) (n : ℕ) :
  (verschiebung x).coeff (n + 1) = x.coeff n := rfl

@[simp] lemma verschiebung_coeff_succ (x : 𝕎 R) (n : ℕ) :
  (verschiebung x).coeff n.succ = x.coeff n := rfl

end witt_vector

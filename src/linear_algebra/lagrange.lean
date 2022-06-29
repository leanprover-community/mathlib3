/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/

import algebra.big_operators.basic
import ring_theory.polynomial.basic
import logic.lemmas
import linear_algebra.vandermonde

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `v : ι ↪ F` is an embedding to the field from a fintype `ι`.
Conceptually, this is a set of distinct nodes around which we interpolate.
* `lagrange.basis_divisor x y`, with `x y : F`. These are the normalised irreducible factors of
the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
are distinct.
* `lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
and `0` at `v j` for `i ≠ j`.
* `lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
associated with the _nodes_`x i`.
* `lagrange.interpolate_at v f`, where `v : ι ↪ F` and `ι` is a fintype, and `f : F → F` is a
function from the field to itself: this is the Lagrange interpolant that evaluates to `f (x i)`
at `x i`, and so approximates the function `f`. This is just a special case of the general
interpolation, where the values are given by a known function `f`.
-/

/-
These theorems are independent of the theory of Lagrange interpolants, though they are highly
related to them. They are the theorems that guarantee that a polynomial of bounded degree, when
specified on sufficient points, is completely determined.
-/
section non_lagrange
open_locale polynomial
open polynomial

variables {F : Type*} [field F] {ι : Type*} [fintype ι] {v : ι ↪ F} {i j : ι}

theorem eq_zero_of_eval_eq_zero {F : Type*} [field F] {ι : Type*} [fintype ι] (v : ι ↪ F) {f : F[X]}
  (degree_f_lt : f.degree < fintype.card ι) (eval_f : ∀ i, f.eval (v i) = 0) : f = 0 :=
begin
  rw ← mem_degree_lt at degree_f_lt,
  exact vandermonde_invert  (function.embedding.trans (fintype.equiv_fin ι).symm.to_embedding v)
                            degree_f_lt (λ _, eval_f _)
end

theorem eq_of_eval_eq (v : ι ↪ F) {f g : F[X]} (degree_fg_lt : (f - g).degree < fintype.card ι)
  (eval_fg : ∀ i, f.eval (v i) = g.eval (v i)) : f = g :=
begin
  rw ← mem_degree_lt at degree_fg_lt,
  exact vandermonde_eq  (function.embedding.trans (fintype.equiv_fin ι).symm.to_embedding v)
                        degree_fg_lt (λ _, eval_fg _)
end

theorem eq_of_eval_eq' (v : ι ↪ F) {f g : F[X]}
  (degree_f_lt : f.degree < fintype.card ι) (degree_g_lt : g.degree < fintype.card ι)
  (eval_fg : ∀ i, f.eval (v i) = g.eval (v i)) : f = g :=
begin
  rw ← mem_degree_lt at degree_f_lt degree_g_lt,
  exact vandermonde_eq' (function.embedding.trans (fintype.equiv_fin ι).symm.to_embedding v)
                        degree_f_lt degree_g_lt (λ _, eval_fg _)
end

end non_lagrange

noncomputable theory
open_locale big_operators polynomial

namespace lagrange
open finset
variables {F : Type*} [field F]

open polynomial

section node
variables {ι : Type*} {v : ι ↪ F} {x y : F} {i j : ι}
/-- The basis divisor is defined in terms of an embedded `v : ι ↪ F` from a fintype `ι`.
`basis_divisor i j` is the unique polynomial with `degree ≤ 1` such that when evaluated at `v i`
it gives `1` and `v j` it gives `0` (where when `i = j` it is identically `0`).

Conceptually, they are therefore the building blocks for the Lagrange interpolants. -/
def basis_divisor (x y : F) : F[X] := C (x - y)⁻¹ * (X - C (y))

lemma basis_divisor_self_zero : basis_divisor x x = 0 :=
by simp only [basis_divisor, sub_self, inv_zero, map_zero, zero_mul]

lemma basis_divisor_injective (hxy : basis_divisor x y = 0) : x = y :=
begin
  simp_rw [ basis_divisor, mul_eq_zero, X_sub_C_ne_zero, or_false,
            C_eq_zero, inv_eq_zero, sub_eq_zero] at hxy, exact hxy
end

@[simp] lemma basis_divisor_zero_iff : basis_divisor x y = 0 ↔ x = y :=
⟨basis_divisor_injective, λ H, H ▸ basis_divisor_self_zero⟩

lemma basis_divisor_degree_ne (hxy : x ≠ y) : (basis_divisor x y).degree = 1 :=
begin
  rw [basis_divisor, degree_mul, degree_X_sub_C, degree_C, zero_add],
  exact inv_ne_zero (sub_ne_zero_of_ne hxy)
end

@[simp] lemma basis_divisor_degree_eq : (basis_divisor x x).degree = ⊥ :=
by rw [basis_divisor_self_zero, degree_zero]

lemma basis_divisor_nat_degree_eq : (basis_divisor x x).nat_degree = 0 :=
by { rw [basis_divisor_self_zero, nat_degree_zero] }

lemma basis_divisor_nat_degree_ne (hxy : x ≠ y) : (basis_divisor x y).nat_degree = 1 :=
nat_degree_eq_of_degree_eq_some (basis_divisor_degree_ne hxy)

@[simp] lemma eval_basis_divisor_right : eval y (basis_divisor x y) = 0 :=
by simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

lemma eval_basis_divisor_left_ne (hxy : x ≠ y) : eval x (basis_divisor x y) = 1 :=
begin
  simp only [basis_divisor, eval_mul, eval_C, eval_sub, eval_X],
  exact inv_mul_cancel (sub_ne_zero_of_ne hxy)
end

end node

section basis
variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i j : ι}

/-- Lagrange basis polynomials indexed by `ι` defined for an embedding `v : ι ↪ F`.
`basis v i` evaluates to 1 at `v i` and 0 at `v j` for `i ≠ j`. -/
def basis (v : ι ↪ F) (i : ι) : F[X] := ∏ j in univ.erase i, basis_divisor (v i) (v j)

theorem basis_eq_of_subsingleton [subsingleton ι] : basis v i = 1 :=
begin
  refine prod_eq_one (λ j hj, false.elim _),
  rwa [mem_erase, ne.def, eq_iff_true_of_subsingleton, not_true, false_and] at hj
end

@[simp] theorem basis_eq_of_unique [unique ι] : basis v i = 1 := basis_eq_of_subsingleton

@[simp] theorem basis_eq_of_is_empty [is_empty ι] : basis v i = 1 := basis_eq_of_subsingleton

@[simp] lemma basis_ne_zero : basis v i ≠ 0 :=
begin
  rw basis, intro H, rw prod_eq_zero_iff at H,
  rcases H with ⟨j, hij₁, hij₂⟩,
  rw mem_erase at hij₁, rw basis_divisor_zero_iff at hij₂,
  exact hij₁.1.symm (v.inj' hij₂)
end

theorem eval_basis_self : (basis v i).eval (v i) = 1 :=
begin
  rw [basis, eval_prod], refine prod_eq_one (λ j hj, _), rw mem_erase at hj,
  exact eval_basis_divisor_left_ne (v.inj'.ne hj.1.symm)
end

theorem eval_basis_ne (hij : i ≠ j) : (basis v i).eval (v j) = 0 :=
begin
  simp_rw [basis, eval_prod, prod_eq_zero_iff],
  use j, exact ⟨by finish, eval_basis_divisor_right⟩
end

theorem eval_basis : (basis v i).eval (v j) = if i = j then 1 else 0 :=
by { split_ifs with H, { subst H, exact eval_basis_self}, { exact eval_basis_ne H } }

@[simp] theorem nat_degree_basis : (basis v i).nat_degree = (fintype.card ι) - 1 :=
begin
  have H : ∀ j, j ∈ univ.erase i → basis_divisor (v i) (v j) ≠ 0,
  by { simp [mem_erase, basis_divisor_zero_iff], rintros _ h rfl, exact h rfl },
  rw [  basis, nat_degree_prod _ _ H, ← card_univ,
        ← card_erase_of_mem (mem_univ i), card_eq_sum_ones ],
  refine sum_congr rfl (λ j hj, basis_divisor_nat_degree_ne _), rw mem_erase at hj,
  exact (v.inj'.ne hj.1.symm)
end

theorem degree_basis : (basis v i).degree = ↑(fintype.card ι - 1) :=
by rw [degree_eq_nat_degree basis_ne_zero, nat_degree_basis]

end basis

section interpolate

variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i : ι} {r s : ι → F}

/-- Lagrange interpolation: given a fintype `ι`, an embedding `v : ι ↪ F`,
and a function `r : ι → F`, `interpolate x r` is the unique polynomial of degree `< fintype.card ι`
that takes value `r (v i)` on `v i` for all `i` in `ι`. -/
def interpolate (v : ι ↪ F) (r : ι → F) : F[X] := ∑ i, C (r i) * basis v i

@[simp] theorem interpolate_empty [is_empty ι] : interpolate v r = 0 :=
by rw [interpolate, univ_eq_empty, sum_empty]

theorem interpolate_singleton [unique ι] : interpolate v r = C (r default) :=
by rw [interpolate, univ_unique, sum_singleton, basis_eq_of_unique, mul_one]

theorem eval_interpolate : ∀ i, eval (v i) (interpolate v r) = r i :=
λ i, by simp_rw [ interpolate, eval_finset_sum, eval_mul, eval_C,
                  eval_basis, mul_boole, sum_ite_eq', mem_univ, if_true]

theorem degree_interpolate_le : (interpolate v r).degree ≤ ↑(fintype.card ι - 1) :=
begin
  refine (degree_sum_le _ _).trans _,
  rw finset.sup_le_iff, intros i _,
  rw [degree_mul, degree_basis],
  by_cases hr : (r i = 0),
  { simp only [hr, map_zero, degree_zero, with_bot.bot_add], exact bot_le },
  { rw [degree_C hr, zero_add, with_bot.coe_le_coe] }
end

theorem degree_interpolate_lt :
 (interpolate v r).degree < fintype.card ι :=
begin
 cases is_empty_or_nonempty ι with h h,
 { rw [@interpolate_empty _ _ _ _ _ _ _ h, degree_zero],
  rw ← fintype.card_eq_zero_iff at h, rw h,
  exact with_bot.bot_lt_coe _ },
 { refine lt_of_le_of_lt degree_interpolate_le _, rw with_bot.coe_lt_coe,
  exact nat.sub_lt (zero_lt_iff.mpr (@fintype.card_ne_zero _ _ h)) (zero_lt_one) }
end

theorem eq_interpolate {f : F[X]} (degree_f_lt : f.degree < fintype.card ι) :
  f = interpolate v (λ i, f.eval (v i)) :=
eq_of_eval_eq' v degree_f_lt degree_interpolate_lt (λ _, by simp_rw eval_interpolate)

theorem eq_interpolate_of_eval_eq {f : F[X]} (degree_f_lt : f.degree < fintype.card ι)
(eval_f : ∀ i, f.eval (v i) = r i) : f = interpolate v r :=
by { convert eq_interpolate degree_f_lt, simp_rw eval_f }

/--
This is the characteristic property of the interpolation: the interpolation is the
unique polynomial of `degree < fintype.card ι` which takes the value of the `r i` on the `v i`.
-/
theorem eq_interpolate_iff {f : F[X]} :
  (f.degree < fintype.card ι ∧ ∀ i, eval (v i) f = r i) ↔ f = interpolate v r :=
begin
  split; intro h,
  exact eq_interpolate_of_eval_eq h.1 h.2,
  rw h, exact ⟨degree_interpolate_lt, eval_interpolate⟩
end

/-- Linear version of `interpolate`. -/
def linterpolate (v : ι ↪ F) : (ι → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate v,
  map_add' := λ f g, by { simp_rw [ interpolate, ← finset.sum_add_distrib,
                                    ← add_mul, ← C_add], refl },
  map_smul' := λ c f, by { simp_rw [interpolate, finset.smul_sum, C_mul', smul_smul], refl } }

lemma interpolate_add (r s) : interpolate v (r + s) = interpolate v r + interpolate v s :=
(linterpolate v).map_add r s

@[simp] lemma interpolate_zero : interpolate v 0 = 0 :=
(linterpolate v).map_zero

@[simp] lemma interpolate_neg (r) : interpolate v (-r) = -interpolate v r :=
(linterpolate v).map_neg r

@[simp] lemma interpolate_sub (r s) : interpolate v (r - s) = interpolate v r - interpolate v s :=
(linterpolate v).map_sub r s

@[simp] lemma interpolate_smul (c : F) (r) : interpolate v (c • r) = c • interpolate v r :=
(linterpolate v).map_smul c r

/-- Lagrange interpolation induces isomorphism between functions from `ι`
and polynomials of degree less than `fintype.card ι`.-/
def fun_equiv_degree_lt : degree_lt F (fintype.card ι) ≃ₗ[F] (ι → F) :=
{ to_fun := λ f i, f.1.eval (v i),
  map_add' := λ f g, funext $ λ v, eval_add,
  map_smul' := λ c f, funext $ by simp,
  inv_fun := λ r, ⟨interpolate v r, mem_degree_lt.mpr degree_interpolate_lt⟩,
  left_inv := λ f, subtype.eq (eq_interpolate (mem_degree_lt.1 f.2)).symm,
  right_inv := λ f, funext eval_interpolate }

end interpolate

section nodal
variables {ι : Type*} [fintype ι] {v : ι ↪ F} {i : ι} (r : ι → F)

/--
We define `nodal`, the unique monic polynomial whose roots are the nodes defined by `v`.

We can use `nodal` for an alternative form of `interpolate`.
-/
def nodal (v : ι ↪ F) : F[X] := ∏ i, (X - C (v i))

lemma nodal_eq_remove [decidable_eq ι] (i : ι) :
  nodal v = (X - C (v i)) * ∏ j in univ.erase i, (X - C (v j)) :=
by rw [nodal, mul_prod_erase _ _ (mem_univ i)]

lemma nodal_derive_eval_node_eq [decidable_eq ι] (i : ι) : eval (v i) (nodal v).derivative =
  ∏ j in (univ.erase i), (v i - v j) :=
begin
  rw [nodal_eq_remove i, bernoulli_rule_left],
  { simp_rw [ eval_prod, derivative_sub, derivative_X, derivative_C,
              sub_zero, eval_one, one_mul, eval_sub, eval_X, eval_C]},
  { rw [eval_sub, eval_X, eval_C, sub_self] }
end

lemma nodal_div_eq (i : ι) [decidable_eq ι] :
  nodal v / (X - C (v i)) = ∏ j in univ.erase i, (X - C (v j)) :=
by { rw [nodal_eq_remove i, euclidean_domain.mul_div_cancel_left], exact X_sub_C_ne_zero _ }

lemma basis_eq_nodal_div_eval_deriv_mul_linear [decidable_eq ι] :
  basis v i = C (eval (v i) (nodal v).derivative)⁻¹ * (nodal v / (X - C (v i)))  :=
by {  simp_rw [ basis, basis_divisor, nodal_div_eq, nodal_derive_eval_node_eq,
                prod_mul_distrib, ← prod_inv_distrib, map_prod] }

lemma interpolate_eq_derivative_interpolate [decidable_eq ι] :
∑ i, C (r i * (eval (v i) (nodal v).derivative)⁻¹) * (nodal v / (X - C (v i))) = interpolate v r :=
by simp_rw [interpolate, basis_eq_nodal_div_eval_deriv_mul_linear, map_mul, mul_assoc]

end nodal

section interpolate_at
variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i j : ι} {f g : F → F}

/-- Lagrange interpolation: given a fintype `ι`, an embedding `v : ι ↪ F`,
and a function `f : F → F`, `interpolate_at v r` is the unique polynomial of
degree `< fintype.card ι` that takes value `f (v i)` on `v i` for all `i` in `ι`. -/
def interpolate_at (v : ι ↪ F) (f : F → F) := interpolate v (λ i, f (v i))

theorem interpolate_at_eq_of_eval_eq (hs : ∀ i, f (v i) = g (v i)) :
  interpolate_at v f = interpolate_at v g :=
by {simp_rw [interpolate_at], congr, exact funext hs}

@[simp] theorem interpolate_at_empty [is_empty ι] : interpolate_at v f = 0 :=
by rw [interpolate_at, interpolate_empty]

theorem interpolate_at_singleton [unique ι] : interpolate_at v f = C (f (v default)) :=
by rw [interpolate_at, interpolate_singleton]

@[simp] theorem eval_interpolate_at : eval (v i) (interpolate_at v f) = f (v i) :=
by rw [interpolate_at, eval_interpolate]

theorem degree_interpolate_at_le : (interpolate_at v f).degree ≤ ↑(fintype.card ι - 1) :=
by {rw [interpolate_at], exact degree_interpolate_le}

theorem degree_interpolate_at_lt : (interpolate_at v f).degree < fintype.card ι :=
by {rw [interpolate_at], exact degree_interpolate_lt}

/-- Linear version of `interpolate_at`. -/
def linterpolate_at (v : ι ↪ F) : (F → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate_at v,
  map_add' := λ f g, by { simp_rw [interpolate_at, ← interpolate_add], refl },
  map_smul' := λ c f, by { { simp_rw [interpolate_at, ← interpolate_smul], refl } } }

@[simp] lemma interpolate_at_add (f g) :
  interpolate_at v (f + g) = interpolate_at v f + interpolate_at v g :=
(linterpolate_at v).map_add f g

@[simp] lemma interpolate_at_zero : interpolate_at v 0 = 0 := (linterpolate_at v).map_zero

@[simp] lemma interpolate_at_neg (f) : interpolate_at v (-f) = -interpolate_at v f :=
(linterpolate_at v).map_neg f

@[simp] lemma interpolate_at_sub (f g) :
  interpolate_at v (f - g) = interpolate_at v f - interpolate_at v g :=
(linterpolate_at v).map_sub f g

@[simp] lemma interpolate_at_smul (c : F) (f) : interpolate_at v (c • f) = c • interpolate_at v f :=
(linterpolate_at v).map_smul c f

theorem eq_interpolate_at (g : F[X]) (degree_g_lt : g.degree < fintype.card ι) :
  g = interpolate_at v (λ x, eval x g) := eq_interpolate degree_g_lt

theorem eq_interpolate_at_of_eval_eq {g : F[X]} (degree_g_lt : g.degree < fintype.card ι)
  (eval_gf : ∀ i, g.eval (v i) = f (v i)) : g = interpolate_at v f :=
eq_interpolate_of_eval_eq degree_g_lt eval_gf

/--
This is the characteristic property of the interpolation of a function at given nodes:
the interpolation at the nodes is the unique polynomial of `degree < fintype.card ι`
which agrees with `f` on the `v i`.
-/
theorem eq_interpolate_at_iff (g : F[X]) : (g.degree < fintype.card ι ∧
  ∀ i, g.eval (v i) = f (v i)) ↔ g = interpolate_at v f := eq_interpolate_iff

end interpolate_at

end lagrange

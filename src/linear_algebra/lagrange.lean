/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Wrenna Robson
-/

import algebra.big_operators.basic
import ring_theory.polynomial.basic
import logic.lemmas
import linear_algebra.vandermonde

-- These theorems are, strictly speaking, not directly about the API defined in this file.
-- So really they "should" go somewhere else. Where that should be is an open question.

section non_lagrange
open_locale polynomial
open polynomial

variables {F : Type*} [field F] {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i j : ι}
theorem eq_zero_of_eval_eq_zero (v : ι ↪ F) {f : F[X]} (hf1 : f.degree < fintype.card ι)
 (hf2 : ∀ i, f.eval (v i) = 0) : f = 0 :=
begin
 rw ← mem_degree_lt at hf1,
 exact vandermonde_invertibility ( function.embedding.trans
                  (fintype.equiv_fin ι).symm.to_embedding v) hf1 (λ _, hf2 _)
end

theorem eq_of_eval_eq (v : ι ↪ F) {f g : F[X]} (hfg1 : (f - g).degree < fintype.card ι)
 (hfg2 : ∀ i, f.eval (v i) = g.eval (v i)) : f = g :=
begin
 rw ← mem_degree_lt at hfg1,
 exact vandermonde_agreement ( function.embedding.trans
                (fintype.equiv_fin ι).symm.to_embedding v) hfg1 (λ _, hfg2 _)
end

theorem eq_of_eval_eq' (v : ι ↪ F) {f g : F[X]}
 (hf : f.degree < fintype.card ι) (hg : g.degree < fintype.card ι)
 (hfg : ∀ i, f.eval (v i) = g.eval (v i)) : f = g :=
begin
 rw ← mem_degree_lt at hf hg,
 exact vandermonde_agreement' ( function.embedding.trans
                 (fintype.equiv_fin ι).symm.to_embedding v) hf hg (λ _, hfg _)
end
end non_lagrange

/-!
# Lagrange interpolation

## Main definitions

* `lagrange.basis s v` where `s : finset F` and `v : F`: the Lagrange basis polynomial
 that evaluates to `1` at `v` and `0` at other elements of `s`.
* `lagrange.interpolate v f` where `s : finset F` and `f : F → F`: the Lagrange interpolant
 that evaluates to `f v` at `v` for `v ∈ s`.
-/

noncomputable theory
open_locale big_operators polynomial

namespace lagrange
open finset
variables {F : Type*} [field F]

open polynomial

section node
variables {ι : Type*} [decidable_eq ι] {v : ι ↪ F} {i j : ι}
/-- TODO FIX DOCSTRING -/
def node_linear (v : ι ↪ F) : ι → ι → F[X] := λ i j, C (v i - v j)⁻¹ * (X - C (v j))

lemma node_linear_def : node_linear v i j = C (v i - v j)⁻¹ * (X - C (v j)) := rfl

lemma node_linear_self_zero : node_linear v i i = 0 :=
by simp only [node_linear_def, sub_self, inv_zero, map_zero, zero_mul]

lemma node_linear_injective (hij : node_linear v i j = 0) : i = j :=
begin
 simp_rw [ node_linear_def, mul_eq_zero, X_sub_C_ne_zero, or_false,
      C_eq_zero, inv_eq_zero, sub_eq_zero] at hij,
 exact v.inj' hij
end

lemma node_linear_zero_iff : node_linear v i j = 0 ↔ i = j :=
⟨node_linear_injective, λ H, H ▸ node_linear_self_zero⟩

lemma node_linear_degree_ne (hij : i ≠ j) : (node_linear v i j).degree = 1 :=
begin
 rw [node_linear_def, degree_mul, degree_X_sub_C, degree_C, zero_add],
 exact inv_ne_zero (sub_ne_zero_of_ne (v.inj'.ne hij))
end

lemma node_linear_degree_eq : (node_linear v i i).degree = ⊥ :=
by rw [node_linear_self_zero, degree_zero]

lemma node_linear_degree : (node_linear v i j).degree = ite (i = j) ⊥ 1 :=
by {split_ifs with H,  { subst H, exact node_linear_degree_eq },
            { exact node_linear_degree_ne H }}

lemma node_linear_nat_degree : (node_linear v i j).nat_degree = ite (i = j) 0 1 :=
by { rw [nat_degree, node_linear_degree], split_ifs; refl }

lemma eval_node_linear_right : eval (v j) (node_linear v i j) = 0 :=
by simp only [node_linear_def, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero]

lemma eval_node_linear_left (hij : i ≠ j) :
 eval (v i) (node_linear v i j) = 1 :=
begin
 simp only [node_linear_def, eval_mul, eval_C, eval_sub, eval_X],
 exact inv_mul_cancel (sub_ne_zero_of_ne (v.inj'.ne hij))
end

lemma eval_node_linear :
 eval (v i) (node_linear v i j) = ite (i = j) 0 1 :=
by {split_ifs with H,  { subst H, exact eval_node_linear_right },
            { exact eval_node_linear_left H }}
end node

section basis
variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i j : ι}

/-- TODO FIX DOCSTRING -/
def basis (v : ι ↪ F) : ι → F[X] := λ i, ∏ j, ite (i = j) 1 (node_linear v i j)

lemma basis_def : basis v i = ∏ j, ite (i = j) 1 (node_linear v i j) := rfl

theorem basis_eq_of_subsingleton [subsingleton ι] : basis v i = 1 :=
by simp_rw [basis_def, eq_iff_true_of_subsingleton, if_true, prod_const_one]

theorem basis_eq_of_unique [unique ι] : basis v i = 1 := basis_eq_of_subsingleton

theorem basis_eq_of_is_empty [is_empty ι] : basis v i = 1 := basis_eq_of_subsingleton

lemma basis_ne_zero : basis v i ≠ 0 :=
begin
 rw basis_def, intro H, rw prod_eq_zero_iff at H,
 rcases H with ⟨j, _, hij⟩,
 by_cases h : i = j,
 { rw if_pos h at hij, exact one_ne_zero hij },
 { rw [if_neg h, node_linear_zero_iff] at hij, exact h hij }
end

lemma basis_eq_prod_filter : basis v i = ∏ j in univ.filter (ne i), (node_linear v i j)
:= by rw [basis_def, prod_ite, prod_const_one, one_mul]

theorem eval_basis_self : (basis v i).eval (v i) = 1 :=
by {simp_rw [basis_eq_prod_filter, eval_prod, eval_node_linear], finish}

theorem eval_basis_ne (hij : i ≠ j) : (basis v i).eval (v j) = 0 :=
begin
 simp_rw [basis_eq_prod_filter, eval_prod, prod_eq_zero_iff],
 use j, exact ⟨by finish, eval_node_linear_right⟩,
end

theorem eval_basis : (basis v i).eval (v j) = if i = j then 1 else 0 :=
by { split_ifs with H, { subst H, exact eval_basis_self}, { exact eval_basis_ne H } }

theorem nat_degree_basis : (basis v i).nat_degree = (fintype.card ι) - 1 :=
begin
 suffices h : (basis v i).nat_degree = (univ.filter (ne i)).card,
 { rw [h, card_eq_sum_ones],
  simp only [ filter_ne, sum_const, card_erase_of_mem,
        mem_univ, algebra.id.smul_eq_mul, mul_one, fintype.card]
 },
 rw [ basis_eq_prod_filter, nat_degree_prod,
    sum_filter, card_eq_sum_ones, sum_filter, sum_congr rfl],
 { simp only [ node_linear_nat_degree, mem_univ, ite_not, ite_eq_right_iff,
        forall_true_left, forall_eq', eq_self_iff_true, if_true],
 },
 { intros _ hij hvij, simp only [mem_filter, mem_univ, ne.def, true_and] at hij,
  exact hij (node_linear_injective hvij),
 }
end

theorem degree_basis : (basis v i).degree = ↑(fintype.card ι - 1) :=
by rw [degree_eq_nat_degree basis_ne_zero, nat_degree_basis]

end basis

section interpolate

variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i : ι} {r s : ι → F}
/-- TODO NEW DOCSTRING-/
def interpolate (v : ι ↪ F) (r : ι → F) : F[X] := ∑ i, C (r i) * basis v i

lemma interpolate_def : interpolate v r = ∑ i, C (r i) * basis v i := rfl

theorem interpolate_empty [is_empty ι] : interpolate v r = 0 :=
by rw [interpolate_def, univ_eq_empty, sum_empty]

theorem interpolate_singleton [unique ι] : interpolate v r = C (r default) :=
by rw [interpolate_def, univ_unique, sum_singleton, basis_eq_of_unique, mul_one]

theorem eval_interpolate : eval (v i) (interpolate v r) = r i :=
by simp_rw [ interpolate_def, eval_finset_sum, eval_mul, eval_C,
       eval_basis, mul_boole, sum_ite_eq', mem_univ, if_true]

theorem degree_interpolate_le
 : (interpolate v r).degree ≤ ↑(fintype.card ι - 1) :=
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

theorem interpolate_eq_of_eval_eq (hs : ∀ i, r i = s i) :
 interpolate v r = interpolate v s := by {rw ← @function.funext_iff _ _ r s at hs, rw hs}

def linterpolate (v : ι ↪ F) : (ι → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate v,
 map_add' := λ f g, by { simp_rw [interpolate_def, ← finset.sum_add_distrib, ← add_mul, ← C_add],
  refl },
 map_smul' := λ c f, by { simp_rw [interpolate_def, finset.smul_sum, C_mul', smul_smul], refl } }

lemma interpolate_add (r s) :
 interpolate v (r + s) = interpolate v r + interpolate v s := (linterpolate v).map_add r s

lemma interpolate_zero : interpolate v 0 = 0 :=
(linterpolate v).map_zero

lemma interpolate_neg (r) : interpolate v (-r) = -interpolate v r :=
(linterpolate v).map_neg r

lemma interpolate_sub (r s) :
 interpolate v (r - s) = interpolate v r - interpolate v s := (linterpolate v).map_sub r s

lemma interpolate_smul (c : F) (r) :
 interpolate v (c • r) = c • interpolate v r := (linterpolate v).map_smul c r

theorem eq_interpolate (f : F[X]) (hf : f.degree < fintype.card ι) :
 interpolate v (λ i, eval (v i) f) = f :=
eq_of_eval_eq' v degree_interpolate_lt hf (λ _, by simp_rw eval_interpolate)

/-- TODO NEW DOCSTRING -/
def fun_equiv_degree_lt : degree_lt F (fintype.card ι) ≃ₗ[F] (ι → F) :=
{ to_fun := λ f i, f.1.eval (v i),
 map_add' := λ f g, funext $ λ v, eval_add,
 map_smul' := λ c f, funext $ by simp,
 inv_fun := λ r, ⟨interpolate v r, mem_degree_lt.mpr degree_interpolate_lt⟩,
 left_inv := λ f, subtype.eq (eq_interpolate _ (mem_degree_lt.1 f.2)),
 right_inv := λ f, funext (λ i, eval_interpolate) }

end interpolate

section interpolate_at
variables {ι : Type*} [fintype ι] [decidable_eq ι] {v : ι ↪ F} {i j : ι} {f g : F → F}

def interpolate_at (v : ι ↪ F) (f : F → F) := interpolate v (λ i, f (v i))

lemma interpolate_at_def : interpolate_at v f = interpolate v (λ i, f (v i)) := rfl

theorem interpolate_at_eq_of_eval_eq (hs : ∀ i, f (v i) = g (v i)) :
 interpolate_at v f = interpolate_at v g :=
by {simp_rw [interpolate_at_def], congr, exact funext hs}

theorem interpolate_at_empty [is_empty ι] : interpolate_at v f = 0 :=
by rw [interpolate_at_def, interpolate_empty]

theorem interpolate_at_singleton [unique ι] : interpolate_at v f = C (f (v default)) :=
by rw [interpolate_at_def, interpolate_singleton]

theorem eval_interpolate_at : eval (v i) (interpolate_at v f) = f (v i) :=
by rw [interpolate_at_def, eval_interpolate]

theorem degree_interpolate_at_le : (interpolate_at v f).degree ≤ ↑(fintype.card ι - 1)
:= by {rw [interpolate_at_def], exact degree_interpolate_le}

theorem degree_interpolate_at_lt : (interpolate_at v f).degree < fintype.card ι
:= by {rw [interpolate_at_def], exact degree_interpolate_lt}

/-- Linear version of `interpolate`. -/
def linterpolate_at (v : ι ↪ F) : (F → F) →ₗ[F] polynomial F :=
{ to_fun := interpolate_at v,
 map_add' := λ f g, by { simp_rw [interpolate_at_def, ← interpolate_add], refl },
 map_smul' := λ c f, by { { simp_rw [interpolate_at_def, ← interpolate_smul], refl } } }

lemma interpolate_at_add (f g) :
  interpolate_at v (f + g) = interpolate_at v f + interpolate_at v g :=
(linterpolate_at v).map_add f g

lemma interpolate_at_zero : interpolate_at v 0 = 0 :=
(linterpolate_at v).map_zero

lemma interpolate_at_neg (f) : interpolate_at v (-f) = -interpolate_at v f :=
(linterpolate_at v).map_neg f

lemma interpolate_at_sub (f g) :
interpolate_at v (f - g) = interpolate_at v f - interpolate_at v g :=
(linterpolate_at v).map_sub f g

lemma interpolate_at_smul (c : F) (f) : interpolate_at v (c • f) = c • interpolate_at v f :=
(linterpolate_at v).map_smul c f

theorem eq_interpolate_at_of_eval_eq {g : F[X]} (hg : g.degree < fintype.card ι)
 (hgf : ∀ i, g.eval (v i) = f (v i)) : interpolate_at v f = g :=
eq_of_eval_eq' v degree_interpolate_at_lt hg (λ _, by simp_rw [eval_interpolate_at, hgf])

theorem eq_interpolate_at (f : F[X]) (hf : f.degree < fintype.card ι) :
 interpolate_at v (λ x, eval x f) = f := eq_interpolate f hf

end interpolate_at

section interpolate_erase
-- These are a challenge to translate into this new language.

/-
theorem lagrange.degree_interpolate_erase (f : F → F) {x : F} (hx : x ∈ s) :
(lagrange.interpolate (s.erase x) f).degree < ↑(s.card - 1)

theorem interpolate_eq_interpolate_erase_add {v y : F} (hv : v ∈ s) (hy : y ∈ s) (hvy : v ≠ y) :
 interpolate v f =
 C (y - v)⁻¹ * ((X - C v) * interpolate (s.erase v) f + (C y - X) * interpolate (s.erase y) f) :=
begin
 refine eq_interpolate_of_eval_eq _ _ _ (λ z hz, _),
 { rw [degree_mul, degree_C (inv_ne_zero (sub_ne_zero.2 hvy.symm)), zero_add],
  refine lt_of_le_of_lt (degree_add_le _ _) (mav_lt _ _),
  { rw [degree_mul, degree_X_sub_C],
   convert (with_bot.add_lt_add_iff_left with_bot.coe_ne_bot).2
    (degree_interpolate_erase s f hv),
   simp [nat.one_add, nat.sub_one, nat.succ_pred_eq_of_pos (finset.card_pos.2 ⟨v, hv⟩)] },
  { rw [degree_mul, ←neg_sub, degree_neg, degree_X_sub_C],
   convert (with_bot.add_lt_add_iff_left with_bot.coe_ne_bot).2
    (degree_interpolate_erase s f hy),
   simp [nat.one_add, nat.sub_one, nat.succ_pred_eq_of_pos (finset.card_pos.2 ⟨y, hy⟩)] } },
 { by_cases hzv : z = v,
  { simp [hzv, eval_interpolate (s.erase y) f v (finset.mem_erase_of_ne_of_mem hvy hv),
      inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hvy.symm)] },
  { by_cases hzy : z = y,
   { simp [hzy, eval_interpolate (s.erase v) f y (finset.mem_erase_of_ne_of_mem hvy.symm hy),
       inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hvy.symm)] },
   { simp only [eval_interpolate (s.erase v) f z (finset.mem_erase_of_ne_of_mem hzv hz),
          eval_interpolate (s.erase y) f z (finset.mem_erase_of_ne_of_mem hzy hz),
          inv_mul_eq_iff_eq_mul₀ (sub_ne_zero_of_ne hvy.symm), eval_mul, eval_C, eval_add,
          eval_sub, eval_X],
    ring } } }
end
-/
end interpolate_erase

end lagrange

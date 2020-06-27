/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import data.polynomial_cayley_hamilton
import linear_algebra.nonsingular_inverse

noncomputable theory

universes u v w

open polynomial matrix
open_locale big_operators

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]

noncomputable def baz : matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R) :=
(((matrix_equiv_tensor R (polynomial R) n)).trans (algebra.tensor_product.comm R _ _)).trans (polynomial_equiv_tensor R (matrix n n R)).symm

-- maybe we don't need this?
lemma matrix_eq {X : Type*} [add_comm_monoid X] (m : matrix n n X) :
  m = ∑ (x : n × n), (λ i j, if (i, j) = x then m i j else 0) := sorry

@[elab_as_eliminator] protected lemma matrix.induction_on {X : Type*} [add_comm_monoid X] {M : matrix n n X → Prop} (m : matrix n n X)
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_elementary : ∀ i j x, M (λ i' j', if i' = i ∧ j' = j then x else 0)) :
  M m := sorry

lemma baz_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
  baz (λ i' j', if i' = i ∧ j' = j then monomial k x else 0) =
    monomial k (λ i' j', if i' = i ∧ j' = j then x else 0) :=
begin
  dsimp only [baz, alg_equiv.trans_apply],
  simp only [matrix_equiv_tensor_apply_elementary],
  apply (polynomial_equiv_tensor R (matrix n n R)).injective,
  simp only [alg_equiv.apply_symm_apply],
  convert algebra.tensor_product.comm_tmul _ _ _ _ _,
  simp only [polynomial_equiv_tensor_apply],
  convert eval₂_monomial _ _,
  { simp only [algebra.tensor_product.tmul_mul_tmul, one_pow, one_mul, matrix.mul_one, algebra.tensor_product.tmul_pow,
     algebra.tensor_product.include_left_apply, mul_eq_mul],
    -- almost there: just use `R` bilinearity
    sorry, },
  { -- wah, missing instance...
    sorry },
end

lemma baz_coeff_apply_aux_2 (i j : n) (p : polynomial R) (k : ℕ) :
  coeff (baz (λ i' j', if i' = i ∧ j' = j then p else 0)) k =
    (λ i' j', if i' = i ∧ j' = j then coeff p k else 0) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq,
    sorry, },
  { intros k x,
    rw baz_coeff_apply_aux_1,
    simp [coeff_single],
    split_ifs; { funext, simp, }, }
end

@[simp] lemma baz_coeff_apply (m : matrix n n (polynomial R)) (k : ℕ) (i j : n) :
  coeff (baz m) k i j = coeff (m i j) k :=
begin
  apply matrix.induction_on m,
  { intros p q hp hq, simp [hp, hq], },
  { intros i' j' x,
    rw baz_coeff_apply_aux_2,
    dsimp,
    split_ifs; simp },
end

def characteristic_matrix (m : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (λ i j, monomial 0 (m i j))

lemma r (p : polynomial R) :
  baz (p • 1) = p.map (algebra_map R (matrix n n R)) :=
begin
  ext m i j,
  simp [coeff_map, matrix.one_val],
  simp [algebra_map_matrix_val],
  split_ifs; simp,
end

lemma q (m : matrix n n R) :
  baz (characteristic_matrix m) = X - monomial 0 m := sorry

def characteristic_polynomial (m : matrix n n R) : polynomial R :=
(characteristic_matrix m).det

theorem cayley_hamilton (m : matrix n n R) :
  (characteristic_polynomial m).eval₂ (algebra_map R (matrix n n R)) m = 0 :=
begin
  have := calc
    (characteristic_polynomial m) • (1 : matrix n n (polynomial R))
         = (characteristic_matrix m).det • (1 : matrix n n (polynomial R)) : rfl
     ... = adjugate (characteristic_matrix m) * (characteristic_matrix m)  : (adjugate_mul _).symm,
  apply_fun baz at this,
  change _ = baz (_ * _) at this,
  simp only [baz.map_mul] at this,
  rw q at this,
  apply_fun (λ p, p.eval₂ (ring_hom.id _) m) at this,
  rw eval₂_mul_X_sub_monomial' at this,
  rw r at this,
  rw eval₂_eq_eval_map at this ⊢,
  simp at this,
  exact this,
end

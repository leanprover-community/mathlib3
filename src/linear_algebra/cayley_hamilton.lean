import ring_theory.matrix_algebra
import ring_theory.polynomial_algebra
import data.polynomial_cayley_hamilton
import linear_algebra.nonsingular_inverse

noncomputable theory

universes u v w

open polynomial matrix

variables {R : Type u} [comm_ring R]
variables {n : Type w} [fintype n] [decidable_eq n]

noncomputable def baz : matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R) :=
(((matrix_equiv_tensor R (polynomial R) n)).trans (algebra.tensor_product.comm R _ _)).trans (polynomial_equiv_tensor R (matrix n n R)).symm

def characteristic_matrix (m : matrix n n R) : matrix n n (polynomial R) :=
matrix.scalar n (X : polynomial R) - (λ i j, monomial 0 (m i j))

lemma q (m : matrix n n R) :
  baz (characteristic_matrix m) = X - monomial 0 m := sorry

-- lemma r (p : polynomial R) :
--   baz (p • 1) = p.map (algebra_map R (matrix n n R))

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
  apply_fun (λ p, p.eval₂ id m) at this,
  rw eval₂_mul_X_sub_monomial' at this,
end

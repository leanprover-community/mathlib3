import data.polynomial
import analysis.calculus.deriv
import tactic

theorem polynomial.aeval_nat_cast'
  {R A : Type*} [comm_semiring R] [nontrivially_normed_field A] [algebra R A]
  (f : polynomial R) (k : ℕ) :
  polynomial.aeval (k:A) f = algebra_map _ _ (polynomial.eval (k : R) f) :=
begin
  rw [polynomial.aeval_def, polynomial.eval₂_eq_eval_map, polynomial.eval_nat_cast_map],
end

theorem polynomial.eval₂_deriv
  {R S : Type*} [semiring R] [nontrivially_normed_field S] (f : R →+* S) (p : polynomial R) :
  (deriv (λ x : S, (p.eval₂ f x))) = (λ x, polynomial.eval₂ f x p.derivative) :=
begin
  ext y,
  simp_rw [polynomial.eval₂_eq_eval_map, polynomial.deriv, polynomial.derivative_map],
end

theorem polynomial.aeval_deriv
  {R A : Type*} [comm_semiring R] [nontrivially_normed_field A] [algebra R A]
  (f : polynomial R) (a : A) :
  (deriv (λ x : A, polynomial.aeval x f)) a = polynomial.aeval a (f.derivative) :=
begin
  simp_rw [polynomial.aeval_def, polynomial.eval₂_deriv],
end

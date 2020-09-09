import data.polynomial.funext
import data.mv_polynomial.variables
import data.mv_polynomial.rename
import data.mv_polynomial.equiv
import ring_theory.polynomial.basic

namespace mv_polynomial

variables {σ : Type*} {R : Type*} [integral_domain R] [infinite R]
variables {S : Type*} [integral_domain S]

instance : infinite (mv_polynomial σ R) := sorry


lemma funext_zero {p : mv_polynomial (fin 0) R} (h : ∀ x, eval x p = 0) : p = 0 :=
sorry

lemma funext_one {n} {p : mv_polynomial (fin n) R} (h : ∀ x, eval x p = 0) : p = 0 :=
begin
  induction n with n ih,
  { apply funext_zero h },
  { apply (fin_succ_equiv _ _).injective,
    apply polynomial.funext,
    intro r,
    rw [ring_equiv.map_zero, polynomial.eval_zero],
    apply ih,
    intro x, }
end


end mv_polynomial

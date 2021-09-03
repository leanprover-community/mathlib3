import algebra.tropical.polynomial

variables (R : Type*)

section quotient

variables [semiring R]

instance polynomial.eval_setoid : setoid (polynomial R) :=
{ r := λ p q, ∀ (x : R), polynomial.eval x p = polynomial.eval x q,
  iseqv :=  ⟨λ p x, rfl, λ p q h x, (h x).symm, λ p q r hpq hqr x, (hpq x).trans (hqr x)⟩ }

def polynomial.eval_quotient : Type* := quotient (polynomial.eval_setoid R)

variable {R}

lemma polynomial.coeff_ne_zero_of_eq_nat_degree_of_ne_zero {p : polynomial R} {n : ℕ}
  (hn : p.nat_degree = n) (hp : p ≠ 0) :
  p.coeff n ≠ 0 :=
polynomial.coeff_ne_zero_of_eq_degree $ (polynomial.degree_eq_iff_nat_degree_eq hp).mpr hn

lemma polynomial.coeff_ne_zero_of_eq_ne_zero_nat_degree {p : polynomial R} {n : ℕ}
  (hn : p.nat_degree = n) (hn' : n ≠ 0) :
  p.coeff n ≠ 0 :=
begin
  refine polynomial.coeff_ne_zero_of_eq_nat_degree_of_ne_zero hn _,
  contrapose! hn',
  rw [←hn, hn', polynomial.nat_degree_zero]
end

end quotient

variables {R}

namespace tropical

local notation `tR` := tropical (with_top R)

variables [linear_ordered_ring R]

open polynomial

def polynomical.tropical_root_via (p : polynomial tR) (r : tR) : Prop :=
∃ (q : polynomial tR), ∀ (x : tR), eval x p = eval x (C (x + r) * q)

example (p : polynomial tR) (hp : nat_degree p = 2)
  (hc : p.coeff 1 / p.coeff 2 ≤ p.coeff 0 / p.coeff 1) :
  p = C (p.coeff 2) * (X + C (p.coeff 1 / p.coeff 2)) * (X + C (p.coeff 0 / p.coeff 1)) :=
calc
  p   = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :
    sorry
  ... = C (p.coeff 2) * (X ^ 2 + C (p.coeff 1 / p.coeff 2) * X + C (p.coeff 0 / p.coeff 2)) :
    by { rw [mul_add, mul_add, ←C_mul, mul_div_cancel', ←mul_assoc, ←C_mul, mul_div_cancel'];
      exact coeff_ne_zero_of_eq_ne_zero_nat_degree hp two_ne_zero }
  ... = C (p.coeff 2) * (X + C (p.coeff 1 / p.coeff 2)) * (X + C (p.coeff 0 / p.coeff 1)) :
    _

end tropical

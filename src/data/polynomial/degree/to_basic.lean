import tactic
import data.polynomial.degree.basic
import data.polynomial.degree.trailing_degree

open polynomial finsupp finset

variables {R : Type*} [semiring R] {f : polynomial R}

--Put this next to degree_monomial, and maybe use that lemma for a shorter proof?
@[simp] lemma nat_degree_monomial {a : R} (n : ℕ) (ha : a ≠ 0) : nat_degree (C a * X ^ n) = n :=
nat_degree_eq_of_degree_eq_some (degree_monomial n ha)

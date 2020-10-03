import tactic
import data.polynomial.degree.basic
import data.polynomial.degree.to_basic
import data.polynomial.degree.trailing_degree

open polynomial finsupp finset

namespace polynomial
variables {R : Type*} [semiring R] {f : polynomial R}

@[simp] lemma trailing_coeff_eq_zero : trailing_coeff f = 0 ↔ f = 0 :=
⟨λ h, by_contradiction $ λ hp, mt mem_support_iff.1
  (not_not.2 h) (mem_of_min (trailing_degree_eq_nat_trailing_degree hp)),
λ h, h.symm ▸ leading_coeff_zero⟩

lemma trailing_coeff_nonzero_of_nonzero : f ≠ 0 ↔ trailing_coeff f ≠ 0 :=
not_congr trailing_coeff_eq_zero.symm

lemma nat_trailing_degree_mem_support_of_nonzero : f ≠ 0 → nat_trailing_degree f ∈ f.support :=
begin
  intro,
  exact mem_support_iff_coeff_ne_zero.mpr (trailing_coeff_nonzero_of_nonzero.mp a),
end

lemma nat_trailing_degree_le_of_mem_supp (a : ℕ) :
  a ∈ f.support → nat_trailing_degree f ≤ a:=
begin
  rw mem_support_iff_coeff_ne_zero,
  exact nat_trailing_degree_le_of_ne_zero,
end

lemma nat_degree_eq_support_max'_trailing (h : f ≠ 0) :
  nat_trailing_degree f = f.support.min' (nonempty_support_iff.mpr h) :=
begin
  apply le_antisymm,
  { apply le_min',
    intros y hy,
    exact nat_trailing_degree_le_of_mem_supp y hy },
  { apply finset.min'_le,
    rw mem_support_iff_coeff_ne_zero,
    exact trailing_coeff_nonzero_of_nonzero.mp h, },
end


lemma xxQ (N O f g : ℚ) :
 N + O - (g + f) = O - g + (N - f) :=
begin
  ring,
end

end polynomial

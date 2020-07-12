import data.polynomial

noncomputable theory

universes u w

open polynomial
open_locale big_operators

variables {R : Type u} [comm_semiring R]
variables {α : Type w} [decidable_eq α]

open finset

section poly_big_ops

namespace polynomial

variables (s : finset α) (f : α → polynomial R)

lemma nat_degree_prod_le : (s.prod f).nat_degree ≤ ∑ i in s, (f i).nat_degree :=
begin
  apply s.induction_on, simp,intros a s anins ih,
  rw [prod_insert anins, sum_insert anins],
  transitivity (f a).nat_degree + (∏ (x : α) in s, (f x)).nat_degree,
  apply polynomial.nat_degree_mul_le, apply add_le_add_left ih,
end

lemma leading_coeff_prod' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (∏ i in s, f i).leading_coeff = ∏ i in s, (f i).leading_coeff :=
begin
  revert h, apply s.induction_on, simp, intros a s anins ih,
  repeat {rw prod_insert anins},
  intro nz, rw polynomial.leading_coeff_mul'; rwa ih, repeat {apply right_ne_zero_of_mul nz},
end

lemma nat_degree_prod_eq' (h : ∏ i in s, (f i).leading_coeff ≠ 0) :
  (s.prod f).nat_degree = ∑ i in s, (f i).nat_degree :=
begin
  revert h, apply s.induction_on, simp, intros a s anins ih,
  rw [prod_insert anins, prod_insert anins, sum_insert anins],
  intro nz, rw polynomial.nat_degree_mul_eq', rw ih, apply right_ne_zero_of_mul nz,
  rwa polynomial.leading_coeff_prod', apply right_ne_zero_of_mul nz,
end

lemma monic_prod_monic :
  (∀ a : α, a ∈ s → monic (f a)) → monic (s.prod f) :=
by { apply prod_induction, apply monic_mul, apply monic_one }

end polynomial

end poly_big_ops

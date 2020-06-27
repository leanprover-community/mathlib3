import data.polynomial

open polynomial
open finset
open_locale big_operators

-- TODO everything here should move up to cayley_hamilton.lean or down to polynomial.lean/...


variables {R S : Type*}

section ring
variables [ring R]

variables [ring S]
variables (f : R → S) (x : S)
variables [is_ring_hom f]

lemma foo {p : polynomial R} {r : R} {a : ℕ} :
  coeff (p * (X - monomial 0 r)) (a + 1) = coeff p a - coeff p (a + 1) * r :=
sorry

@[simp] lemma quux {p : polynomial R} : p.coeff (p.nat_degree + 1) = 0 := sorry

lemma sum_over_range' (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0)
  (n : ℕ) (w : p.nat_degree < n) :
  p.sum f = ∑ (a : ℕ) in range n, f a (coeff p a) :=
begin
  sorry,
end

lemma sum_over_range (p : polynomial R) {f : ℕ → R → S} (h : ∀ n, f n 0 = 0) :
  p.sum f = ∑ (a : ℕ) in range (p.nat_degree + 1), f a (coeff p a) :=
sum_over_range' p h (p.nat_degree + 1) (lt_add_one _)

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
sorry

@[simp] lemma coeff_monomial (n : ℕ) (r : R) : coeff (monomial n r) n = r := sorry

lemma eval₂_mul_X_sub_monomial {p : polynomial R} {r : R} :
  (p * (X - monomial 0 r)).eval₂ f (f r) = 0 :=
begin
  simp [eval₂],
  rw sum_over_range' _ _ (p.nat_degree + 2) sorry,
  swap,
  { simp [is_ring_hom.map_zero f], },
  rw sum_range_succ',
  conv_lhs {
    congr,
    apply_congr,
    skip,
    rw [foo],
    rw [is_ring_hom.map_sub f],
    rw [is_ring_hom.map_mul f],
    rw [sub_mul],
    rw [mul_assoc, ←pow_succ],
  },
  conv_lhs {
    congr,
    skip,
    simp [coeff_sub],
    rw [is_ring_hom.map_neg f],
    rw [is_ring_hom.map_mul f],
  },
  rw sum_range_sub',
  simp [is_ring_hom.map_zero f],
end

lemma eval₂_mul_X_sub_monomial' {p : polynomial R} (r : R) :
  (p * (X - monomial 0 r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

lemma eval₂_mul_X_sub_C {p : polynomial R} (r : R) :
  (p * (X - C r)).eval₂ (ring_hom.id _) r = 0 :=
eval₂_mul_X_sub_monomial id

end ring

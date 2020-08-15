import data.polynomial
import algebra.ordered_field
import field_theory.algebraic_closure

variables (k : Type*)

class is_euclidean [field k] : Prop :=
(add_squares_ne_neg_one : ∀ x y : k, x * x + y * y ≠ -1)
(eq_square_or_neg_square : ∀ x : k, (∃ y, x = y * y) ∨ (∃ y, x = - (y * y)))

namespace is_euclidean

section ordered

variables [linear_ordered_field k] [is_euclidean k]

#check sub_le_sub_left

theorem le_iff (x y : k) : x ≤ y ↔ ∃ z, x + z * z = y :=
begin
  split; intro h,
  { cases eq_square_or_neg_square (y - x), {cases h_1 with z hz, use z, rw ← hz, abel},
    use 0, rw [mul_zero, add_zero], symmetry, apply le_antisymm _ h,
    cases h_1 with a ha, apply le_of_sub_nonpos, simp [ha, mul_self_nonneg], },
  { rcases h with ⟨z, rfl⟩, simp [mul_self_nonneg], }
end

end ordered


variables [field k] [is_euclidean k]

instance : has_le k := ⟨λ x y, ∃ z, y - x = z * z⟩

variable {k}

lemma ge_of_sub_eq_neg_square {x y : k} (h : ∃ z, y - x = - (z * z)) : y ≤ x :=
by { cases h with z h, rw [← neg_sub, neg_inj] at h, exact ⟨z, h⟩, }

lemma eq_zero_of_sum_three_squares_eq_zero (x y z : k) (h : x * x + y * y + z * z = 0) :
  x = 0 :=
begin
  have h1 := add_squares_ne_neg_one (y / x) (z / x), contrapose h1, field_simp,
  rw [div_eq_iff, ← add_sub_cancel (y * y + z * z) (x * x)], rw [add_assoc, add_comm] at h,
  simp [h],
  intro c, rw mul_eq_zero at c, cases c; apply h1 c,
end

variable (k)

instance : linear_order k :=
{ le_refl := λ x, by { use 0, rw [mul_zero, sub_self], },
  le_total := λ x y, by { unfold has_le.le, cases is_euclidean.eq_square_or_neg_square (y - x),
    { left, apply h, },
    { right, apply ge_of_sub_eq_neg_square h, } },
  le_trans := λ x y z hxy hyz, by {
    cases is_euclidean.eq_square_or_neg_square (z - x) with h h, { exact h },
    { cases h with d hd, by_cases d = 0, {use 0, rw h at hd, simp [hd], },
      exfalso, rcases hxy with ⟨e, he⟩, rcases hyz with ⟨f, hf⟩,
      apply h, apply eq_zero_of_sum_three_squares_eq_zero d e f,
      rw [← he, ← hf, ← neg_inj], simp only [←hd, neg_sub, neg_add_rev, neg_zero], abel, }
  },
  le_antisymm := λ x y hxy hyx, by {
    rcases hxy with ⟨a, ha⟩, rcases hyx with ⟨b, hb⟩, apply eq_of_sub_eq_zero,
    rw [hb, mul_eq_zero], left,
    apply eq_zero_of_sum_three_squares_eq_zero b a 0,
    rw [← ha, ← hb, mul_zero], abel, },
  .. (is_euclidean.has_le k) }

instance : linear_ordered_field k :=
{ add_le_add_left := λ a b h c, by { cases h with d h, use d, rw ← h, abel, },
  mul_pos := λ a b ha hb, by { apply lt_of_le_of_ne, cases ha.1 with c hc, cases hb.1 with d hd,
    rw sub_zero at *, rw [hc, hd], use c * d, rw sub_zero, symmetry,
    rw [mul_assoc, mul_comm d], simp [mul_assoc],
    symmetry, apply mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm, },
  zero_lt_one := by { show (0 : k) < 1, use 1, simp,
    intro con, cases con with x hx, apply add_squares_ne_neg_one x 0, simp [← hx], },
 .. (is_euclidean.linear_order k), .. (infer_instance : field k) }

end is_euclidean

variable [field k]

open polynomial

class is_real_closed extends is_euclidean k :=
(exists_root_of_odd_degree:
  ∀ (p : polynomial k), ¬ 2 ∣ p.nat_degree → ∃ (x : k), p.eval x = 0)

namespace is_real_closed

section basic

variables {k} [is_real_closed k]

instance irreducible_x_squared_add_one : irreducible ( X * X + 1 : polynomial k) := sorry

theorem adjoin_i_is_alg_closed : is_alg_closed (adjoin_root (X * X + 1 : polynomial k)) := sorry

theorem degree_alg_closure_eq_two {K : Type*} [field K] [algebra k K] (ac : is_alg_closure k K) :
  vector_space.dim k K = 2 := sorry

theorem linear_or_quadratic_of_monic_irreducible
  {p : polynomial k} (hmon : p.monic) (hirr : irreducible p) :
  (∃ (a : k), p = X - C a) ∨ (∃ (a b : k), p = (X - C a) ^ 2 + C b ∧ 0 < b) := sorry

theorem intermediate_value_property (p : polynomial k) (a b : k) :
  set.Icc (p.eval a) (p.eval b) ⊆ (λ x, p.eval x) '' set.Icc a b := sorry

end basic

variables {k} {K : Type*} [field K] [algebra k K] (ac : is_alg_closure k K)

theorem artin_schreier (hfin : finite_dimensional k K) : is_real_closed k := sorry


end is_real_closed

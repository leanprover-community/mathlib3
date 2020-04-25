
import number_theory.quadratic_reciprocity
import data.padics.hensel

example : legendre_sym 43 29 = -1 :=
begin
  haveI : fact (nat.prime 29) := by norm_num,
  haveI : fact (nat.prime  7) := by norm_num,
  haveI : fact (29 % 2 = 1)   := by norm_num,
  haveI : fact ( 7 % 2 = 1)   := by norm_num,
  calc legendre_sym 43 29 = legendre_sym 14 29 :
                            by { rw [legendre_sym_mod, show 43 % 29 = 14, by norm_num] }
                      ... = legendre_sym (2 * 7) 29 :
                            by { rw [show 14 = 2 * 7, by norm_num] }
                      ... = legendre_sym 2 29 * legendre_sym 7 29 :
                            by { rw [legendre_sym_mul] }
                      ... = -legendre_sym 7 29 :
                            by { rw [legendre_sym_two, show (-1:ℤ)^(29/4 + 29/2) = -1, by norm_num],
                                 rw [neg_one_mul] }
                      ... = -legendre_sym 29 7 :
                            by { rw [legendre_sym_swap 7 29 dec_trivial],
                                 rw [show (-1:ℤ) ^ (7 / 2 * (29 / 2)) = 1, by norm_num, mul_one] }
                      ... = -legendre_sym 1 7 :
                            by { rw [legendre_sym_mod, show 29 % 7 = 1, by norm_num] }
                      ... = -1 :
                            by { rw [legendre_sym_one] }
end
.

variables (p : ℕ) [nat.prime p]

open polynomial

lemma foo (hp : p ≠ 2) (n : ℕ) (h : legendre_sym n p = 1) : ∃ (x : ℤ_[p]), x^2 = n :=
begin
  letI _hp : fact p.prime := ‹p.prime›,
  by_cases hn : (n : zmod p) = 0,
  { rw ← legendre_sym_eq_zero_iff at hn,
    rw hn at h,
    exact absurd h zero_ne_one },
  rw [legendre_sym_eq_one_iff p hn] at h,
  rcases h with ⟨x, hx⟩,
  rcases zmod.nat_cast_surjective x with ⟨k, rfl⟩,
  let f : polynomial ℤ_[p] := X^2 - C n,
  rcases @hensels_lemma p _ f k _ with ⟨x, hx, H⟩,
  { refine ⟨x, _⟩,
    simpa only [sub_eq_zero, eval_C, eval_X, eval_pow, eval_sub] using hx, },
  simp only [f],
  simp only [eval_C, eval_X, eval_pow, eval_sub],
  simp only [pow_two, sub_eq_add_neg],
  simp only [eval_X, add_assoc, derivative_X, mul_one, derivative_add, derivative_mul, one_mul, eval_add],
  sorry
end

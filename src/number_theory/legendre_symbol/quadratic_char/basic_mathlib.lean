import data.fintype.parity
import number_theory.legendre_symbol.quadratic_char.basic

open fintype (card)
open finset

variables {F : Type*} [fintype F] [field F]

lemma symmetric_is_square (hF : card F % 4 ≠ 3) :
  symmetric (λ x y : F, is_square (x - y)) :=
λ _ _ h, by simpa using h.mul (finite_field.is_square_neg_one_iff.2 hF)

lemma card_non_zero_square_non_square [decidable_eq F] (hF : ring_char F ≠ 2) :
  (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)).card = card F / 2 ∧
  (univ.filter (λ x : F, ¬ is_square x)).card = card F / 2 :=
begin
  have : (univ.filter (λ x : F, ¬ is_square x)) = (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)),
  { refine filter_congr _,
    simp [not_imp_not] {contextual := tt} },
  rw this,
  have cf := quadratic_char_sum_zero hF,
  simp only [quadratic_char_apply, quadratic_char_fun] at cf,
  rw [sum_ite, sum_const_zero, zero_add, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    mul_neg, mul_one, mul_one, add_neg_eq_zero, nat.cast_inj, filter_filter, filter_filter] at cf,
  rw [←cf, and_self],
  have : (univ.filter (λ x : F, x ≠ 0 ∧ is_square x)) ∪
    (univ.filter (λ x : F, x ≠ 0 ∧ ¬ is_square x)) ∪ {0} = univ,
  { simp only [←filter_or, ←and_or_distrib_left, em, and_true, filter_ne'],
    rw [union_comm, ←insert_eq, insert_erase],
    exact mem_univ _ },
  have h' := congr_arg finset.card this,
  rw [card_disjoint_union, card_disjoint_union, card_singleton, card_univ, ←cf, ←two_mul,
    ←bit0_eq_two_mul, ←bit1] at h',
  { rw [←h', nat.bit1_div_two] },
  { rw finset.disjoint_left,
    simp {contextual := tt} },
  { simp },
end

lemma card_square (F : Type*) [fintype F] [field F] [decidable_eq F] (hF : ring_char F ≠ 2) :
  ((univ : finset F).filter is_square).card = card F / 2 + 1 :=
begin
  rw [←(card_non_zero_square_non_square hF).1],
  simp only [and_comm, ←filter_filter, filter_ne'],
  rw card_erase_add_one,
  simp
end

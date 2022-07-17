/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/

import data.polynomial.of_list
import ring_theory.polynomial.basic

/-!

# Equivalence between lists and polynomials below a degree

Constructing polynomials of less than a certain degree by providing an explicit list of
coefficients.

## Main definitions

- `of_list_lt_of_le`: a `list R` defines a `polynomial R` of degree at least the length of the list
- `equiv_list_degree_lt`: lists that do not terminate with a `0` below a certain length are
  isomorphic to polynomials below such a degree.

## Main theorems

- `surjective_of_list_lt_of_le`: for every `polynomial R` of a certain degree or less, there
  is a list of length at most that degree that can construct the polynomial by coefficient.

-/

variables {R : Type*} [semiring R] (l : list R) [decidable_pred (λ (i : ℕ), list.nthd 0 l i ≠ 0)]

namespace polynomial

/-- A `l : list R` over a `semiring R` defines a polynomial of degree less than its length,
with the elements as coefficients. A specialization of `polynomial.of_list`. -/
def of_list_lt : degree_lt R l.length :=
⟨of_list l, by simpa [mem_degree_lt] using degree_of_list_lt l⟩

@[simp] lemma coe_of_list_lt : (of_list_lt l : polynomial R) = of_list l := rfl

/-- A `l : list R` over a `semiring R` defines a polynomial of degree less than `n : ℕ` where
`l.length ≤ n` with the elements as coefficients. A specialization of `polynomial.of_list`. -/
def of_list_lt_of_le {n : ℕ} (hn : l.length ≤ n): degree_lt R n :=
subtype.imp_embedding _ _ (degree_lt_mono hn) (of_list_lt l)

@[simp] lemma coe_of_list_lt_of_le {n : ℕ} (hn : l.length ≤ n) :
  (of_list_lt_of_le l hn : polynomial R) = of_list l := rfl

variables [decidable_pred (λ (x : R), x = 0)]

lemma surjective_of_list_lt_of_le {n : ℕ} (p : degree_lt R n) :
  ∃ (l : list R) (hl : l.length = n), p = of_list_lt_of_le l hl.le :=
begin
  cases p with p hp,
  -- separate out p = 0 case because `surjective_of_list 0` can give either `[]`, which we need,
  -- or `[0]`, from `to_list`, which would not work.
  rcases eq_or_ne p 0 with rfl|hp',
  { refine ⟨list.repeat 0 n, list.length_repeat _ _, _⟩,
    ext,
    simp },
  obtain ⟨l, rfl, hl'⟩ := surjective_of_list p,
  refine ⟨l ++ list.repeat 0 (n - l.length), _, _⟩,
  { have : l.length ≤ n,
    { simp only [mem_degree_lt, degree_eq_nat_degree hp', with_bot.coe_lt_coe, hl'] at hp,
      exact nat.le_of_pred_lt hp },
    simp [this] },
  { have : ∀ (n : ℕ), of_list (list.repeat (0 : R) n) = 0,
    { intro,
      simp [of_list_eq_zero_iff, list.mem_repeat] },
    ext,
    simp [coeff_X_pow_mul', this] }
end

/-- Lists `list R` of length less than or equal to `n : ℕ` that do not terminate in a `0` are
in direct correspondence to `polynomial R` of degree less than `n`. -/
def equiv_list_degree_lt (n : ℕ) :
  {l : list R // l.length ≤ n ∧ (l = [] ∨ l.nthd 0 (l.length - 1) ≠ 0)} ≃ degree_lt R n :=
{ to_fun := λ l, of_list_lt_of_le l l.prop.left,
  inv_fun := λ p, begin
    refine ⟨(to_list (p : polynomial R)).rdrop_while (= 0), _, _⟩,
    { have hp := p.prop,
      simp only [mem_degree_lt] at hp,
      rcases eq_or_ne p 0 with rfl|hp',
      { simp [list.rdrop_while_singleton] },
      replace hp' : (p : polynomial R) ≠ 0 := λ H, hp' (submodule.coe_eq_zero.mp H),
      rw [←nat_degree_lt_iff_degree_lt hp', nat.lt_iff_add_one_le, ←length_to_list] at hp,
      exact (list.length_le_of_sublist (list.rdrop_while_prefix _ _).sublist).trans hp },
    { cases eq_or_ne (p : polynomial R) 0 with hp' hp',
      { rw submodule.coe_eq_zero at hp',
        simp [hp'] },
      simp only [list.rdrop_while_eq_nil_iff],
      right,
      rw [list.nthd_eq_nth_le, ←list.last_eq_nth_le],
      refine list.rdrop_while_last_not (= (0 : R)) (to_list (p : polynomial R)) _,
      simp only [ne.def, list.rdrop_while_eq_nil_iff, not_forall, exists_prop],
      refine ⟨(p : polynomial R).leading_coeff, _, _⟩,
      { rw ←last_to_list,
        exact list.last_mem _ },
      { simp [hp'] } }
  end,
  left_inv := begin
    rintro ⟨l, hl, hl'⟩,
    simp only [subtype.coe_mk, coe_of_list_lt_of_le],
    by_cases hn : l = [],
    { simp [hn] },
    simp only [hn, false_or] at hl',
    rw [to_list_of_list l hl', list.rdrop_while_eq_self_iff],
    intro,
    rwa [list.last_eq_nth_le, ←list.nthd_eq_nth_le _ (0 : R)]
  end,
  right_inv := begin
    rintro ⟨p, hp⟩,
    rw [subtype.ext_iff],
    rcases eq_or_ne p 0 with rfl|hp',
    { simp [list.rdrop_while_singleton] },
    simp only [subtype.coe_mk, coe_of_list_lt_of_le],
    rw [list.rdrop_while_eq_self_iff.mpr, of_list_to_list p],
    simp [hp']
  end }

@[simp] lemma coe_equiv_list_degree_lt_apply (n : ℕ)
  (l : {l : list R // l.length ≤ n ∧ (l = [] ∨ l.nthd 0 (l.length - 1) ≠ 0)}) :
  (equiv_list_degree_lt n l : polynomial R) = of_list l := rfl

lemma coe_equiv_list_degree_lt_symm_apply {n : ℕ}
  (p : degree_lt R n) :
  ((equiv_list_degree_lt n).symm p : list R) = (to_list (p : polynomial R)).rdrop_while (= 0) := rfl

@[simp] lemma equiv_list_degree_lt_symm_apply_zero (n : ℕ) :
  (equiv_list_degree_lt n).symm (0 : degree_lt R n) = ⟨[], nat.zero_le _, or.inl rfl⟩ :=
by simp [subtype.ext_iff, coe_equiv_list_degree_lt_symm_apply]

lemma equiv_list_degree_lt_symm_apply_ne_zero {n : ℕ} {p : degree_lt R n} (hp : p ≠ 0) :
  ((equiv_list_degree_lt n).symm p : list R) = to_list p :=
by simp [coe_equiv_list_degree_lt_symm_apply, hp]

end polynomial

/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import tactic

import data.nat.choose.multinomial
import data.fin.tuple.nat_antidiagonal


/-! # Multinomial theorem

`finset.sum_pow` is the *multinomial theorem* that expresses a power of a
finite sum in a commutative semiring as a finite sum involving multinomial
 coefficients:
(f 0 + f 1 + ...  + f (m-1))^n
    = ∑_(c ∈ list.nat.antidiagonal_tuple m n)
     (multinomial c id) *  ∏ (f i) ^ (c i)
It generalizes the binomial formula which is `add_pow`.

A small section on `tuples` which are members of `fin m → ℕ` and proves results
which are used to simplify the proof and could be elsewhere.


## TODO :
* Extend to the noncommutative case, as `commute.add_pow`
* The indices of the sums are `fin m`. This may be painful but is due
to thedefinition of `nat.antidiagonal_tuple` which is defined as
`finset : (fin m → ℕ)`.  Some lemmas would apply once `nat_antidiagonal` is
rewritten in a greater generality.
* The proofs are in need of being golfed.

-/

section tuples

variables {ι : Type*} [decidable_eq ι]

/-- Add an element to a tuple -/
def tuple.add : (ι → ℕ) → ι → (ι → ℕ) :=
λ f a, function.update f a (f a + 1)

/-- Subtract an element from a tuple -/
def tuple.sub : (ι → ℕ) → ι → (ι → ℕ) :=
λ f a, function.update f a (f a - 1)

/- Addition then subtraction of the same element gives the original tuple -/
lemma tuple.sub_add_cancel {f : ι → ℕ} {a : ι} :
  tuple.sub (tuple.add f a) a = f :=
begin
  dsimp only [tuple.add, tuple.sub],
  ext x,
  by_cases hx : x = a,
  { rw hx, simp only [function.update_same], apply nat.add_sub_cancel, },
  { simp only [function.update_noteq hx], },
end

/-- Subtraction then addition of the same element gives the original tuple
if that element was there -/
lemma tuple.add_sub_cancel {f : ι → ℕ} {a : ι} (ha : f a ≠ 0) :
  tuple.add (tuple.sub f a) a = f :=
begin
  rw ← nat.one_le_iff_ne_zero at ha,
  dsimp only [tuple.add, tuple.sub],
  ext x,
  by_cases hx : x = a,
  { rw hx, simp only [function.update_same], exact nat.sub_add_cancel ha, },
  { simp only [function.update_noteq hx], },
end

/-- Adding an element to a tuple gives an element the next antidiagonal -/
lemma tuple.add_sum {m n : ℕ} {c : fin m → ℕ} {a : fin m} :
  c ∈ finset.nat.antidiagonal_tuple m n ↔
  tuple.add c a ∈ finset.nat.antidiagonal_tuple m n.succ :=
begin
  simp only [finset.nat.mem_antidiagonal_tuple, tuple.add],
  rw finset.sum_update_of_mem (finset.mem_univ a),
  rw add_comm _ 1, rw add_assoc,
  rw ← finset.sum_update_of_mem (finset.mem_univ a),
  simp only [function.update_eq_self, nat.succ_eq_one_add, add_right_inj],
end

end tuples

section multinomial_theorem

lemma multinomial_induction {m n : ℕ} (c ∈ finset.nat.antidiagonal_tuple m n.succ) :
(finset.filter (λ (x : (fin m → ℕ) × fin m), tuple.add x.fst x.snd = c)
     (finset.nat.antidiagonal_tuple m n ×ˢ finset.univ)).sum
    (λ (x : (fin m → ℕ) × fin m), nat.multinomial finset.univ x.fst) =
  nat.multinomial finset.univ c :=
begin
  rw finset.sum_filter,
  rw finset.sum_finset_product_right
    (finset.nat.antidiagonal_tuple m n ×ˢ (finset.univ : finset (fin m)))
    (finset.univ) (λ a, finset.nat.antidiagonal_tuple m n)
    (λ ca, begin rw and.comm, exact finset.mem_product, end),
  simp only,

  let H' := finset.nat.mem_antidiagonal_tuple.mp H,
  suffices H1 : 0 <finset.univ.prod (λ i, (c i).factorial),
  rw ← nat.mul_right_inj H1,
  rw nat.multinomial_spec,
  simp only [H', nat.factorial_succ],
  rw [← nat.succ_eq_add_one, ← H', finset.mul_sum, finset.sum_mul],
  rw finset.sum_congr rfl,
  intros a _,
  rw finset.mul_sum,
  simp_rw mul_ite,
  simp only [mul_zero],
  suffices H2 : ∀ (x ∈ finset.nat.antidiagonal_tuple m n),
    ite (tuple.add x a = c)
      (finset.univ.prod (λ (i : fin m), (c i).factorial)
        * nat.multinomial finset.univ x)
      0
    = (ite (tuple.add x a = c) (c a) 0) * n.factorial,
  rw finset.sum_congr rfl H2,
  rw ← finset.sum_mul,
  apply congr_arg2 _ _ rfl,
  rw ← finset.sum_filter,
  rw finset.sum_const,
  rw smul_eq_mul,  conv_rhs {rw ← one_mul (c a)},
  by_cases hc : c a = 0,
  { simp only [hc, mul_zero], },
  { apply congr_arg2 _ _ rfl,
    simp,
    rw finset.card_eq_one ,
    use tuple.sub c a,
    ext c',
    simp only [finset.mem_filter, finset.mem_singleton],
    split,
    { intro h', rw ← h'.2, rw tuple.sub_add_cancel, },
    { intro h',
      suffices : tuple.add c' a = c,
      apply and.intro _ this,
      rw tuple.add_sum,  rw this,  exact H,
      rw h', rw tuple.add_sub_cancel hc, }, },

  { -- H2
    intros c hc,
    split_ifs,
    { rw ← h,
      simp only [tuple.add, function.update_same,
        ← function.comp_apply nat.factorial, function.comp_update],

      rw finset.prod_update_of_mem (finset.mem_univ a),
      dsimp,
      rw mul_assoc (c a + 1),
      rw ← finset.prod_update_of_mem (finset.mem_univ a),
      simp only [function.update_eq_self],
      rw mul_assoc,
      rw nat.multinomial_spec,
      apply congr_arg2 _ rfl, apply congr_arg,
      exact finset.nat.mem_antidiagonal_tuple.mp hc, },
    rw zero_mul, },

  { -- H1
    apply finset.prod_pos ,
    intros i _,
    apply nat.factorial_pos, },

end



variables {α : Type*} [comm_semiring α]

/-- The multinomial theorem -/
theorem finset.sum_pow {m : ℕ} (f : fin m → α) (n : ℕ) :
  (finset.univ.sum f) ^ n =
  (finset.nat.antidiagonal_tuple m n).sum
    (λ c : fin m → ℕ, (nat.multinomial finset.univ c)
      * finset.univ.prod (λ i, (f i) ^ (c i))) :=
begin
  induction n with n ih,
  { -- case 0
    simp only [finset.nat.antidiagonal_tuple_zero_right, pow_zero,
      finset.sum_singleton, pi.zero_apply, finset.prod_const_one, mul_one],
    simp only [nat.multinomial, pi.zero_apply, finset.sum_const_zero,
      nat.factorial_zero, finset.prod_const_one, nat.div_self,
      nat.lt_one_iff, nat.cast_one], },
  { -- induction case
    by_cases hm : m = 0,
    { have : (finset.univ : finset (fin m)) = ∅,
      rw [finset.univ_eq_empty_iff, hm], exact fin.is_empty,
      rw this,
      simp only [finset.sum_empty, zero_pow', ne.def, nat.succ_ne_zero,
        not_false_iff, nat.multinomial_nil, nat.cast_one, finset.prod_empty,
        mul_one, finset.sum_const, nat.smul_one_eq_coe],
      rw hm,
      simp only [hm, finset.nat.antidiagonal_tuple_zero_succ,
        finset.card_empty, nat.cast_zero], },

    -- m ≠ 0
    rw pow_succ',
    rw ih,
    rw finset.sum_mul, simp_rw finset.mul_sum, rw ← finset.sum_product',

    have hq : ∀ ca ∈  finset.nat.antidiagonal_tuple m n
      ×ˢ (finset.univ : finset (fin m)),
      tuple.add ca.fst ca.snd ∈ finset.nat.antidiagonal_tuple m n.succ
    := λ ca hca, tuple.add_sum.mp (finset.mem_product.mp hca).1,
    rw ← finset.sum_fiberwise_of_maps_to hq,
    rw finset.sum_congr rfl,
    intros c hc,
    simp only [finset.filter_congr_decidable],

    suffices : ∀ a ∈ finset.filter (λ (x : (fin m → ℕ) × (fin m)), tuple.add x.fst x.snd = c) (finset.nat.antidiagonal_tuple m n ×ˢ (finset.univ : finset (fin m))),
       ↑(nat.multinomial (finset.univ) a.fst)
       * finset.univ.prod (λ i, f i ^ (a.fst i)) * f a.snd
       = ↑(nat.multinomial (finset.univ) a.fst)
         * finset.univ.prod (λ i, (f i) ^ (c i)),
    { rw finset.sum_congr rfl this,
    rw ← finset.sum_mul,
    apply congr_arg2 _ _ rfl,
    norm_cast,
    apply congr_arg,
    apply multinomial_induction,
    exact hc, },
    { rintros ⟨x,a⟩ hxa,
      simp only [finset.mem_filter, finset.mem_product,
        finset.nat.mem_antidiagonal_tuple] at hxa,
      rw mul_assoc,
      apply congr_arg2 _ rfl,
      rw ← hxa.2,

      conv_lhs { rw finset.prod_eq_prod_diff_singleton_mul hxa.1.2, },
      conv_rhs { rw finset.prod_eq_prod_diff_singleton_mul hxa.1.2, },
      rw mul_assoc,
      apply congr_arg2,
      { rw finset.prod_congr rfl,
        intros i hi,
        simp only [finset.mem_sdiff,
          finset.mem_range, finset.mem_singleton] at hi,
        apply congr_arg2 _ rfl,
        change x i = function.update x a (x a + 1) i,
        simp only [function.update_apply, if_neg hi.2], },
      { dsimp only,
        rw ← pow_succ',
        apply congr_arg2 _ rfl,
        simp only [tuple.add],
        simp only [function.update_apply, if_pos rfl], }, }, },
end

end multinomial_theorem

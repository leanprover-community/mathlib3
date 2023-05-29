/-
Copyright (c) 2021 Benjamin Davidson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Davidson, Yury Kudryashov
-/
import analysis.calculus.local_extr.rolle
import analysis.calculus.deriv.polynomial
import topology.algebra.polynomial

/-!
# Rolle's Theorem for polynomials

In this file we use Rolle's Theorem to relate the number of roots of a polynomial and its
derivative. Namely, we prove the following facts.

* `polynomial.card_roots_to_finset_le_card_roots_derivative_diff_roots_succ`: the number of roots of
  a real polynomial `p` is at most the number of roots of its derivative that are not roots of `p`
  plus one.

* `polynomial.card_roots_to_finset_le_derivative`, `polynomial.card_root_set_le_derivative`: the
  number of roots of a real polynomial is at most the number of roots of its derivative plus one.

* `polynomial.card_roots_le_derivative`: same, but the roots are counted with multiplicities.

## Keywords

polynomial, Rolle's Theorem, root
-/

namespace polynomial

open_locale big_operators polynomial

/-- The number of roots of a real polynomial `p` is at most the number of roots of its derivative
that are not roots of `p` plus one. -/
lemma card_roots_to_finset_le_card_roots_derivative_diff_roots_succ (p : ℝ[X]) :
  p.roots.to_finset.card ≤ (p.derivative.roots.to_finset \ p.roots.to_finset).card + 1 :=
begin
  cases eq_or_ne p.derivative 0 with hp' hp',
  { rw [eq_C_of_derivative_eq_zero hp', roots_C, multiset.to_finset_zero, finset.card_empty],
    exact zero_le _ },
  have hp : p ≠ 0, from ne_of_apply_ne derivative (by rwa [derivative_zero]),
  refine finset.card_le_diff_of_interleaved (λ x hx y hy hxy hxy', _),
  rw [multiset.mem_to_finset, mem_roots hp] at hx hy,
  obtain ⟨z, hz1, hz2⟩ := exists_deriv_eq_zero hxy p.continuous_on (hx.trans hy.symm),
  refine ⟨z, _, hz1⟩,
  rwa [multiset.mem_to_finset, mem_roots hp', is_root, ← p.deriv]
end

/-- The number of roots of a real polynomial is at most the number of roots of its derivative plus
one. -/
lemma card_roots_to_finset_le_derivative (p : ℝ[X]) :
  p.roots.to_finset.card ≤ p.derivative.roots.to_finset.card + 1 :=
p.card_roots_to_finset_le_card_roots_derivative_diff_roots_succ.trans $
  add_le_add_right (finset.card_mono $ finset.sdiff_subset _ _) _

/-- The number of roots of a real polynomial (counted with multiplicities) is at most the number of
roots of its derivative (counted with multiplicities) plus one. -/
lemma card_roots_le_derivative (p : ℝ[X]) : p.roots.card ≤ p.derivative.roots.card + 1 :=
calc p.roots.card = ∑ x in p.roots.to_finset, p.roots.count x :
  (multiset.to_finset_sum_count_eq _).symm
... = ∑ x in p.roots.to_finset, (p.roots.count x - 1 + 1) :
  eq.symm $ finset.sum_congr rfl $ λ x hx, tsub_add_cancel_of_le $ nat.succ_le_iff.2 $
    multiset.count_pos.2 $ multiset.mem_to_finset.1 hx
... = ∑ x in p.roots.to_finset, (p.root_multiplicity x - 1) + p.roots.to_finset.card :
  by simp only [finset.sum_add_distrib, finset.card_eq_sum_ones, count_roots]
... ≤ ∑ x in p.roots.to_finset, p.derivative.root_multiplicity x +
  ((p.derivative.roots.to_finset \ p.roots.to_finset).card + 1) :
  add_le_add
    (finset.sum_le_sum $ λ x hx, root_multiplicity_sub_one_le_derivative_root_multiplicity _ _)
    p.card_roots_to_finset_le_card_roots_derivative_diff_roots_succ
... ≤ ∑ x in p.roots.to_finset, p.derivative.roots.count x +
  (∑ x in p.derivative.roots.to_finset \ p.roots.to_finset, p.derivative.roots.count x + 1) :
  begin
    simp only [← count_roots],
    refine add_le_add_left (add_le_add_right ((finset.card_eq_sum_ones _).trans_le _) _) _,
    refine finset.sum_le_sum (λ x hx, nat.succ_le_iff.2 $ _),
    rw [multiset.count_pos, ← multiset.mem_to_finset],
    exact (finset.mem_sdiff.1 hx).1
  end
... = p.derivative.roots.card + 1 :
  begin
    rw [← add_assoc, ← finset.sum_union finset.disjoint_sdiff, finset.union_sdiff_self_eq_union,
      ← multiset.to_finset_sum_count_eq, ← finset.sum_subset (finset.subset_union_right _ _)],
    intros x hx₁ hx₂,
    simpa only [multiset.mem_to_finset, multiset.count_eq_zero] using hx₂
  end

/-- The number of real roots of a polynomial is at most the number of roots of its derivative plus
one. -/
lemma card_root_set_le_derivative {F : Type*} [comm_ring F] [algebra F ℝ] (p : F[X]) :
  fintype.card (p.root_set ℝ) ≤ fintype.card (p.derivative.root_set ℝ) + 1 :=
by simpa only [root_set_def, finset.coe_sort_coe, fintype.card_coe, derivative_map]
  using card_roots_to_finset_le_derivative (p.map (algebra_map F ℝ))

end polynomial

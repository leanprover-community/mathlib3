/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashwin Iyengar
-/
import analysis.normed_space.basic

/-!
# Foos and bars

In this file we introduce `nonarchimedean_normed_ring` and `nonarchimedean_normed_comm_ring`.
These are classes which extend `normed_ring` and include an extra ultrametric inequality.

## Main results

- `ultrametric`: this is an extension of the ultrametric inequality to an arbitrary number.
  of variables

-/

class nonarchimedean_normed_ring (R : Type*) extends normed_ring R :=
(ultrametric_inequality : ∀ x y : R, ∥x + y∥ ≤ (max ∥x∥ ∥y∥))

class nonarchimedean_normed_comm_ring (R : Type*) extends nonarchimedean_normed_ring R :=
(mul_comm : ∀ x y : R, x * y = y * x)

variables {R : Type*}

@[priority 100] -- see Note [lower instance priority]
instance nonarchimedean_normed_comm_ring.to_comm_ring
  [β : nonarchimedean_normed_comm_ring R] : comm_ring R := { ..β }

variables [nonarchimedean_normed_ring R]

namespace nonarchimedean_normed_ring

lemma ultrametric {ι : Type*} (S : finset ι) {hS : S.nonempty} (f : ι → R) :
  ∃ x ∈ S, ∥S.sum f∥ ≤ ∥f x∥ ∧ ∀ y ∈ S, ∥f y∥ ≤ ∥f x∥ :=
begin
  haveI : decidable_eq ι := classical.dec_eq _,
  induction S using finset.induction with t S ht i_hyp,
  { simp only [finset.not_mem_empty, exists_false, not_false_iff, exists_prop_of_false],
    exact exists_false hS },
  { rw finset.sum_insert ht,
    have ue := (ultrametric_inequality (f t) (S.sum f)),
    by_cases S.nonempty,
    { obtain ⟨x, hx, x_ineq⟩ := i_hyp,
      by_cases (∥f t∥ ≤ ∥f x∥),
      { use x,
        simp only [hx, true_and, forall_eq_or_imp, or_true, finset.mem_insert],
        exact ⟨le_trans ue (max_le_iff.2 ⟨h, x_ineq.1⟩), h, x_ineq.2⟩ },
      { use t,
        rw not_le at h,
        replace h := le_of_lt h,
        simp only [true_and, forall_eq_or_imp, true_or, eq_self_iff_true, finset.mem_insert],
        exact ⟨le_trans ue (max_le_iff.2 ⟨rfl.ge, le_trans x_ineq.1 h⟩),
        rfl.ge, λ a ha, le_trans (x_ineq.2 a ha) h⟩ },
      assumption },
    { rw finset.not_nonempty_iff_eq_empty at h,
      simp [h] } }
end

end nonarchimedean_normed_ring
